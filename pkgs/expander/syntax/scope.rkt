#lang racket/base
(require ;"../common/set.rkt"
         "../compile/serialize-property.rkt"
         "../compile/serialize-state.rkt"
         "../common/memo.rkt"
         "syntax.rkt"
         "binding-table.rkt"
         "taint.rkt"
         "tamper.rkt"
         "../common/phase.rkt"
         "fallback.rkt"
         "datum-map.rkt"
         "cache.rkt")

(provide new-scope
         new-multi-scope
         add-scope
         add-scopes
         remove-scope
         remove-scopes
         flip-scope
         flip-scopes
         push-scope
         
         syntax-e ; handles lazy scope and taint propagation
         syntax-e/no-taint ; like `syntax-e`, but doesn't explode a dye pack
         
         syntax-scope-list
         syntax-any-scopes?
         syntax-any-macro-scopes?
         
         syntax-shift-phase-level

         syntax-swap-scopes

         add-binding-in-scopes!
         add-bulk-binding-in-scopes!

         resolve

         bound-identifier=?

         top-level-common-scope

         deserialize-scope
         deserialize-scope-fill!
         deserialize-representative-scope
         deserialize-representative-scope-fill!
         deserialize-multi-scope
         deserialize-shifted-multi-scope
         
         generalize-scope
         
         scope?
         scope<?
         shifted-multi-scope?
         shifted-multi-scope<?)

(define (list-member? lst to-find)
  (not (not (member to-find lst))))
(define (list-add lst elem)
  (cons elem lst))

(module+ for-debug
  (provide (struct-out scope)
           (struct-out multi-scope)
           (struct-out representative-scope)
           scope-list-at-fallback))

;; TODO - no longer correct for lists
;; A scope represents a distinct "dimension" of binding. We can attach
;; the bindings for a set of scopes to an arbitrary scope in the set;
;; we pick the most recently allocated scope to make a binding search
;; faster and to improve GC, since non-nested binding contexts will
;; generally not share a most-recent scope.

(struct scope (id             ; internal scope identity; used for sorting
               kind           ; debug info
               [binding-table #:mutable]) ; see "binding-table.rkt"
        ;; Custom printer:
        #:property prop:custom-write
        (lambda (sc port mode)
          (write-string "#<scope:" port)
          (display (scope-id sc) port)
          (write-string ":" port)
          (display (scope-kind sc) port)
          (write-string ">" port))
        #:property prop:serialize
        (lambda (s ser-push! state)
          (unless (list-member? (serialize-state-reachable-scopes state) s)
            (error "internal error: found supposedly unreachable scope"))
          (cond
           [(eq? s top-level-common-scope)
            (ser-push! 'tag '#:scope)]
           [else
            (ser-push! 'tag '#:scope+kind)
            (ser-push! (scope-kind s))]))
        #:property prop:serialize-fill!
        (lambda (s ser-push! state)
          (cond
           [(binding-table-empty? (scope-binding-table s))
            (ser-push! 'tag #f)]
           [else
            (ser-push! 'tag '#:scope-fill!)
            (ser-push! (binding-table-prune-to-reachable (scope-binding-table s) state))]))
        #:property prop:reach-scopes
        (lambda (s reach)
          ;; the `bindings` field is handled via `prop:scope-with-bindings`
          (void))
        #:property prop:scope-with-bindings
        (lambda (s reachable-scopes reach register-trigger)
          (binding-table-register-reachable (scope-binding-table s)
                                            reachable-scopes
                                            reach
                                            register-trigger)))

(define deserialize-scope
  (case-lambda
    [() top-level-common-scope]
    [(kind)
     (scope (new-deserialize-scope-id!) kind empty-binding-table)]))

(define (deserialize-scope-fill! s bt)
  (set-scope-binding-table! s bt))

;; A "multi-scope" represents a group of scopes, each of which exists
;; only at a specific phase, and each in a distinct phase. This
;; infinite group of scopes is realized on demand. A multi-scope is
;; used to represent the inside of a module, where bindings in
;; different phases are distinguished by the different scopes within
;; the module's multi-scope.
;;
;; To compute a syntax's set of scopes at a given phase, the
;; phase-specific representative of the multi scope is combined with
;; the phase-independent scopes. Since a multi-scope corresponds to
;; a module, the number of multi-scopes in a syntax is expected to
;; be small.
(struct multi-scope (id       ; identity
                     name     ; for debugging
                     scopes   ; phase -> representative-scope
                     shifted  ; box of table: interned shifted-multi-scopes for non-label phases
                     label-shifted) ; box of table: interned shifted-multi-scopes for label phases
        #:property prop:serialize
        (lambda (ms ser-push! state)
          (ser-push! 'tag '#:multi-scope)
          (ser-push! (multi-scope-name ms))
          (ser-push! (multi-scope-scopes ms)))
        #:property prop:reach-scopes
        (lambda (ms reach)
          (reach (multi-scope-scopes ms))))

(define (deserialize-multi-scope name scopes)
  (multi-scope (new-deserialize-scope-id!) name scopes (box (hasheqv)) (box (hash))))

(struct representative-scope scope (owner   ; a multi-scope for which this one is a phase-specific identity
                                    phase)  ; phase of this scope
        #:mutable ; to support serialization
        #:property prop:custom-write
        (lambda (sc port mode)
          (write-string "#<scope:" port)
          (display (scope-id sc) port)
          (when (representative-scope-owner sc)
            (write-string "=" port)
            (display (multi-scope-id (representative-scope-owner sc)) port))
          (write-string "@" port)
          (display (representative-scope-phase sc) port)
          (write-string ">" port))
        #:property prop:serialize
        (lambda (s ser-push! state)
          (ser-push! 'tag '#:representative-scope)
          (ser-push! (scope-kind s))
          (ser-push! (representative-scope-phase s)))
        #:property prop:serialize-fill!
        (lambda (s ser-push! state)
          (ser-push! 'tag '#:representative-scope-fill!)
          (ser-push! (binding-table-prune-to-reachable (scope-binding-table s) state))
          (ser-push! (representative-scope-owner s)))
        #:property prop:reach-scopes
        (lambda (s reach)
          ;; the inherited `bindings` field is handled via `prop:scope-with-bindings`
          (reach (representative-scope-owner s))))

(define (deserialize-representative-scope kind phase)
  (define v (representative-scope (new-deserialize-scope-id!) kind #f #f phase))
  v)

(define (deserialize-representative-scope-fill! s bt owner)
  (deserialize-scope-fill! s bt)
  (set-representative-scope-owner! s owner))

(struct shifted-multi-scope (phase        ; non-label phase shift or shifted-to-label-phase
                             multi-scope) ; a multi-scope
        #:property prop:custom-write
        (lambda (sms port mode)
          (write-string "#<scope:" port)
          (display (multi-scope-id (shifted-multi-scope-multi-scope sms)) port)
          (write-string "@" port)
          (display (shifted-multi-scope-phase sms) port)
          (write-string ">" port))
        #:property prop:serialize
        (lambda (sms ser-push! state)
          (ser-push! 'tag '#:shifted-multi-scope)
          (ser-push! (shifted-multi-scope-phase sms))
          (ser-push! (shifted-multi-scope-multi-scope sms)))
        #:property prop:reach-scopes
        (lambda (sms reach)
          (reach (shifted-multi-scope-multi-scope sms))))

(define (deserialize-shifted-multi-scope phase multi-scope)
  (intern-shifted-multi-scope phase multi-scope))

(define (intern-shifted-multi-scope phase multi-scope)
  (define (transaction-loop boxed-table key make)
    (or (hash-ref (unbox boxed-table) phase #f)
        (let* ([val (make)]
               [current (unbox boxed-table)]
               [next (hash-set current key val)])
          (if (box-cas! boxed-table current next)
              val
              (transaction-loop boxed-table key make)))))
  (cond
   [(phase? phase)
    ;; `eqv?`-hashed by phase
    (or (hash-ref (unbox (multi-scope-shifted multi-scope)) phase #f)
        (transaction-loop (multi-scope-shifted multi-scope)
                          phase
                          (lambda () (shifted-multi-scope phase multi-scope))))]
   [else
    ;; `equal?`-hashed by shifted-to-label-phase
    (or (hash-ref (unbox (multi-scope-label-shifted multi-scope)) phase #f)
        (transaction-loop (multi-scope-label-shifted multi-scope)
                          phase
                          (lambda () (shifted-multi-scope phase multi-scope))))]))

;; A `shifted-to-label-phase` record in the `phase` field of a
;; `shifted-multi-scope` makes the shift reversible; when we're
;; looking up the label phase, then use the representative scope at
;; phase `from`; when we're looking up a non-label phase, there is no
;; corresponding representative scope
(struct shifted-to-label-phase (from) #:prefab)

;; Each new scope increments the counter, so we can check whether one
;; scope is newer than another.
(define id-counter 0)
(define (new-scope-id!)
  (set! id-counter (add1 id-counter))
  id-counter)

(define (new-deserialize-scope-id!)
  ;; negative scope ensures that new scopes are recognized as such by
  ;; having a larger id
  (- (new-scope-id!)))

;; A shared "outside-edge" scope for all top-level contexts
(define top-level-common-scope (scope 0 'module empty-binding-table))

(define (new-scope kind)
  (scope (new-scope-id!) kind empty-binding-table))

(define (new-multi-scope [name #f])
  (intern-shifted-multi-scope 0 (multi-scope (new-scope-id!) name (make-hasheqv) (box (hasheqv)) (box (hash)))))

(define (multi-scope-to-scope-at-phase ms phase)
  ;; Get the identity of `ms` at phase`
  (or (hash-ref (multi-scope-scopes ms) phase #f)
      (let ([s (representative-scope (new-scope-id!) 'module
                                     empty-binding-table
                                     ms phase)])
        (hash-set! (multi-scope-scopes ms) phase s)
        s)))

(define (scope>? sc1 sc2)
  ((scope-id sc1) . > . (scope-id sc2)))
(define (scope<? sc1 sc2)
  ((scope-id sc1) . < . (scope-id sc2)))

(define (shifted-multi-scope<? sms1 sms2)
  (define ms1 (shifted-multi-scope-multi-scope sms1))
  (define ms2 (shifted-multi-scope-multi-scope sms2))
  (if (eq? ms1 ms2)
      (let ([p1 (shifted-multi-scope-phase sms1)]
            [p2 (shifted-multi-scope-phase sms2)])
        (cond
         [(shifted-to-label-phase? p1)
          (cond
           [(shifted-to-label-phase? p2)
            (phase<? (shifted-to-label-phase-from p1) (shifted-to-label-phase-from p2))]
           [else #f])]
         [(shifted-to-label-phase? p2) #t]
         [else (phase<? p1 p2)]))
      ((multi-scope-id ms1) . < . (multi-scope-id ms2))))

;; Adding, removing, or flipping a scope is propagated
;; lazily to subforms
(define (apply-scope s sc op prop-op)
  (struct-copy syntax s
               [scopes (fallback-update-first (syntax-scopes s)
                                              (lambda (scs)
                                                (op (fallback-first scs) sc)))]
               [scope-propagations (and (datum-has-elements? (syntax-content s))
                                        (prop-op (syntax-scope-propagations s)
                                                 sc
                                                 (syntax-scopes s)))]))

(define (syntax-e/no-taint s)
  (propagate-taint! s)
  (define prop (syntax-scope-propagations s))
  (if prop
      (let ([new-content
             (non-syntax-map (syntax-content s)
                             (lambda (tail? x) x)
                             (lambda (sub-s)
                               (struct-copy syntax sub-s
                                            [scopes (propagation-apply
                                                     prop
                                                     (syntax-scopes sub-s)
                                                     s)]
                                            [scope-propagations (propagation-merge
                                                                 prop
                                                                 (syntax-scope-propagations sub-s)
                                                                 (syntax-scopes sub-s))])))])
        (set-syntax-content! s new-content)
        (set-syntax-scope-propagations! s #f)
        new-content)
      (syntax-content s)))

(define (syntax-e s)
  (define content (syntax-e/no-taint s))
  (cond
   [(not (tamper-armed? (syntax-tamper s))) content]
   [(datum-has-elements? content) (taint-content content)]
   [else content]))

;; When a representative-scope is manipulated, we want to
;; manipulate the multi scope, instead (at a particular
;; phase shift)
(define (generalize-scope sc)
  (if (representative-scope? sc)
      (intern-shifted-multi-scope (representative-scope-phase sc)
                                  (representative-scope-owner sc))
      sc))

(define (add-scope s sc)
  (apply-scope s (generalize-scope sc) set-add propagation-add))

(define (add-scopes s scs)
  (for/fold ([s s]) ([sc (in-list scs)])
    (add-scope s sc)))

(define (remove-scope s sc)
  (apply-scope s (generalize-scope sc) set-remove propagation-remove))

(define (remove-scopes s scs)
  (for/fold ([s s]) ([sc (in-list scs)])
    (remove-scope s sc)))

(define (set-flip s e)
  (if (set-member? s e)
      (set-remove s e)
      (set-add s e)))

(define (flip-scope s sc)
  (apply-scope s (generalize-scope sc) set-flip propagation-flip))

(define (flip-scopes s scs)
  (for/fold ([s s]) ([sc (in-list scs)])
    (flip-scope s sc)))

;; Pushes a multi-scope to accomodate multiple top-level namespaces.
;; See "fallback.rkt".
(define (push-scope s sms)
  (define-memo-lite (push scs/maybe-fallbacks)
    (define scs (fallback-first scs/maybe-fallbacks))
    (cond
     [(empty? scs) (list-add scs sms)]
     [(list-member? scs sms) scs/maybe-fallbacks]
     [else (fallback-push (list-add scs sms)
                          scs/maybe-fallbacks)]))
  (syntax-map s
              (lambda (tail? x) x)
              (lambda (s d)
                (struct-copy syntax s
                             [content d]
                             [scopes (push (syntax-scopes s))]))
              syntax-e/no-taint))

;; ----------------------------------------

(struct propagation (prev-scs scope-ops)
        #:property prop:propagation syntax-e)

(define (propagation-add prop sc prev-scs)
  (if prop
      (struct-copy propagation prop
                   [scope-ops (hash-set (propagation-scope-ops prop)
                                        sc
                                        'add)])
      (propagation prev-scs (hasheq sc 'add))))

(define (propagation-remove prop sc prev-scs)
  (if prop
      (struct-copy propagation prop
                   [scope-ops (hash-set (propagation-scope-ops prop)
                                        sc
                                        'remove)])
      (propagation prev-scs (hasheq sc 'remove))))

(define (propagation-flip prop sc prev-scs)
  (if prop
      (let* ([ops (propagation-scope-ops prop)]
             [current-op (hash-ref ops sc #f)])
        (cond
         [(and (eq? current-op 'flip)
               (= 1 (hash-count ops)))
          ;; Nothing left to propagate
          #f]
         [else
          (struct-copy propagation prop
                       [scope-ops
                        (if (eq? current-op 'flip)
                            (hash-remove ops sc)
                            (hash-set ops sc (case current-op
                                               [(add) 'remove]
                                               [(remove) 'add]
                                               [else 'flip])))])]))
      (propagation prev-scs (hasheq sc 'flip))))

(define (propagation-apply prop scs parent-s)
  (cond
   [(eq? (propagation-prev-scs prop) scs)
    (syntax-scopes parent-s)]
   [else
    (define new-scs
      (for/fold ([scs scs])
                ([(sc op) (in-immutable-hash (propagation-scope-ops prop))])
        (fallback-update-first
         scs
         (lambda (scs)
           (case op
             [(add) (set-add scs sc)]
             [(remove) (set-remove scs sc)]
             [else (set-flip scs sc)])))))
    ;; Improve sharing if the result clearly matches the parent:
    (define parent-scs (syntax-scopes parent-s))
    (if (and (set? new-scs)
             (set? parent-scs)
             (set=? new-scs parent-scs))
        parent-scs
        (cache-or-reuse-hash new-scs))]))

(define (propagation-merge prop base-prop prev-scs)
  (cond
   [(not base-prop)
    (cond
     [(eq? (propagation-prev-scs prop) prev-scs)
      prop]
     [else
      (propagation prev-scs
                   (propagation-scope-ops prop))])]
   [else
    (define new-ops
      (for/fold ([ops (propagation-scope-ops base-prop)]) ([(sc op) (in-immutable-hash (propagation-scope-ops prop))])
        (case op
          [(add) (hash-set ops sc 'add)]
          [(remove) (hash-set ops sc 'remove)]
          [else ; flip
           (define current-op (hash-ref ops sc #f))
           (case current-op
             [(add) (hash-set ops sc 'remove)]
             [(remove) (hash-set ops sc 'add)]
             [(flip) (hash-remove ops sc)]
             [else (hash-set ops sc 'flip)])])))
    (if (zero? (hash-count new-ops))
        #f
        (struct-copy propagation base-prop
                     [scope-ops new-ops]))]))

;; ----------------------------------------

;; To shift a syntax's phase, we only have to shift the phase
;; of any phase-specific scopes. The bindings attached to a
;; scope must be represented in such a way that the binding
;; shift is implicit via the phase in which the binding
;; is resolved.
(define (shift-multi-scope sms delta)
  (cond
   [(zero-phase? delta)
    ;; No-op shift
    sms]
   [(label-phase? delta)
    (cond
     [(shifted-to-label-phase? (shifted-multi-scope-phase sms))
      ;; Shifting to the label phase moves only phase 0, so
      ;; drop a scope that is already collapsed to phase #f
      #f]
     [else
      ;; Move the current phase 0 to the label phase, which
      ;; means recording the negation of the current phase
      (intern-shifted-multi-scope (shifted-to-label-phase (phase- 0 (shifted-multi-scope-phase sms)))
                                  (shifted-multi-scope-multi-scope sms))])]
   [(shifted-to-label-phase? (shifted-multi-scope-phase sms))
    ;; Numeric shift has no effect on bindings in phase #f
    sms]
   [else
    ;; Numeric shift added to an existing numeric shift
    (intern-shifted-multi-scope (phase+ delta (shifted-multi-scope-phase sms))
                                (shifted-multi-scope-multi-scope sms))]))

;; Since we tend to shift rarely and only for whole modules, it's
;; probably not worth making this lazy
(define (syntax-shift-phase-level s phase)
  (if (eqv? phase 0)
      s
      (let ()
        (define-memo-lite (shift-all scs)
          (fallback-map
           scs
           (lambda (scs)
             (for*/list ([sc scs]
                         [new-sc (in-value (if (shifted-multi-scope? sc)
                                               (shift-multi-scope sc phase)
                                               sc))]
                         #:when new-sc)
               new-sc))))
        (syntax-map s
                    (lambda (tail? d) d)
                    (lambda (s d)
                      (struct-copy syntax s
                                   [content d]
                                   [scopes
                                    (shift-all (syntax-scopes s))]))
                    syntax-e/no-taint))))

;; ----------------------------------------

;; Scope swapping is used to make top-level compilation relative to
;; the top level. Each top-level environment has a set of scopes that
;; identify the environment; usually, it's a common outside-edge scope
;; and a namespace-specific inside-edge scope, but there can be
;; additional scopes due to `module->namespace` on a module that was
;; expanded multiple times (where each expansion adds scopes).
(define (syntax-swap-scopes s src-scopes dest-scopes)
  (if (equal? src-scopes dest-scopes)
      s
      (let ([src-scs
             (for/seteq ([sc (in-set src-scopes)])
               (generalize-scope sc))]
            [dest-scs
             (for/seteq ([sc (in-set dest-scopes)])
               (generalize-scope sc))])
        (define-memo-lite (swap-scs scs)
          (fallback-update-first
           scs
           (lambda (scs)
             (if (subset? src-scs scs)
                 (set-union (set-subtract scs src-scs) dest-scs)
                 scs))))
        (syntax-map s
                    (lambda (tail? d) d)
                    (lambda (s d)
                      (struct-copy syntax s
                                   [content d]
                                   [scopes (swap-scs (syntax-scopes s))]))
                    syntax-e/no-taint))))

;; ----------------------------------------

;; Assemble the complete set of scopes at a given phase by extracting
;; a phase-specific representative from each multi-scope.
(define (syntax-scope-list s phase)
  (scope-list-at-fallback (fallback-first (syntax-scopes s)) phase))

(define (scope-list-at-fallback scs phase)
  (reverse
   (for*/fold ([scopes (list)])
              ([scope (in-list scs)])
     (cond [(not (shifted-multi-scope? scope))
            (list-add scopes scope)]
           [(or (label-phase? phase)
                (not (shifted-to-label-phase? (shifted-multi-scope-phase scope))))
            (list-add scopes
                      (multi-scope-to-scope-at-phase
                       (shifted-multi-scope-multi-scope scope)
                       (let ([ph (shifted-multi-scope-phase scope)])
                         (if (shifted-to-label-phase? ph)
                             (shifted-to-label-phase-from ph)
                             (phase- ph phase)))))]
           [else scopes]))))

(define (find-max-scope scopes)
  (when (empty? scopes)
    (error "cannot bind in empty scope set"))
  (car scopes))

(define (add-binding-in-scopes! scopes sym binding #:just-for-nominal? [just-for-nominal? #f])
  (define max-sc (find-max-scope scopes))
  (define bt (binding-table-add (scope-binding-table max-sc) scopes sym binding just-for-nominal?))
  (set-scope-binding-table! max-sc bt)
  (clear-resolve-cache! sym))

(define (add-bulk-binding-in-scopes! scopes bulk-binding)
  (define max-sc (find-max-scope scopes))
  (define bt (binding-table-add-bulk (scope-binding-table max-sc) scopes bulk-binding))
  (set-scope-binding-table! max-sc bt)
  (clear-resolve-cache!))

(define (syntax-any-scopes? s)
  (not (empty? (fallback-first (syntax-scopes s)))))

(define (syntax-any-macro-scopes? s)
  (for/or ([sc (fallback-first (syntax-scopes s))])
    (and (scope? sc) (eq? (scope-kind sc) 'macro))))

;; ----------------------------------------

;; Result is #f for no binding, `ambigious-value` for an ambigious binding,
;; or binding value
(define (resolve s phase
                 #:ambiguous-value [ambiguous-value #f]
                 #:exactly? [exactly? #f]
                 #:get-scopes? [get-scopes? #f] ; gets scope list instead of binding
                 ;; For resolving bulk bindings in `free-identifier=?` chains:
                 #:extra-shifts [extra-shifts null])
  (define sym (syntax-content s))
  (let fallback-loop ([scs (syntax-scopes s)])
    (cond
     [(and (not exactly?)
           (not get-scopes?)
           (resolve-cache-get sym phase (fallback-first scs)))
      => (lambda (b) b)]
     [else
      (define scopes (scope-list-at-fallback (fallback-first scs) phase))
      ;; As we look through all scopes, if we find two where neither
      ;; is a subset of the other, accumulate them into a list; maybe
      ;; we find a superset of both, later; if we end with a list,
      ;; then the binding is ambiguous. We expect that creating a list
      ;; of ambigious scopes is rare relative to eventual success.
      (define-values (best-scopes best-binding)
        (for*/fold ([best-scopes #f] [best-binding #f])
                   ([sc (in-set scopes)]
                    [(b-scopes binding) (in-binding-table sym (scope-binding-table sc) s extra-shifts)]
                    #:when (and b-scopes binding (subset? b-scopes scopes)))
          (cond
           [(pair? best-scopes)
            ;; We have a list of scopes where none is a superset of the others
            (cond
             [(for/and ([amb-scopes (in-list best-scopes)])
                (subset? amb-scopes b-scopes))
              ;; Found a superset of all
              (values b-scopes binding)]
             [else
              ;; Accumulate another ambiguous set
              (values (cons b-scopes best-scopes) #f)])]
           [(not best-scopes)
            (values b-scopes binding)]
           [(subset? b-scopes best-scopes) ; can be `set=?` if binding is overridden
            (values best-scopes best-binding)]
           [(subset? best-scopes b-scopes)
            (values b-scopes binding)]
           [else
            ;; Switch to ambigous mode
            (values (list best-scopes b-scopes) #f)])))
      (cond
       [(pair? best-scopes) ; => ambiguous
        (if (fallback? scs)
            (fallback-loop (fallback-rest scs))
            ambiguous-value)]
       [best-scopes
        (resolve-cache-set! sym phase (fallback-first scs) best-binding)
        (and (or (not exactly?)
                 (eqv? (set-count scopes)
                       (set-count best-scopes)))
             (if get-scopes?
                 best-scopes
                 best-binding))]
       [else
        (if (fallback? scs)
            (fallback-loop (fallback-rest scs))
            #f)])])))

;; ----------------------------------------

(define (bound-identifier=? a b phase)
  (and (eq? (syntax-e a)
            (syntax-e b))
       (equal? (syntax-scope-set a phase)
               (syntax-scope-set b phase))))
