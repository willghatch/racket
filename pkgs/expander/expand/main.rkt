#lang racket/base
(require "../common/set.rkt"
         "../syntax/syntax.rkt"
         "../syntax/property.rkt"
         "../syntax/scope.rkt"
         "../syntax/taint.rkt"
         "../syntax/taint-dispatch.rkt"
         "../syntax/match.rkt"
         "../namespace/namespace.rkt"
         "../namespace/module.rkt"
         "../namespace/inspector.rkt"
         "../syntax/binding.rkt"
         "env.rkt"
         "../syntax/track.rkt"
         "../syntax/error.rkt"
         "syntax-id-error.rkt"
         "syntax-implicit-error.rkt"
         "free-id-set.rkt"
         "dup-check.rkt"
         "use-site.rkt"
         "../compile/main.rkt"
         "../eval/top.rkt"
         "../namespace/core.rkt"
         "../boot/runtime-primitive.rkt"
         "context.rkt"
         "lift-context.rkt"
         "already-expanded.rkt"
         "liberal-def-ctx.rkt"
         "rename-trans.rkt"
         "allowed-context.rkt"
         "lift-key.rkt"
         "../syntax/debug.rkt"
         "reference-record.rkt"
         "log.rkt"
         "../common/performance.rkt"
         "parsed.rkt")

(provide expand
         lookup
         apply-transformer
         
         register-variable-referenced-if-local!
         
         expand/capture-lifts
         expand-transformer
         expand+eval-for-syntaxes-binding
         eval-for-syntaxes-binding
         eval-for-bindings

         keep-properties-only
         keep-as-needed
         rebuild
         attach-disappeared-transformer-bindings
         increment-binding-layer
         accumulate-def-ctx-scopes
         rename-transformer-target-in-context)

;; ----------------------------------------

;; Main expander dispatch
(define (expand s ctx
                ;; Aplying a rename transformer substitutes
                ;; an id without changing `s`
                #:alternate-id [alternate-id #f])
  (log-expand ctx (if (expand-context-only-immediate? ctx) 'enter-check 'visit) s)
  (cond
   [(identifier? s)
    (expand-identifier s ctx alternate-id)]
   [(and (pair? (syntax-e/no-taint s))
         (identifier? (car (syntax-e/no-taint s))))
    (expand-id-application-form s ctx alternate-id)]
   [(or (pair? (syntax-e (syntax-disarm s)))
        (null? (syntax-e (syntax-disarm s))))
    ;; An "application" form that doesn't start with an identifier, so
    ;; use implicit `#%app`
    (expand-implicit '#%app s ctx #f)]
   [(already-expanded? (syntax-e/no-taint s))
    (expand-already-expanded s ctx)]
   [else
    ;; Anything other than an identifier or parens triggers the
    ;; implicit `#%datum` form
    (expand-implicit '#%datum s ctx #f)]))

;; An identifier by itself (i.e., not after an open parenthesis)
(define (expand-identifier s ctx alternate-id)
  (define id (or alternate-id s))
  (guard-stop
   id ctx s
   (define binding (resolve+shift id (expand-context-phase ctx)
                                  #:ambiguous-value 'ambiguous
                                  #:immediate? #t))
   (log-expand* ctx #:unless (expand-context-only-immediate? ctx) ['resolve id])
   (cond
    [(eq? binding 'ambiguous)
     (raise-ambiguous-error id ctx)]
    [(not binding)
     ;; The implicit `#%top` form handles unbound identifiers
     (expand-implicit '#%top (substitute-alternate-id s alternate-id) ctx s)]
    [else
     ;; Variable or form as identifier macro
     (define-values (t primitive? insp-of-t) (lookup binding ctx id
                                                     #:in (and alternate-id s)
                                                     #:out-of-context-as-variable? (expand-context-in-local-expand? ctx)))
     (dispatch t insp-of-t s id ctx binding primitive?)])))

;; An "application" form that starts with an identifier
(define (expand-id-application-form s ctx alternate-id)
  (define disarmed-s (syntax-disarm s #f))
  (define id (or alternate-id (car (syntax-e disarmed-s))))
  (guard-stop
   id ctx s
   (define binding (resolve+shift id (expand-context-phase ctx)
                                  #:ambiguous-value 'ambiguous
                                  #:immediate? #t))
   (log-expand* ctx #:unless (expand-context-only-immediate? ctx) ['resolve id])
   (cond
    [(eq? binding 'ambiguous)
     (raise-ambiguous-error id ctx)]
    [(not binding)
     ;; The `#%app` binding might do something with unbound ids
     (expand-implicit '#%app (substitute-alternate-id s alternate-id) ctx id)]
    [else
     ;; Find out whether it's bound as a variable, syntax, or core form
     (define-values (t primitive? insp-of-t) (lookup binding ctx id
                                                     #:in (and alternate-id (car (syntax-e disarmed-s)))
                                                     #:out-of-context-as-variable? (expand-context-in-local-expand? ctx)))
     (cond
      [(variable? t)
       ;; Not as syntax or core form, so use implicit `#%app`
       (expand-implicit '#%app (substitute-alternate-id s alternate-id) ctx id)]
      [else
       ;; Syntax or core form as "application"
       (dispatch t insp-of-t s id ctx binding primitive?)])])))

;; Handle an implicit: `#%app`, `#%top`, or `#%datum`; this is similar
;; to handling an id-application form, but there are several little
;; differences: the binding must be a core form or transformer,
;; an implicit `#%top` is handled specially, and so on
(define (expand-implicit sym s ctx trigger-id)
  (define disarmed-s (syntax-disarm s))
  (define id (datum->syntax disarmed-s sym))
  (guard-stop
   id ctx s
   (define b (resolve+shift id (expand-context-phase ctx)
                            #:ambiguous-value 'ambiguous
                            #:immediate? #t))
   (cond
    [(eq? b 'ambiguous)
     (raise-ambiguous-error id ctx)]
    [else
     (define-values (t primitive? insp-of-t) (if b (lookup b ctx id) (values #f #f #f)))
     (cond
      [(transformer? t)
       (dispatch-transformer t insp-of-t (make-explicit sym s disarmed-s) id ctx b)]
      [(expand-context-only-immediate? ctx)
       (log-expand ctx 'exit-check s)
       s]
      [(core-form? t)
       (cond
        [(and (eq? sym '#%top)
              (eq? (core-form-name t) '#%top)
              (expand-context-in-local-expand? ctx))
         (dispatch-implicit-#%top-core-form t s ctx)]
        [else
         (dispatch-core-form t (make-explicit sym s disarmed-s) ctx)])]
      [else
       (define tl-id
         (and (eq? sym '#%top)
              (root-expand-context-top-level-bind-scope ctx)
              (add-scope s (root-expand-context-top-level-bind-scope ctx))))
       (define tl-b (and tl-id (resolve tl-id (expand-context-phase ctx))))
       (cond
        [tl-b
         ;; Special case: the identifier is not bound and its scopes don't
         ;; have a binding for `#%top`, but it's bound temporaily for compilation;
         ;; treat the identifier as a variable reference
         (if (expand-context-to-parsed? ctx)
             (parsed-id tl-id tl-b)
             tl-id)]
        [else
         (raise-syntax-implicit-error s sym trigger-id ctx)])])])))

;; An expression that is already fully expanded via `local-expand-expression`
(define (expand-already-expanded s ctx)
  (define ae (syntax-e s))
  (when (or (syntax-any-macro-scopes? s)
            (not (eq? (expand-context-binding-layer ctx)
                      (already-expanded-binding-layer ae))))
    (raise-syntax-error #f
                        (string-append "expanded syntax not in its original lexical context;\n"
                                       " extra bindings or scopes in the current context")
                        (already-expanded-s ae)))
  (define result-s (syntax-track-origin (already-expanded-s ae) s))
  (log-expand* ctx ['tag result-s] ['opaque-expr result-s])
  (if (expand-context-to-parsed? ctx)
      (expand result-s ctx) ; fully expanded to compiled
      result-s))

(define (make-explicit sym s disarmed-s)
  (syntax-rearm (datum->syntax disarmed-s (cons sym disarmed-s) s s) s))

;; ----------------------------------------

;; Expand `s` given that the value `t` of the relevant binding,
;; where `t` is either a core form, a macro transformer, some
;; other compile-time value (which is an error), or a token
;; indicating that the binding is a run-time variable; note that
;; `s` is not disarmed
(define (dispatch t insp-of-t s id ctx binding primitive?)
  (cond
   [(core-form? t)
    (dispatch-core-form t s ctx)]
   [(transformer? t)
    (dispatch-transformer t insp-of-t s id ctx binding)]
   [(variable? t)
    (dispatch-variable t s id ctx binding primitive?)]
   [else
    ;; Some other compile-time value:
    (raise-syntax-error #f "illegal use of syntax" s)]))

;; Call a core-form expander (e.g., `lambda`)
(define (dispatch-core-form t s ctx)
  (cond
   [(expand-context-only-immediate? ctx)
    (log-expand ctx 'exit-check s)
    s]
   [else
    (log-expand ctx 'enter-prim s)
    (define result-s ((core-form-expander t) s ctx))
    (log-expand* ctx ['exit-prim result-s] ['return result-s])
    result-s]))

;; Special favor to `local-expand` from `expand-implicit`: call
;; `#%top` form without making `#%top` explicit in the form
(define (dispatch-implicit-#%top-core-form t s ctx)
  (log-expand ctx 'enter-prim s)
  (define result-s ((core-form-expander t) s ctx #t))
  (log-expand* ctx ['exit-prim result-s] ['return result-s])
  result-s)

;; Call a macro expander, taking into account whether it works
;; in the current context, whether to expand just once, etc.
(define (dispatch-transformer t insp-of-t s id ctx binding)
  (cond
   [(not-in-this-expand-context? t ctx)
    (log-expand ctx 'enter-macro s)
    (define adj-s (avoid-current-expand-context (substitute-alternate-id s id) t ctx))
    (log-expand ctx 'exit-macro s)
    (expand adj-s ctx)]
   [else
    (log-expand* ctx #:when (expand-context-only-immediate? ctx) ['visit s] ['resolves id])
    ;; Apply transformer and expand again
    (define-values (exp-s re-ctx)
      (if (rename-transformer? t)
          (values s ctx)
          (apply-transformer t insp-of-t s id ctx binding)))
    (log-expand* ctx #:when (expand-context-only-immediate? ctx) ['return exp-s])
    (cond
     [(expand-context-just-once? ctx) exp-s]
     [else (expand exp-s re-ctx
                   #:alternate-id (and (rename-transformer? t)
                                       (syntax-track-origin (rename-transformer-target-in-context t ctx)
                                                            id
                                                            id)))])]))

;; Handle the expansion of a variable to itself
(define (dispatch-variable t s id ctx binding primitive?)
  (cond
   [(expand-context-only-immediate? ctx)
    (log-expand ctx 'exit-check s)
    id]
   [else
    (log-expand ctx 'variable s)
    ;; A reference to a variable expands to itself
    (register-variable-referenced-if-local! binding)
    ;; If the variable is locally bound, replace the use's scopes with the binding's scopes
    (define result-s (substitute-variable id t #:no-stops? (free-id-set-empty-or-just-module*? (expand-context-stops ctx))))
    (cond
     [(expand-context-to-parsed? ctx)
      (if primitive?
          (parsed-primitive-id result-s binding)
          (parsed-id result-s binding))]
     [else
      (log-expand ctx 'return result-s)
      result-s])]))

;; ----------------------------------------

;; Given a macro transformer `t`, apply it --- adding appropriate
;; scopes to represent the expansion step; the `insp-of-t` inspector
;; is the inspector of the module that defines `t`, which gives it
;; priviledge for `syntax-arm` and similar
(define (apply-transformer t insp-of-t s id ctx binding)
  (performance-region
   ['expand '_ 'macro]
   
   (log-expand ctx 'enter-macro s)
   (define disarmed-s (syntax-disarm s))
   (define intro-scope (new-scope 'macro))
   (define intro-s (flip-scope disarmed-s intro-scope))
   ;; In a definition context, we need use-site scopes
   (define-values (use-s use-scopes) (maybe-add-use-site-scope intro-s ctx binding))
   ;; Avoid accidental transfer of taint-controlling properties:
   (define cleaned-s (syntax-remove-taint-dispatch-properties use-s))
   ;; Prepare to accumulate definition contexts created by the transformer
   (define def-ctx-scopes (box null))
   
   ;; Call the transformer; the current expansion context may be needed
   ;; for `syntax-local-....` functions, and we may accumulate scopes from
   ;; definition contexts created by the transformer
   (define transformed-s
     (apply-transformer-in-context t cleaned-s ctx insp-of-t
                                   intro-scope use-scopes def-ctx-scopes
                                   id))
   
   ;; Flip the introduction scope
   (define result-s (flip-scope transformed-s intro-scope))
   ;; In a definition context, we need to add the inside-edge scope to
   ;; any expansion result
   (define post-s (maybe-add-post-expansion-scope result-s ctx))
   ;; Track expansion:
   (define tracked-s (syntax-track-origin post-s cleaned-s id))
   (define rearmed-s (taint-dispatch tracked-s (lambda (t-s) (syntax-rearm t-s s)) (expand-context-phase ctx)))
   (log-expand ctx 'exit-macro rearmed-s)
   (values rearmed-s
           (accumulate-def-ctx-scopes ctx def-ctx-scopes))))

;; With all the pre-call scope work done and post-call scope work in
;; the continuation, actually call the transformer function in the
;; appropriate context
(define (apply-transformer-in-context t cleaned-s ctx insp-of-t
                                      intro-scope use-scopes def-ctx-scopes
                                      id)
  (log-expand ctx 'macro-pre-x cleaned-s)
  (define confine-def-ctx-scopes?
    (not (or (expand-context-only-immediate? ctx)
             (not (free-id-set-empty-or-just-module*? (expand-context-stops ctx))))))
  (define accum-ctx
    (if (and confine-def-ctx-scopes?
             (expand-context-def-ctx-scopes ctx)
             (not (null? (unbox (expand-context-def-ctx-scopes ctx)))))
        (accumulate-def-ctx-scopes ctx (expand-context-def-ctx-scopes ctx))
        ctx))
  (define m-ctx (struct-copy expand-context accum-ctx
                             [current-introduction-scopes (cons intro-scope
                                                                use-scopes)]
                             [def-ctx-scopes
                               (if confine-def-ctx-scopes?
                                   ;; Can confine tracking to this call
                                   def-ctx-scopes
                                   ;; Keep old def-ctx-scopes box, so that we don't
                                   ;; lose them at the point where expansion stops
                                   (expand-context-def-ctx-scopes ctx))]))
  (define transformed-s
    (parameterize ([current-expand-context m-ctx]
                   [current-namespace (namespace->namespace-at-phase
                                       (expand-context-namespace ctx)
                                       (add1 (expand-context-phase ctx)))]
                   [current-module-code-inspector (or insp-of-t (current-module-code-inspector))])
      (call-with-continuation-barrier
       (lambda ()
         ;; Call the transformer!
         ((transformer->procedure t) cleaned-s)))))
  (log-expand ctx 'macro-post-x transformed-s)
  (unless (syntax? transformed-s)
    (raise-arguments-error (syntax-e id)
                           "received value from syntax expander was not syntax"
                           "received" transformed-s))
  transformed-s)

(define (maybe-add-use-site-scope s ctx binding)
  (cond
   #;[(and (root-expand-context-use-site-scopes ctx)
         (matching-frame? (root-expand-context-frame-id ctx)
                          (binding-frame-id binding)))
    ;; We're in a recursive definition context where use-site scopes
    ;; are needed, so create one, record it, and add to the given
    ;; syntax
    (define sc (new-scope 'use-site))
    (define b (root-expand-context-use-site-scopes ctx))
    (set-box! b (cons sc (unbox b)))
    (values (add-scope s sc) (list sc))]
   [else (values s null)]))

(define (matching-frame? current-frame-id bind-frame-id)
  (and current-frame-id
       (or (eq? current-frame-id bind-frame-id)
           (eq? current-frame-id 'all))))

(define (maybe-add-post-expansion-scope s ctx)
  (cond
   [(root-expand-context-post-expansion-scope ctx)
    ;; We're in a definition context where, say, an inside-edge scope
    ;; needs to be added to any immediate macro expansion; that way,
    ;; if the macro expands to a definition form, the binding will be
    ;; in the definition context's scope. The sepcific action depends
    ;; on the expansion context.
    ((expand-context-post-expansion-scope-action ctx)
     s
     (root-expand-context-post-expansion-scope ctx))]
   [else s]))

(define (accumulate-def-ctx-scopes ctx def-ctx-scopes)
  ;; Move any accumulated definition-context scopes to the `scopes`
  ;; list for further expansion:
  (if (null? (unbox def-ctx-scopes))
      ctx
      (struct-copy expand-context ctx
                   [scopes (append (unbox def-ctx-scopes)
                                   (expand-context-scopes ctx))])))

;; ----------------------------------------

;; Helper to lookup a binding in an expansion context
(define (lookup b ctx id
                #:in [in-s #f]
                #:out-of-context-as-variable? [out-of-context-as-variable? #f])
  (binding-lookup b
                  (expand-context-env ctx)
                  (expand-context-lift-envs ctx)
                  (expand-context-namespace ctx)
                  (expand-context-phase ctx)
                  id
                  #:in in-s
                  #:out-of-context-as-variable? out-of-context-as-variable?))

(define-syntax-rule (guard-stop id ctx s otherwise ...)
  (cond
   [(free-id-set-member? (expand-context-stops ctx)
                         (expand-context-phase ctx)
                         id)
    (log-expand* ctx #:unless (expand-context-only-immediate? ctx)
                 ['enter-prim s] ['prim-stop] ['exit-prim s] ['return s])
    s]
   [else
    otherwise ...]))

(define (substitute-alternate-id s alternate-id)
  (cond
   [(not alternate-id) s]
   [(identifier? s) (syntax-rearm (syntax-track-origin alternate-id s) s)]
   [else
    (define disarmed-s (syntax-disarm s))
    (syntax-rearm (syntax-track-origin (datum->syntax
                                        disarmed-s
                                        (cons alternate-id
                                              (cdr (syntax-e disarmed-s)))
                                        s)
                                       s)
                       s)]))

(define (register-variable-referenced-if-local! binding)
  ;; If the binding's frame has a reference record, then register
  ;; the use for the purposes of `letrec` splitting
  (when (and (local-binding? binding)
             (reference-record? (binding-frame-id binding)))
    (reference-record-used! (binding-frame-id binding) (local-binding-key binding))))

;; ----------------------------------------

;; Expand `s` as a compile-time expression relative to the current
;; expansion context
(define (expand/capture-lifts s ctx
                              #:expand-lifts? [expand-lifts? #f]
                              #:begin-form? [begin-form? #f]
                              #:lift-key [lift-key (generate-lift-key)]
                              #:always-wrap? [always-wrap? #f])
  (define context (expand-context-context ctx))
  (define phase (expand-context-phase ctx))
  (define local? (not begin-form?)) ;; see "[*]" below
  ;; Expand `s`, but loop to handle lifted expressions
  (let loop ([s s] [always-wrap? always-wrap?] [ctx ctx])
    (define lift-env (and local? (box empty-env)))
    (define lift-ctx (make-lift-context
                      (if local?
                          (make-local-lift lift-env (root-expand-context-counter ctx))
                          (make-top-level-lift ctx))
                      #:module*-ok? (and (not local?) (eq? context 'module))))
    (define capture-ctx (struct-copy expand-context ctx
                                     [lift-key #:parent root-expand-context lift-key]
                                     [lifts lift-ctx]
                                     [lift-envs (if local?
                                                    (cons lift-env
                                                          (expand-context-lift-envs ctx))
                                                    (expand-context-lift-envs ctx))]
                                     [module-lifts (if (or local?
                                                           (not (memq context '(top-level module))))
                                                       (expand-context-module-lifts ctx)
                                                       lift-ctx)]))
    (define exp-s (expand s capture-ctx))
    (define lifts (get-and-clear-lifts! (expand-context-lifts capture-ctx)))
    (define with-lifts-s
      (cond
       [(or (pair? lifts) always-wrap?)
        (cond
         [(expand-context-to-parsed? ctx)
          (unless expand-lifts? (error "internal error: to-parsed mode without expanding lifts"))
          (wrap-lifts-as-parsed-let lifts exp-s s ctx (lambda (rhs rhs-ctx) (loop rhs #f rhs-ctx)))]
         [else
          (if begin-form?
              (wrap-lifts-as-begin lifts exp-s s phase)
              (wrap-lifts-as-let lifts exp-s s phase))])]
       [else exp-s]))
    (cond
     [(or (not expand-lifts?) (null? lifts) (expand-context-to-parsed? ctx))
      ;; Expansion is done
      with-lifts-s]
     [else
      ;; Expand again...
      (log-expand ctx 'lift-loop with-lifts-s)
      (loop with-lifts-s #f ctx)])))

;; [*] Although `(memq context '(top-level module))` makes more sense
;;     than `(not begin-form?)`, the latter was used historically; the
;;     implementation of `typed/require` currently depends on that
;;     choice, because it expands in 'expression mode to obtain forms
;;     that are splcied into a module context --- leading to an
;;     out-of-context definition error if the historical choice is not
;;     preserved.

;; Expand `s` as a compile-time expression relative to the current
;; expansion context
(define (expand-transformer s ctx
                            #:context [context 'expression]
                            #:begin-form? [begin-form? #f]
                            #:expand-lifts? [expand-lifts? #t]
                            #:lift-key [lift-key (generate-lift-key)]
                            #:always-wrap? [always-wrap? #f])
  (performance-region
   ['expand 'transformer]

   (define trans-ctx (context->transformer-context ctx context))
   (expand/capture-lifts s trans-ctx
                         #:expand-lifts? expand-lifts?
                         #:begin-form? begin-form?
                         #:lift-key lift-key
                         #:always-wrap? always-wrap?)))

(define (context->transformer-context ctx [context 'expression])
  (define phase (add1 (expand-context-phase ctx)))
   (define ns (namespace->namespace-at-phase (expand-context-namespace ctx)
                                             phase))
   (namespace-visit-available-modules! ns phase)
   (struct-copy expand-context ctx
                [context context]
                [scopes null]
                [phase phase]
                [namespace ns]
                [env empty-env]
                [only-immediate? #f]
                [def-ctx-scopes #f]
                [post-expansion-scope #:parent root-expand-context #f]))

;; Expand and evaluate `s` as a compile-time expression, ensuring that
;; the number of returned values matches the number of target
;; identifiers; return the expanded form as well as its values
(define (expand+eval-for-syntaxes-binding rhs ids ctx)
  (define exp-rhs (expand-transformer rhs (as-named-context ctx ids)))
  (define phase (add1 (expand-context-phase ctx)))
  (define parsed-rhs (if (expand-context-to-parsed? ctx)
                         exp-rhs
                         (expand exp-rhs (context->transformer-context
                                          (as-to-parsed-context ctx)))))
  (values exp-rhs
          parsed-rhs
          (eval-for-bindings ids
                             parsed-rhs
                             phase
                             (namespace->namespace-at-phase
                              (expand-context-namespace ctx)
                              phase)
                             ctx)))

;; Expand and evaluate `s` as a compile-time expression, returning
;; only the compile-time values
(define (eval-for-syntaxes-binding rhs ids ctx)
  (define-values (exp-rhs parsed-rhs vals)
    (expand+eval-for-syntaxes-binding rhs ids ctx))
  vals)

;; Expand and evaluate `s` as an expression in the given phase;
;; ensuring that the number of returned values matches the number of
;; target identifiers; return the values
(define (eval-for-bindings ids p phase ns ctx)
  (define compiled (compile-single p (make-compile-context
                                      #:namespace ns
                                      #:phase phase)))
  (define vals
    (call-with-values (lambda ()
                        (parameterize ([current-expand-context ctx]
                                       [current-namespace ns]
                                       [eval-jit-enabled #f])
                          (eval-single-top compiled ns)))
      list))
  (unless (= (length vals) (length ids))
    (error "wrong number of results (" (length vals) "vs." (length ids) ")"
           "from" p))
  vals)

;; ----------------------------------------

(define (keep-properties-only s)
  (datum->syntax #f 'props s s))

;; Drop the `syntax-e` part of `s`, and also drop its scopes when
;; producing a parsed result, producing a result suitable for use with
;; `rebuild` or including in a `parsed` record. Dropping references in
;; this way helps the GC not retain too much of an original syntax
;; object in the process of expanding it, which can matter for deeply
;; nested expansions.
(define (keep-as-needed ctx s #:for-track? [for-track? #f])
  (cond
   [(expand-context-to-parsed? ctx) (keep-properties-only s)]
   [else
    (define d (and for-track? (syntax-e s)))
    (syntax-rearm (datum->syntax (syntax-disarm s)
                                 (cond
                                  [(symbol? d) d]
                                  [(and (pair? d) (identifier? (car d))) (syntax-e (car d))]
                                  [else #f])
                                 s
                                 s)
                  s)]))

;; A helper for forms to reconstruct syntax while preserving source
;; locations, properties, and arming; if `track?` is #f, then don't keep
;; properties, because we've kept them in a surrounding form
(define (rebuild orig-s new
                 #:track? [track? #t])
  (syntax-rearm (datum->syntax (syntax-disarm orig-s) new orig-s (and track? orig-s))
                orig-s))

(define (attach-disappeared-transformer-bindings s trans-idss)
   (cond
    [(null? trans-idss) s]
    [else
     (syntax-property s
                      'disappeared-binding
                      (append (apply append trans-idss)
                              (or (syntax-property s 'disappeared-binding)
                                  null)))]))

;; Generate a fresh binding-layer identity if `ids` contains any
;; identifiers
(define (increment-binding-layer ids ctx layer-val)
  (if (let loop ([ids ids])
        (or (identifier? ids)
            (and (pair? ids)
                 (or (loop (car ids)) (loop (cdr ids))))))
      layer-val
      (expand-context-binding-layer ctx)))

;; Wrap lifted forms in a `let` for a mode where we're generating a
;; parsed result. The body has already been parsed, and the left-hand
;; sides already have bindings. We need to parse the right-hand sides
;; as a series of nested `lets`.
(define (wrap-lifts-as-parsed-let lifts exp-s s ctx parse-rhs)
  (define idss+keyss+rhss (get-lifts-as-lists lifts))
  (let lets-loop ([idss+keyss+rhss idss+keyss+rhss] [rhs-ctx ctx])
    (cond
     [(null? idss+keyss+rhss) exp-s]
     [else
      (define ids (caar idss+keyss+rhss))
      (define keys (cadar idss+keyss+rhss))
      (define rhs (caddar idss+keyss+rhss))
      (define exp-rhs (parse-rhs rhs rhs-ctx))
      (parsed-let-values
       s
       (list ids)
       (list (list keys exp-rhs))
       (list
        (lets-loop (cdr idss+keyss+rhss)
                   (struct-copy expand-context rhs-ctx
                                [env (for/fold ([env (expand-context-env rhs-ctx)]) ([id (in-list ids)]
                                                                                     [key (in-list keys)])
                                       (env-extend env key (local-variable id)))]))))])))

;; A rename transformer can have a `prop:rename-transformer` property
;; as a function, and that fnuction might want to use
;; `syntax-local-value`, etc.
(define (rename-transformer-target-in-context t ctx)
  (parameterize ([current-expand-context ctx])
    (rename-transformer-target t)))
