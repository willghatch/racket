#lang racket/base
(require "../common/set.rkt"
         "syntax.rkt"
         "scope.rkt"
         "fallback.rkt"
         "binding-table.rkt"
         (submod "scope.rkt" for-debug)
         "binding.rkt"
         "module-binding.rkt")

(provide syntax-debug-info)

(define (syntax-debug-info s phase all-bindings?)
  (define hts
    (for/list ([scopes (in-list (fallback->list (syntax-scopes s)))])
      (define init-ht (if (identifier? s)
                          (hasheq 'name (syntax-e s))
                          #hasheq()))
      (define s-scs (scope-set-at-fallback scopes phase))
      (define context (scope-set->context s-scs))
      (define context-ht (hash-set init-ht 'context context))
      (define sym (syntax-e s))
      (define bindings
        (cond
         [(identifier? s)
          (define-values (bindings covered-scopess)
            (for*/fold ([bindings null] [covered-scope-sets (set)])
                       ([sc (in-set s-scs)]
                        [(scs b) (in-binding-table sym (scope-binding-table sc) s null)]
                        #:when (and scs b
                                    (or all-bindings?
                                        (subset? scs s-scs))
                                    ;; Skip overidden:
                                    (not (set-member? covered-scope-sets scs))))
              (values
               (cons
                (hash 'name (syntax-e s)
                      'context (scope-set->context scs)
                      'match? (subset? scs s-scs)
                      (if (local-binding? b)
                          'local
                          'module)
                      (if (local-binding? b)
                          (local-binding-key b)
                          (vector (module-binding-sym b)
                                  (module-binding-module b)
                                  (module-binding-phase b))))
                bindings)
               (set-add covered-scope-sets scs))))
          bindings]
         [else null]))
      (if (null? bindings)
          context-ht
          (hash-set context-ht 'bindings bindings))))
  (define ht (car hts))
  (if (null? (cdr hts))
      ht
      (hash-set ht 'fallbacks (cdr hts))))

(define (scope-set->context scs)
  (sort
   (for/list ([sc (in-set scs)])
     (if (representative-scope? sc)
         (vector (scope-id sc)
                 (scope-kind sc)
                 (multi-scope-name (representative-scope-owner sc)))
         (vector (scope-id sc)
                 (scope-kind sc))))
   <
   #:key (lambda (v) (vector-ref v 0))))
