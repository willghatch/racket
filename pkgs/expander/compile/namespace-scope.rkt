#lang racket/base
(require "../syntax/syntax.rkt"
         "../syntax/scope.rkt"
         "../common/phase.rkt"
         "../namespace/namespace.rkt"
         "../expand/root-expand-context.rkt")
         
(provide swap-top-level-scopes
         extract-namespace-scopes
         encode-namespace-scopes
         namespace-scopes=?)

;; In case a syntax object in compiled top-level code is from a
;; different namespace or deserialized, swap the current namespace's
;; scope for the original namespace's scope.
;;
;; To swap a namespace scopes, we partition the namespace scopes into
;; two groups: the scope that's added after every expansion (and
;; therefore appears on every binding form), and the other scopes that
;; indicate being original to the namespace. We swap those groups
;; separately.

(struct namespace-scopes (scs) #:prefab)

;; Swapping function, used at run time:
(define (swap-top-level-scopes s original-scopes-s new-ns)
  (define old-scs (if (pair? original-scopes-s)
                      original-scopes-s
                      (decode-namespace-scopes original-scopes-s)))
  (define new-scs (extract-namespace-scopes new-ns))
  (syntax-swap-scopes s old-scs new-scs))

(define (extract-namespace-scopes ns)
  (define root-ctx (namespace-get-root-expand-ctx ns))
  (root-expand-context-module-scopes root-ctx))

;; Extract namespace scopes to a syntax object, used at compile time:
(define (encode-namespace-scopes ns)
  (define scs (extract-namespace-scopes ns))
  (define s (add-scopes (datum->syntax #f 'post)
                        scs))
  (datum->syntax #f s))

;; Decoding, used at run time:
(define (decode-namespace-scopes stx)
  (syntax-scope-list stx 0))

(define (namespace-scopes=? nss1 nss2)
  (equal? nss1 nss2))
