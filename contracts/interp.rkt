#lang plai

(require "ast.rkt")

;; the internal value
(define-type rize-value
  ;; basic types
  [rz-num (n number?)]
  [rz-str (s string?)]
  [rz-bool (b boolean?)]
  ;; list must have empty value
  [rz-nil]
  [rz-list (ls (listof rize-value?))]
  ;; function as value that can be passed around
  [rz-function (id symbol?) (body rize-expr?)]
  ;; contracts and higher contracts
  [rz-contract (c rize-value?)]
  [rz-contract-high (from rize-value?)
                   (to rize-value?)])


;; (define-type state
;;   [])

(define (run program)
  ;; (printf "run ~a\n" program)
  (let ([result (foldl interp '() program)])
    ; TODO: use state as a struct to store complex state
    (car result)))

; return a new state, for folding
(define (interp expr state)
  ;; (printf "interp ~v\n" expr)
  (cond
    [(rize-decl? expr) (interp-decl expr state)]
    [else (interp-expr expr state)]))

(define (interp-decl expr state)
  (printf "interp-decl ~v\n" expr)
  (type-case rize-decl expr
             [val (id contract expr)
                  ;; evaluate contract
                  ;; evaluate expr
                  ;; put to state
                  state]))

(define (interp-expr expr state)
  (printf "interp-expr ~v\n" expr)
  (type-case rize-expr expr
             [num (n) '(n state)]
             [else (error 'interp "unimplemented ~a" expr)]))
