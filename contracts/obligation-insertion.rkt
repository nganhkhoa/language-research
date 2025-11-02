#lang plai

(require racket/trace)

(require "ast.rkt")

;; this file provides an obligation insertion according to the I function defined
;; in the index of https://www2.ccs.neu.edu/racket/pubs/NU-CCIS-02-05.pdf

;; I in paper
(define (obligation-insert (decls (listof rz-decl?)) (e rz-expr?))
  (define new-decls
    (foldl (lambda (decl cur)
             (type-case rz-decl
                        decl
                        [val
                         (name contract expr)
                         (define new-contract (do-obligation-insert contract decls name (list)))
                         (define new-expr (do-obligation-insert expr decls name (list)))
                         (cons (val name new-contract new-expr) cur)]))
           (list)
           decls))

  (define new-e (do-obligation-insert e decls 'main (list)))
  (values new-decls new-e))

(define (try-get-decl (name symbol?) (decls (listof rz-decl?)))
  ;; what if not found
  (define found (filter (lambda (decl) (eq? name (val-id decl))) decls))
  (if (empty? found) null (car found)))

;; Ie in paper
;; PSA, the paper has a lot of typos
;; shadow-names should be a set not list
(define (do-obligation-insert (e rz-expr?)
                              (decls (listof rz-decl?))
                              (outer-name symbol?)
                              (shadow-names (listof symbol?)))
  (type-case rz-expr
             e
             [comment () (comment)]
             [num (n) (num n)]
             [str (s) (str s)]
             [bool (b) (bool b)]
             [nil () (nil)]
             [id
              (name)
              (define decl (try-get-decl name decls))
              (cond
                [(or (null? decl) (member name shadow-names)) (id name)]
                [else (obligation (id name) (val-contract decl) name outer-name)])]
             [condition
              (e t f)
              (condition (do-obligation-insert e decls outer-name shadow-names)
                         (do-obligation-insert t decls outer-name shadow-names)
                         (do-obligation-insert f decls outer-name shadow-names))]
             ;; function related
             [function
              (param body)
              ;; the paper has a typo
              ;; Ie(lambda y. e, p, n, s) = lambda y. Ie(n, p, e, s + {y})
              ;; but n is a name and cannot be used as expression
              (function param (do-obligation-insert body decls outer-name (cons param shadow-names)))]
             [application
              (e1 e2)
              (application (do-obligation-insert e1 decls outer-name shadow-names)
                           (do-obligation-insert e2 decls outer-name shadow-names))]
             ;; numerical and boolean operations
             [aop
              (op lhs rhs)
              (aop op
                   (do-obligation-insert lhs decls outer-name shadow-names)
                   (do-obligation-insert rhs decls outer-name shadow-names))]
             [rop
              (op lhs rhs)
              (rop op
                   (do-obligation-insert lhs decls outer-name shadow-names)
                   (do-obligation-insert rhs decls outer-name shadow-names))]
             ;; list operations
             [concat
              (l r)
              (concat (do-obligation-insert l decls outer-name shadow-names)
                      (do-obligation-insert r decls outer-name shadow-names))]
             [head (lst) (head (do-obligation-insert lst decls outer-name shadow-names))]
             [tail (lst) (tail (do-obligation-insert lst decls outer-name shadow-names))]
             [mt (lst) (mt (do-obligation-insert lst decls outer-name shadow-names))]
             ;; contract operations
             [h-contract
              (domain range)
              (h-contract (do-obligation-insert domain decls outer-name shadow-names)
                          (do-obligation-insert range decls outer-name shadow-names))]
             [f-contract (c) (f-contract (do-obligation-insert c decls outer-name shadow-names))]
             [pred (c) (f-contract (do-obligation-insert c decls outer-name shadow-names))]
             [dom (c) (f-contract (do-obligation-insert c decls outer-name shadow-names))]
             [rng (c) (f-contract (do-obligation-insert c decls outer-name shadow-names))]
             [blame (c) (f-contract (do-obligation-insert c decls outer-name shadow-names))]
             [else (error 'obligation-insert "cannot insert obligation to ~a" e)]))

;; (trace do-obligation-insert)
;; (trace try-get-decl)
