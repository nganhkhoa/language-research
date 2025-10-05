#lang plai

(require "ast.rkt")

(define (find-decl (name symbol?) (decls (listof rize-decl?)))
  (match decls
    [(list) null]
    [(list hd rst ...)
     (if (eq? name (val-id hd))
         hd
         (find-decl name rst))]))

;; TODO: need a way to record symbol -> (or rize-expr rize-decl)
;; right now we don't allow shadowing
(define (lift-obligation (expr rize-expr?)
                         (decls (listof rize-decl?))
                         (blame-out symbol?))
  ;; (printf "lift obligation ~a\n" expr)
  (type-case rize-expr expr
             [num (n) (num n)]
             [str (s) (str s)]
             [bool (b) (bool b)]
             [nil () (nil)]
             [aop (op left right) (aop op
                                       (lift-obligation left decls blame-out)
                                       (lift-obligation right decls blame-out))]
             [rop (op left right) (rop op
                                       (lift-obligation left decls blame-out)
                                       (lift-obligation right decls blame-out))]
             [id (name)
                 ;; either a lambda/fix bound value
                 ;; we don't have a way to know if shadow
                 ;; or a free identifier to `val rec`
                 ;; we only care if it is a ref to `val rec`
                 ;; -> obligation expression
                 (define decl (find-decl name decls))
                 (cond
                   [(eq? decl null) (id name)]
                   [else (obligation (val-expr decl)
                                     (val-contract decl)
                                     (val-id decl)
                                     blame-out)])]
             [h-contract (dom rng)
                         (h-contract (lift-obligation dom decls blame-out)
                                     (lift-obligation rng decls blame-out))]
             [f-contract (c)
                         (f-contract (lift-obligation c decls blame-out))]
             [condition (c t-branch f-branch)
                       (condition (lift-obligation c decls blame-out)
                                  (lift-obligation t-branch decls blame-out)
                                  (lift-obligation f-branch decls blame-out))]
             [function (arg body)
                       (function arg (lift-obligation body decls blame-out))]
             [application (funclike value)
                       (application
                         (lift-obligation funclike decls blame-out)
                         (lift-obligation value decls blame-out))]
             [else (error 'transform "fail to transform ~a" expr)]))

(define (lift-single-decl (decl rize-decl?) (decls rize-decl?))
  (type-case rize-decl decl
             [val (name contract body)
                  (val name
                       (lift-obligation contract decls name)
                       (lift-obligation body decls name))]))

;; because all decls must be evaluated to a value
;; that means we can have functions that returns a contract
;; or have something that returns a contract
;; and apply that contract to the decls
;; and it will be used across the program
;; we force strict order, so A: B, B: A is impossible
;;
;; evaluation contexts P
(define (lift-decls (decls (listof rize-decl?)))
  (foldl (lambda (decl previous)
           (cons (lift-single-decl decl previous) previous))
         (list) decls))

;; transformer will try to walk the tree and apply obligation
;;
;; the basic idea is that variables that are val rec when referenced
;; are enforced/transformed into an obligation
;; this means that we will replace free variables to obligation
;; if is it a val rec
(define (transform (exprs rize-expr?) (decls (listof rize-decl?)))
  (define decls-transformed (lift-decls decls))
  ;; (printf "declarations ~a\n" decls-transformed)
  ;; (printf "program ~a\n" exprs)
  ;; now we have all declarations compiled
  (foldl (lambda (expr program)
            (cons (lift-obligation expr decls-transformed 'main) program))
         (list)
         exprs))
