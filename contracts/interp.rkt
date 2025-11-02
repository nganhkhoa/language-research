#lang plai

(require racket/trace)

(require "ast.rkt")

(define-type rz-value
             [rz-num (n number?)]
             [rz-str (s string?)]
             [rz-bool (b boolean?)]
             [rz-list (hd rz-value?) (rst rz-value?)]
             [rz-nil]
             [rz-function (id symbol?) (body rz-expr?)]
             [rz-app (funclike rz-value?) (arg rz-value?)]
             [rz-fcontract (c rz-value?)]
             [rz-hcontract (dom rz-value?) (rng rz-value?)]
             [rz-dcontract (arg-c rz-value?) (ret-c rz-value?)]
             [rz-obligation (v rz-value?) (c rz-value?) (in symbol?) (out symbol?)])

(define (run (program (listof rz-expr?)) (decls (listof rz-decl?)))
  ;; we actually don't want multiple expression, but just ignore it
  ;; because transform gives us an "inverted" program so we fold right
  (foldr (lambda (expr _)
           (with-handlers ([exn:fail? (lambda (exn)
                                        (printf "encountered error when running the program\n\n~a\n" exn))])
             (printf "~a => ~a\n" expr (interp expr decls))))
         '()
         program))

(define (get-name (name symbol?) (decls (listof rz-decl?)))
  (val-expr (car (filter (lambda (decl) (eq? name (val-id decl))) decls))))

(define (interp (expr rz-expr?) (decls (listof rz-decl?)))
  (type-case
   rz-expr
   expr
   ;; some first order element
   [id (name) (interp (get-name name decls) decls)]
   [num (n) (rz-num n)]
   [str (s) (rz-str s)]
   [bool (b) (rz-bool b)]
   [nil () (rz-nil)]
   [condition
    (e t-branch f-branch)
    (type-case rz-value
               (interp e decls)
               [rz-bool
                (b)
                (cond
                  [b (interp t-branch decls)]
                  [else (interp f-branch decls)])]
               ;; everything else is treated as true
               ;; whatever, type check should check this
               [else (error 'interp "if case can only switch on boolean")])]
   [aop (op lhs rhs) (perform-op op (interp lhs decls) (interp rhs decls))]
   [rop (op lhs rhs) (perform-op op (interp lhs decls) (interp rhs decls))]
   [concat (left right) (rz-list (interp left decls) (interp right decls))]
   [head
    (lst)
    (type-case rz-value
               (interp lst decls)
               [rz-list (hd _) hd]
               [rz-nil () (error 'interp "cannot get head of nil ~a" expr)]
               [else (error 'interp "cannot get head of non-list ~a" expr)])]
   [tail
    (lst)
    (type-case rz-value
               (interp lst decls)
               [rz-list (_ rst) rst]
               [rz-nil () (error 'interp "cannot get head of nil ~a" expr)]
               [else (error 'interp "cannot get head of non-list ~a" expr)])]
   [mt
    (lst)
    (type-case rz-value
               (interp lst decls)
               [rz-list (a b) (rz-bool false)]
               [rz-nil () (rz-bool true)]
               [else (error 'interp "non-list cannot check for empty ~a" expr)])]
   [function (arg body) (rz-function arg body)]
   [fixpoint (param body) (interp (subst param (fixpoint param body) body) decls)]
   [application
    (funclike arg)
    (define f (interp funclike decls))
    (define a (interp arg decls))
    (type-case
     rz-value
     f
     [rz-function (param body) (interp (subst param a body) decls)]
     [rz-obligation
      (v c in out)
      ;; make new obligation value yay
      (cond
        [(rz-hcontract? c)
         (define arg-guard (obligation-reduce (rz-obligation a (rz-hcontract-dom c) out in) decls))
         (obligation-reduce (rz-obligation (rz-app v arg-guard) (rz-hcontract-rng c) in out) decls)]
        [(rz-dcontract? c)
         (define arg-guard (obligation-reduce (rz-obligation a (rz-dcontract-arg-c c) out in) decls))
         (define ret-guard
           (type-case rz-value (rz-dcontract-ret-c c)
                      [rz-function (param body) (interp (subst param a body) decls)] ;; function returns contract
                      [else (error 'interp "dependent contract must be a function but ~a" (rz-dcontract-ret-c c))]))
         (obligation-reduce (rz-obligation (rz-app v arg-guard) ret-guard in out) decls)]
        [else (error 'interp "expecting obligation but ~a" f)])]
     [else (error 'interp "cannot call a non-callable value ~a" f)])]
   [h-contract (dom rng) (rz-hcontract (interp dom decls) (interp rng decls))]
   [d-contract (arg-check ret-check) (rz-dcontract (interp arg-check decls) (interp ret-check decls))]
   [f-contract (c) (rz-fcontract (interp c decls))]
   [obligation
    (e c in out)
    (define c-value (interp c decls))
    (define e-value (interp e decls))
    (obligation-reduce (rz-obligation e-value c-value in out) decls)]
   [else (error 'interp "unimplemented ~a" expr)]))

(define (obligation-reduce (obligation rz-value?) (decls (listof rz-decl?)))
  ;; higher order contract
  ;; example includes: V1^{A1->A2}^{B1->B2} V2
  ;; reduces to (V1^{A1->A2} V2^{B1})^{B2}
  ;; and further reduces to (V1 V2^{B1}^{A1})^{A2}^{B2}
  ;; this is by placing multiple constraints after going
  ;; through multiple function calls

  ;; two main rules
  ;; v^{contract(c)} -> if c(v) then v else blame
  ;; v1^{A->B} v2 -> (v1 v2^{A})^{B}
  ;; idk which rule should be applied first
  ;; but for the sake of simplicity, we check flat contract first then application
  (type-case
   rz-value
   obligation
   [rz-obligation
    (v c in out)
    ;; if e is rz-app then move on and apply the function
    (define reduced-v
      (type-case
       rz-value
       v
       [rz-app
        (function argument)
        (type-case
         rz-value
         function
         [rz-function (param body) (interp (subst param argument body) decls)]
         [else (error 'interp "higher order contract works with function only not ~a" function)])]
       [else v]))
    (cond
      ;; high order contract, e must be a call-able or rz-app
      [(rz-hcontract? c) (rz-obligation reduced-v c in out)]
      [(rz-dcontract? c) (rz-obligation reduced-v c in out)]
      [(rz-fcontract? c)
       ;; flat contract, e must be a basic value
       (type-case
        rz-value
        (rz-fcontract-c c)
        ;; check contract
        [rz-function
         (param body)
         (define condition (interp (subst param reduced-v body) decls))
         (type-case
          rz-value
          condition
          [rz-bool
           (b)
           (if b
               reduced-v
               (error 'interp "rize contract violation contract:~a value:~a at:~a" c reduced-v in))]
          [else (error 'interp "contract must return a boolean value")])]
        [else (error 'interp "contract is not callable ~a" c)])])]
   [else (error 'interp "can only reduce an obligation not ~a" obligation)]))

(define (as-expr (v rz-value?))
  (type-case rz-value
             v
             [rz-num (n) (num n)]
             [rz-str (s) (str s)]
             [rz-bool (b) (bool b)]
             [rz-function (param body) (function param body)]
             [rz-nil () (nil)]
             [rz-obligation (v c in out) (obligation (as-expr v) (as-expr c) in out)]
             [rz-hcontract (dom rng) (h-contract (as-expr dom) (as-expr rng))]
             [rz-fcontract (c) (f-contract (as-expr c))]
             [else error 'interp "can only convert basic value to expr ~a" v]))

(define (subst arg maybe-value expr)
  (define value
    (if (rz-expr? maybe-value)
        maybe-value
        (as-expr maybe-value)))
  (type-case
   rz-expr
   expr
   [id
    (name)
    (if (eq? name arg)
        value
        (id name))]
   [concat (left right) (concat (subst arg value left) (subst arg value right))]
   [aop (op left right) (aop op (subst arg value left) (subst arg value right))]
   [rop (op left right) (rop op (subst arg value left) (subst arg value right))]
   [condition (e t f) (condition (subst arg value e) (subst arg value t) (subst arg value f))]
   [head (ls) (head (subst arg value ls))]
   [tail (ls) (tail (subst arg value ls))]
   [mt (ls) (mt (subst arg value ls))]
   [function
    (name body)
    (if (eq? name arg)
        expr
        (function name (subst arg value body)))]
   [fixpoint
    (name body)
    (if (eq? name arg)
        expr
        (function name (subst arg value body)))]
   [application (name body) (application (subst arg value name) (subst arg value body))]
   [f-contract (c) (f-contract (subst arg value c))]
   [h-contract (d r) (h-contract (subst arg value d) (subst arg value r))]
   [d-contract (d r) (d-contract (subst arg value d) (subst arg value r))]
   ;; will error when interp if not correct
   [else expr]))

(define (perform-op (op symbol?) (left rz-value?) (right rz-value?))
  (define (do-op (left number?) (right number?))
    (match op
      ['+ (rz-num (+ left right))]
      ['- (rz-num (- left right))]
      ['* (rz-num (* left right))]
      ['/ (rz-num (/ left right))]
      ['>= (rz-bool (>= left right))]
      ['= (rz-bool (= left right))]
      [_ (error 'interp "cannot perform operation ~a" op)]
      ;; no extra case, guard by parser
      ))
  (cond
    [(and (rz-num? left) (rz-num? right)) (do-op (rz-num-n left) (rz-num-n right))]
    [else (error 'interp "cannot do-op a non-value ~a ~a" left right)]))

;; (trace interp)
;; (trace obligation-reduce)
;; (trace subst)
