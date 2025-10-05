#lang plai

(require "ast.rkt")

(define-type rz-value
             [rz-num (n number?)]
             [rz-str (s string?)]
             [rz-bool (b boolean?)]
             [rz-list (hd rz-value?) (rst rz-value?)]
             [rz-nil]
             [rz-function (id symbol?) (body rize-expr?)]
             [rz-fcontract (c rz-value?)]
             [rz-hcontract (dom rz-value?)
                           (rng rz-value?)]
             [rz-obligation (v rz-value?)
                            (c rize-expr?)
                            (in symbol?)
                            (out symbol?)])

(define (run (program rize-expr?))
  ;; we actually don't want multiple expression, but just ignore it
  (foldl (lambda (expr _) (interp expr)) '() program))

(define (interp (expr rize-expr?))
  ;; (printf "interp ~a\n" expr)
  (type-case rize-expr expr
             ;; some first order element
             [num (n) (rz-num n)]
             [str (s) (rz-str s)]
             [bool (b) (rz-bool b)]
             [nil () (rz-nil)]
             [condition (e t-branch f-branch)
                        (type-case rz-value (interp e)
                          [rz-bool (b) (cond
                                         [b (interp t-branch)]
                                         [else (interp f-branch)])]
                          [rz-num (n) (cond
                                        [(eq? n 0) (interp f-branch)]
                                        [else (interp t-branch)])]
                          ;; everything else is treated as true
                          ;; whatever, type check should check this
                          [else (interp t-branch)])]
             [aop (op lhs rhs) (perform-op op (interp lhs) (interp rhs))]
             [rop (op lhs rhs) (perform-op op (interp lhs) (interp rhs))]
             [concat (left right)
                     (rz-list (interp left) (interp right))]

             [head (lst)
                   (type-case rz-value (interp lst)
                     [rz-list (hd _) hd]
                     [rz-nil ()
                             (error 'interp "cannot get head of nil ~a" expr)]
                     [else (error 'interp "cannot get head of non-list ~a" expr)])]
             [tail (lst)
                   (type-case rz-value (interp lst)
                     [rz-list (_ rst) rst]
                     [rz-nil ()
                             (error 'interp "cannot get head of nil ~a" expr)]
                     [else (error 'interp "cannot get head of non-list ~a" expr)])]
             [mt (lst)
                  (type-case rz-value (interp lst)
                    [rz-list (a b) (rz-bool false)]
                    [rz-nil () (rz-bool true)]
                    [else (error 'interp "non-list cannot check for empty ~a" expr)])]

             ;; function
             [function (arg body)
                       (rz-function arg body)]
             ;; TODO: fix fixpoint function
             [fixpoint (arg body)
                       (rz-function arg body)]

             [application (funclike arg) (interp-apply (interp funclike) arg)]
             ;; [h-contract (dom rng)
             ;;             (rz-hcontract (interp dom) (interp rng))]
             ;; [f-contract (c) (rz-fcontract (interp c))]
             [obligation (e c in out)
                         (rz-obligation (interp e) c in out)]
             [else (error 'interp "unimplemented ~a" expr)]))

(define (interp-apply (funclike rz-value?) (arg rize-expr?))
  ;; (printf "apply function ~a ~a\n" funclike arg)
  (type-case rz-value funclike
    ;; this feels awkward, because body is rz-value
    ;; arg is also rz-value when evaluated
    ;; i think we need an interp-value
    ;; we don't evaluate, so it's call by name
    [rz-function (param body)
                 (interp (subst param arg body))]
    [rz-obligation
      ;; body is already rz-value
      (body contract in out)
      ;; body^{contract, in, out}
      ;; (printf "obligation body ~a\n" body)
      ;; (printf "obligation contract ~a\n" contract)
      ;; although the paper wants us to evaluate
      ;; but if we evaluate, then we have to convert back to a function
      ;; function^{dom -> rng,in,out} arg
      ;; =>
      ;; (function (arg^{dom,out,in}))^{rng,in,out}
      ;; evaluate argument first

      ;; at this point contract must be a high order contract
      ;; because this is a function

      ;; but because we also transform `val rec` to contract
      ;; so when checking for upper contract, we go down to flat-contract
      ;; as well

      ;; g = ...
      ;; f: g = ...
      ;; f x
      ;; g has contract (_ -> true)
      ;; f has contract g
      ;; while checking for x in g
      ;; x itself must be compatible with g contract

      (cond
        [(f-contract? contract)
         ;; when g has a flat contract
         ;; input to g is a value
         ;; this is a single case, because when g is itself a value
         ;; it will not have contract
         ;; so only happens in compositional contracts
         (define arg-safe
           (contract-guard (obligation arg contract out in)))
         (interp-apply body arg-safe)]
        [(h-contract? contract)
         ;; other cases, including when g expect a function
         (define arg-safe
           (contract-guard
             (obligation arg (h-contract-from contract) out in)))
         (define result-unsafe (interp-apply body arg-safe))
         (contract-guard
           (obligation (as-expr result-unsafe) (h-contract-to contract) in out))])]
    [else (error 'interp "cannot apply non-function value ~a" funclike)]))

(define (as-expr (v rz-value?))
  (type-case rz-value v
             [rz-num (n) (num n)]
             [rz-str (s) (str s)]
             [rz-bool (b) (bool b)]
             [rz-function (param body)
                          (function param body)]
             [rz-nil () (nil)]
             [else error 'interp "can only convert basic value to expr ~a" v]))

(define (subst arg value expr)
  (type-case rize-expr expr
             [id (name) (if (eq? name arg)
                            value
                            (id name))]
             [concat (left right) (concat (subst arg value left)
                                          (subst arg value right))]
             [aop (op left right)
                  (aop op (subst arg value left) (subst arg value right))]
             [rop (op left right)
                  (rop op (subst arg value left) (subst arg value right))]
             [condition (e t f)
                        (condition (subst arg value e)
                                   (subst arg value t)
                                   (subst arg value f))]
             [head (ls) (head (subst arg value ls))]
             [tail (ls) (tail (subst arg value ls))]
             [mt (ls) (mt (subst arg value ls))]
             [function (name body)
                       (if (eq? name arg)
                           expr
                           (function name (subst arg value body)))]
             [fixpoint (name body)
                       (if (eq? name arg)
                           expr
                           (function name (subst arg value body)))]
             [application (name body)
                          (application (subst arg value name)
                                       (subst arg value body))]
             ;; will error when interp if not correct
             [else expr]))


(define (contract-guard (value rize-expr?) (is-in boolean?))
  (define error-msg (lambda (v c in out)
                      (error 'interp "contract violation ~a of ~a by ~a"
                             c v (if is-in in out))))
  (type-case rize-expr value
    ;; [function (param body) (interp (subst param value body))]
    [obligation (v c in out)
      (type-case rz-value (interp-apply (interp (f-contract-c c)) v)
        [rz-bool (b) (if b v (error-msg v c in out))]
        [else (error 'interp "contract must return bool (type-check)")])]
    [else (error 'interp "contract guard apply to a non-obligation ~a" value)]))

(define (perform-op (op symbol?) (left rz-value?) (right rz-value?))
  (define (do-op (left number?) (right number?))
    (match op
      ['+ (rz-num (+ left right))]
      ['- (rz-num (- left right))]
      ['* (rz-num (* left right))]
      ['/ (rz-num (/ left right))]
      ['>= (rz-bool (>= left right))]
      ['= (rz-bool (= left right))]
      ;; no extra case, guard by parser
      ))
  (cond
    [(and (rz-num? left)
          (rz-num? right))
     (do-op (rz-num-n left) (rz-num-n right))]
    [else (error 'interp "cannot do-op a non-value ~a ~a" left right)]))
