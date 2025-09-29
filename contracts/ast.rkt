#lang plai

(define-type rize-decl
  [val (id symbol?)
       (contract rize-expr?)
       (expr rize-expr?)])

(define-type rize-expr
  ;; basic types
  [num (n number?)]
  [id (name symbol?)]
  [str (s string?)]
  [bool (b boolean?)]
  [nil]
  ;; main language feature
  [function (arg symbol?)
            (expr rize-expr?)]
  [fixpoint (arg symbol?)
            (expr rize-expr?)]
  [application (func rize-expr?)
               (arg rize-expr?)]
  [condition (e rize-expr?)
             (true-branch rize-expr?)
             (false-branch rize-expr?)]
  [aop (op symbol?)
       (left rize-expr?)
       (right rize-expr?)]
  [rop (op symbol?)
       (left rize-expr?)
       (right rize-expr?)]
  [concat (left rize-expr?)
          (right rize-expr?)]
  [head (lst rize-expr?)]
  [tail (lst rize-expr?)]
  [mt (lst rize-expr?)]
  ;; contracts
  [high-contract (from rize-expr?)
                  (to rize-expr?)]
  [construct-contract (c rize-expr?)]
  [flatp (c rize-expr?)]
  [pred (c rize-expr?)]
  [dom (c rize-expr?)]
  [rng (c rize-expr?)]
  [blame (c rize-expr?)])

