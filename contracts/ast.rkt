#lang plai

(define-type rz-decl [val (id symbol?) (contract rz-expr?) (expr rz-expr?)])

(define-type rz-expr
             ;; basic types
             [comment]
             [num (n number?)]
             [id (name symbol?)]
             [str (s string?)]
             [bool (b boolean?)]
             [nil]
             ;; main language feature
             [function (arg symbol?) (expr rz-expr?)]
             [fixpoint (arg symbol?) (expr rz-expr?)]
             [application (func rz-expr?) (arg rz-expr?)]
             [condition (e rz-expr?) (true-branch rz-expr?) (false-branch rz-expr?)]
             [aop (op symbol?) (left rz-expr?) (right rz-expr?)]
             [rop (op symbol?) (left rz-expr?) (right rz-expr?)]
             [concat (left rz-expr?) (right rz-expr?)]
             [head (lst rz-expr?)]
             [tail (lst rz-expr?)]
             [mt (lst rz-expr?)]
             ;; contracts
             [h-contract (from rz-expr?) (to rz-expr?)]
             [f-contract (c rz-expr?)]
             [flatp (c rz-expr?)]
             [pred (c rz-expr?)]
             [dom (c rz-expr?)]
             [rng (c rz-expr?)]
             [blame (c rz-expr?)]
             [obligation (e rz-expr?) (c rz-expr?) (blame-in symbol?) (blame-out symbol?)])
