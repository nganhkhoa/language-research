#lang plai

(require "ast.rkt")

;; the internal value
(define-type rize-value
  ;; basic types
  ;; [rz-id (name symbol?)]
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
                    (to rize-value?)]
  [rz-obligation (v rize-value?)
                 (c rize-value?)
                 (blame-in symbol?)
                 (blame-out symbol?)])

;; Obligations are placed on each reference to a val rec-defined vari- able.
;; through evaluation context, we know that
;; E ::= ... | e^{E,x,x} | E^{V,x,x}
;; - contract must be executed first
;; - then the expression is executed

(struct state
  (globals) ; a hash-map of rize-decl
  #:transparent)

(define initial-state (state (make-hash)))

(define (run program)
  (printf "run ~a\n" program)
  (let ([result (foldl interp initial-state program)])
    ; TODO: use state as a struct to store complex state
    result))

; return a new state, for folding
(define (interp expr state)
  ;; (printf "interp ~v\n" expr)
  (cond
    [(rize-decl? expr) (interp-decl expr state)]
    [(rize-expr? expr) (interp-expr expr state)]
    [else (error 'interp
                 "try to interp something not decl/expr ~a" expr)]))

(define (interp-decl expr state)
  (printf "interp-decl ~v\n" expr)
  (type-case rize-decl expr
             [val (id contract body)
                  ;; update the state with the value bound
                  (hash-set! (state-globals state)
                             id (list contract body))
                  state]))

(define (interp-expr expr state)
  (interp-expr-> expr state))

(define (interp-expr-> expr state)
  (printf "interp-expr ~v\n" expr)
  ;; the basic idea is to replace any references of rize-decl
  ;; to their equivalent rize-expr of e^{e,x,x}
  ;; and we should have the rules to reduce the contract
  ;; we can be lazy, and only replace when we actually use it?
  ;; (lift-contracts expr (state-globals state))
  (type-case rize-expr expr
             [num (n) (rz-num n)]
             [str (s) (rz-str s)]
             [bool (b) (rz-bool b)]
             [h-contract (from to)
                         (rz-contract-high (interp-contract from state)
                                           (interp-contract to state))]
             [f-contract (c) (rz-contract (interp-contract c state))]
             ;; if id is a reference to a global
             ;; then it must be replaced with obligation e^{e,x,x}
             ;; if a lambda, we have already replace the names already
             [id (name)
                 ;; (printf "~a\n" (hash-ref (state-globals state) name))
                 (match (hash-ref (state-globals state) name)
                   [(list contract body)
                    ;; replace the id to an obligation
                    ;; because we don't have two obligation expr
                    ;; but by the rules, we know we should eval
                    ;; contract and then body to a value
                    ;; then this will be an obligation
                    (define v-contract (interp-expr-> contract state))
                    (define v-body (interp-expr-> body state))
                    ;; (printf "contract is ~a\n" v-contract)
                    ;; (printf "body is ~a\n" v-body)
                    (rz-obligation v-body v-contract 'bruh 'bruh)]
                   [else (error 'interp "free identifier ~a" name)])]
             [aop (op left right) (perform-op op
                                              (interp-expr-> left state)
                                              (interp-expr-> right state))]
             [rop (op left right) (perform-op op
                                              (interp-expr-> left state)
                                              (interp-expr-> right state))]
             [function (arg body) (rz-function arg body)]
             [application (fun arg)
                          (define v-fun (interp-expr-> fun state))
                          (define v-arg (interp-expr-> arg state))
                          (cond
                            ;; either an obligation
                            [(rz-obligation? v-fun)
                             (printf "apply with obligation ~a ~a\n" v-fun v-arg)
                             (define arg-monitor
                               (rz-obligation v-arg
                                              (rz-contract-high-from
                                                (rz-obligation-c v-fun))
                                              (rz-obligation-blame-out v-fun)
                                              (rz-obligation-blame-in v-fun)))
                             ;; will raise error if contract violation
                             (rewrite-obligation-value arg-monitor state)
                             ;; continue applying
                             (define function (rz-obligation-v v-fun))
                             (define arg (rz-function-id function))
                             (define body (rz-function-body function))
                             (define result
                               (interp-expr->
                                 (subst arg (convert-expr v-arg) body)
                                 state))
                             ;; check result
                             (rewrite-obligation-value
                               (rz-obligation result
                                              (rz-contract-high-to
                                                (rz-obligation-c v-fun))
                                              (rz-obligation-blame-in v-fun)
                                              (rz-obligation-blame-out v-fun))
                               state)


                             ]
                             ;; (printf "value obligation ~a\n" arg-monitor)
                             ;; (define v-arg-monitor (interp-expr-> arg-monitor state))
                             ;; (printf "value monitor ~a\n" v-arg-monitor)
                             ;; (interp-expr->
                             ;;   (rz-obligation
                             ;;     (rz-obligation-v v-fun)
                             ;;     v-arg-monitor
                             ;;     (rz-obligation-blame-in v-fun)
                             ;;     (rz-obligation-blame-out v-fun))
                             ;;   state)]
                            ;; or a lambda
                            ;; [(rz-function? v-fun)
                            ;;  ()]
                            ;; or a fix
                            [else error 'interp "cannot apply a non-function ~a" fun])]
             [obligation (e c blame-in blame-out)
                         (error 'interp "hmmge ~a" expr)]
             [else (error 'interp "unimplemented ~a" expr)]))

(define (perform-op (op symbol?) (left rize-value?) (right rize-value?))
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

(define (rewrite-obligation-value value state)
  (define v (rz-obligation-v value))
  (define c (rz-obligation-c value))
  (define blame-in (rz-obligation-blame-in value))
  (define blame-out (rz-obligation-blame-in value))
  ;; (printf "obligation for ~a\n" v)
  ;; (printf "contract is ~a\n" c)
  ;; TODO: it could be applying a wrong contract type?
  (define guard (guard-evaluation (rz-contract-c c) v state))
  (cond
    [(rz-bool? guard)
     (if (eq? (rz-bool-b guard) true)
         v
         (error 'interp "rize contract violation ~a : ~a (blame who?)" v c))]))


(define (interp-contract contract state)
  (type-case rize-expr contract
             [id (name)
                 ;; here we just get the body
                 (match (hash-ref (state-globals state) name)
                   [(list contract body)
                    (rz-contract (interp-expr-> body state))]
                   [else (error 'interp
                                "unidentified function ~a in contract" name)])]
             [f-contract (e)
                         (rz-contract (interp-expr-> e state))]
             [h-contract (f t)
                         (rz-contract-high
                           (rz-contract (interp-contract f state))
                           (rz-contract (interp-contract t state)))]
             [else (error 'interp
                          "cannot resolve contract ~a" contract)]))

(define (guard-evaluation f v state)
  (type-case rize-value f
             [rz-function (arg body)
                          ;; v must be some value
                          ;; body must be function
                          ;; later we will turn into application
                          (printf "contract guard body ~a\n" body)
                          (interp-expr-> (subst arg (convert-expr v) body) state)]
             [rz-bool (b) b]
             [else (error 'guard
                          "guard was passed in a non-contract equivalent ~a" f)]))

(define (convert-expr v)
  (type-case rize-value v
             [rz-num (n) (num n)]
             [rz-str (s) (str s)]
             [rz-bool (b) (bool b)]
             [rz-nil () (nil)]
             ;; TODO: fix
             [rz-list (ls) (nil)]
             [rz-function (arg body)
                          (function arg body)]
             [else (error 'guard "cannot convert value to expr ~a" v)]))

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
             ;; will error when interp if not correct
             [else expr]))

;; (define (lift-contracts expr globals)
;;   (type-case rize-expr expr
;;              []))

;; (module+ test
;;   (test (interp ()))
;; )
