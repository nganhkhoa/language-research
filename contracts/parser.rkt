#lang plai

(require "ast.rkt")

(define (is-rop? (op symbol?))
  (match op
    ['+ true]
    ['- true]
    ['- true]
    ['/ true]
    [else false]))

(define (is-aop? (op symbol?))
  (match op
    ['>= true]
    ['= true]
    [else false]))

(define (is-con? (op symbol?))
  (eq? ':: op))

(define (is-lambda? (op symbol?))
  (eq? 'lambda op))

(define (is-fix? (op symbol?))
  (eq? 'fix op))

(define (is-contract? (op symbol?))
  (eq? '-> op))

(define (is-keyword? (name symbol?))
  (member name '['hd 'td 'mt
                 'lambda 'fix
                 'if 'then 'else
                 'contract
                 'flatp 'pred 'dom 'rng 'blame]))

(define (parse s-expr)
  ; (printf "parsing expr ~v\n" s-expr)
  (cond
    [(number? s-expr) (num s-expr)]
    [(string? s-expr) (str s-expr)]
    [(boolean? s-expr) (bool s-expr)]
    [(empty? s-expr) (nil)]
    [(symbol? s-expr)
     (if (or (is-rop? s-expr)
             (is-aop? s-expr)
             (is-lambda? s-expr)
             (is-fix? s-expr)
             (is-contract? s-expr)
             (is-keyword? s-expr))
         (error 'parse "cannot use name ~a" s-expr)
         (id s-expr))]

    ;; because we expect an expression, so it should simple to parse
    [(list? s-expr)
     (match s-expr
       ; application has 2 arguments
       [(list fst snd)
        (cond
          ;; special functions like hd/td/mt are parsed to
          ;; the expression, which will have their own rules
          ;; instead of relying on runtime execution
          [(symbol? fst)
           (match fst
             ['hd (head (parse snd))]
             ['td (tail (parse snd))]
             ['mt (mt (parse snd))]
             ['contract (f-contract (parse snd))]
             ['flatp (flatp (parse snd))]
             ['pred (pred (parse snd))]
             ['dom (dom (parse snd))]
             ['rng (rng (parse snd))]
             ['blame (blame (parse snd))]
             [else (application (id fst) (parse snd))])]
          ;; fst argument is an expression (aka lambda), so parse
          [else (application (parse fst) (parse snd))])]

       ; arithmetic, comparison, concat have 3 arguments
       [(list fst snd rd)
        (cond
          [(and (is-lambda? fst)
                (symbol? snd)) (function snd (parse rd))]
          [(and (is-fix? fst)
                (symbol? snd)) (fixpoint snd (parse rd))]
          [(is-aop? snd) (aop snd (parse fst) (parse rd))]
          [(is-rop? snd) (rop snd (parse fst) (parse rd))]
          [(is-con? snd) (concat (parse fst) (parse rd))]
          ;; contract parsing
          [(is-contract? snd) (h-contract (parse fst) (parse rd))]
          [else
            (error 'parse
                   "expected either lambda, fix, aop, rop, or :: at ~a" s-expr)])]

       ; if expression has 6 arguments
       [(list 'if b 'then t 'else f)
        (condition (parse b) (parse t) (parse f))]

       [else (error 'parse "cannot parse ~a" s-expr)])]
    [else (error 'parse "cannot parse ~a" s-expr)]))

(define (parse-decl s-expr)
  ; (printf "parsing expr ~v\n" s-expr)
  (match s-expr
    ;; no contract
    [(list 'val 'rec x '= e)
     (val x (f-contract (function '_ (bool true))) (parse e))]
    ;; with contract
    [(list 'val 'rec x ': c '= e)
     (val x (parse c) (parse e))]
    [else (error 'parse "cannot parse declaration ~a" s-expr)]))

(module+ test

  (test (parse `1)
        (num 1))

  (test (parse `x)
        (id 'x))

  (test (parse `#t)
        (bool true))

  (test (parse `"hello world")
        (str "hello world"))

  (test (parse `{1 + 1})
        (rop '+ (num 1) (num 1)))

  (test (parse `{1 >= 2})
        (aop '>= (num 1) (num 2)))

  (test (parse `{1 :: []})
        (concat (num 1) (nil)))

  (test (parse `{g (lambda x 25)})
        (application (id 'g) (function 'x (num 25))))

  (test (parse `{(lambda x (x + 1)) 1})
        (application (function 'x (rop '+ (id 'x) (num 1))) (num 1)))

  (test (parse `{g (fix x 25)})
        (application (id 'g) (fixpoint 'x (num 25))))

  (test (parse `{(fix x (x + 1)) 1})
        (application (fixpoint 'x (rop '+ (id 'x) (num 1))) (num 1)))

  (test (parse `{hd(1 :: [])})
        (head (concat (num 1) (nil))))

  (test (parse `{if #t then 1 else 2})
        (condition (bool #t) (num 1) (num 2)))

  (test (parse-decl `{val rec gt9 = (lambda x (x >= 9))})
        (val 'gt9 (nil) (function 'x (aop '>= (id 'x) (num 9)))))

  (test (parse-decl `{val rec bet0_99 = (lambda x (if (99 >= x) then (x >= 0) else #f))})
        (val 'bet0_99 (nil)
             (function 'x (condition (aop '>= (num 99) (id 'x))
                                     (aop '>= (id 'x) (num 0))
                                     (bool #f)))))

  (test (parse-decl `{val rec g : ((gt9 -> bet0_99) -> bet0_99) = (lambda f (f 0))})
        (val 'g
             (h-contract (h-contract (id 'gt9) (id 'bet0_99))
                         (id 'bet0_99))
             (function 'f (application (id 'f) (num 0)))))

)
