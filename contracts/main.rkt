#lang racket

(require racket/base)

(require "ast.rkt")
(require "parser.rkt")
(require "interp.rkt")
(require "transformer.rkt")

(define (read-file path)
  (with-input-from-file path
    (lambda ()
      (port->string))))

(define (program-text->datum program-text)
  (let ([wrapped-text (format "(~a)" program-text)])
    (read (open-input-string wrapped-text))))

(define (try-parse program-expr)
  (define (try-parse-element s-expr)
    (with-handlers
      ([exn:fail?
         (lambda (_) (parse s-expr))])
      (parse-decl s-expr)))
  (map try-parse-element program-expr))

(define (main-program args)
  (cond
    [(empty? args)
     (printf "Usage: racket main.rkt <program-file.rkt>~n")]

    [(equal? 1 (length args))
     (let* ([file-path (first args)]
            [program-text (read-file file-path)]
            [program-expr (program-text->datum program-text)]
            [program (try-parse program-expr)]
            [decls (filter rize-decl? program)]
            [exprs (filter rize-expr? program)]
            [exprs (filter (lambda (x) (not (comment? x))) exprs)]
            [program-ready (transform exprs decls)]
            ; TODO: Type check
            [_ (run program-ready)])
       (printf "Complete\n"))]

    [else
     (printf "Too many arguments.~n")]))

(module* main #f
  (main-program (vector->list (current-command-line-arguments))))
