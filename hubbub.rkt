#lang racket #| ★ CSC324 Fall 2019: Assignment 1 ★ |#
#|
Module: hubbub_errors
Description: Assignment 1: Building an Interpreter
Copyright: (c) University of Toronto
               CSC324 Principles of Programming Languages, Fall 2019

The assignment handout can be found at
https://www.cs.toronto.edu/~david/csc324/assignments/a1/handout.html
|#
(provide run-interpreter)

(require racket/hash)  ; You may use the functions imported from this module.
(require "hubbub_errors.rkt")


;-----------------------------------------------------------------------------------------
; Main functions (skeleton provided in starter code)
;-----------------------------------------------------------------------------------------

;Error checking functions
(define (check-duplicate-define id env)
  (if (hash-has-key? env id) (report-error 'duplicate-name id) void))

(define (check-duplicate-param params)
  (cond
    [(empty? params) void]
    [(member (first params) (rest params)) (report-error 'duplicate-name (first params))]
    [else
     (check-duplicate-param (rest params))
    ])
)

#|(define (check-function id env)
  (if
    (equal? (interpret env (procedure? id)) #t) (void)
    (report-error 'not-a-function id)
    )
)|#





#|
(run-interpreter prog) -> any
  prog: datum?
    A syntactically-valid Hubbub program.

  Evaluates the Hubbub program and returns its value, or raises an error if the program is
  not semantically valid.
|#
(define (run-interpreter prog)
  (match prog
    [(list bindings ... expr) (interpret (build-env bindings) expr)]
    )
  )

#|
(interpret env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.
  expr: datum?
    A syntactically-valid Hubbub expression.

  Returns the value of the Hubbub expression under the given environment.
|#
(define (interpret env expr)
  (match expr
    [(? number?) expr] ; handle literals
    [(? boolean?) expr]
    [(? symbol?) (interpret env (hash-ref env expr))] ; handle variable
    [(list '+ a b) (+ (interpret env a) (interpret env b))] ; handle builtin functions
    [(list '< a b) (< (interpret env a) (interpret env b))]
    [(list 'equal? a b) (equal? (interpret env a) (interpret env b))]
    [(list 'integer? a) (integer? (interpret env a))]
    [(list  'boolean? a) (boolean? (interpret env a))]
    ; check whether procedure
    [(list 'procedure? possible-procedure)
     (match possible-procedure
       ['+ #t] ; build in functions are procedures
       ['< #t]
       ['equal? #t]
       ['integer? #t]
       ['boolean? #t]
       ['procedure? #t]
       [(list 'lambda params expr) #t] ; anon function
       [(? symbol?) (closure? (hash-ref env possible-procedure))] ; identifier refers to a closure in env
       )]
    ; handle lambda def, return closure
    [(list 'lambda params expr)
     (check-duplicate-param params)
     (closure params expr env)]
    ; handle function call
    [(list ID args ...)
     (match ID
       [(list 'lambda params expr) (interpret (add-params-mapping env params args ) expr) ] ; anon n-ary non 
       [else
        (interpret (add-params-mapping (closure-env (hash-ref env ID)) (closure-params (hash-ref env ID)) args ) (closure-body (hash-ref env ID)))]) ; n-ary call
     ] 
    )
  )


;-----------------------------------------------------------------------------------------
; Helpers: Builtins and closures
;-----------------------------------------------------------------------------------------
; A hash mapping symbols for Hubbub builtin functions to their corresponding Racket value.
(define builtins
  (hash
   '+ +
   'equal? equal?
   '< <
   'integer? integer?
   'boolean? boolean?
   ; Note: You'll almost certainly need to replace procedure? here to properly return #t
   ; when given your closure data structure at the end of Task 1!
   'procedure? procedure?
   ))

; Returns whether a given symbol refers to a builtin Hubbub function.
(define (builtin? identifier) (hash-has-key? builtins identifier))

#|
Starter definition for a closure "struct". Racket structs behave similarly to
C structs (contain fields but no methods or encapsulation).
Read more at https://docs.racket-lang.org/guide/define-struct.html.

You can and should modify this as necessary. If you're having trouble working with
Racket structs, feel free to switch this implementation to use a list/hash instead.
|#
(struct closure (params body env))

; environment builders
(define (build-env bindings) 
  (foldl update_env builtins bindings))

(define (update_env binding env)
  (match binding
    [(list 'define ID b)
     (check-duplicate-define ID env)
     (match b 
       [(? symbol?) (hash-set env ID (hash-ref env b))] ; variable define b = a
       [else (hash-set env ID (interpret env b))] ; want ID to val binding, not ID to expr
       )
     ]
    )
  )

(define (add-params-mapping env params args)
  (if (equal? (length params) (length args)) 
  (let
      ([update-params-mapping (lambda(param params-mapping) (hash-set params-mapping param (interpret env (list-ref args (index-of params param))) ) )])
    (foldl update-params-mapping env params)
    )
  (report-error 'arity-mismatch (length args) (length params))
  )
)

;(add-params-mapping (build-env '((define a 4) (define b 4))) (list) (list))

(run-interpreter '((define a (+ 4 4))
                   (define b 4)
                   (define c #f)
                   (+ a b) ))



; TODO: define an anon, then call it >> this does not seem to require a closure

