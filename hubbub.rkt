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

(define (check-function id env)
  (if
   (interpret env (list 'procedure? id)) (void)
   (report-error 'not-a-function id)
   )
  )

(define (check-unbound-name id env)
  (if
   (hash-has-key? env id) (void)
   (report-error 'unbound-name id)
   )
  )

(define (check-invalid-contract id env)
  (check-unbound-name id env)
  (if
   (interpret env (list 'procedure? id)) (void)
   (report-error 'invalid-contract id)
   )
  (let* ([f-closure (hash-ref env id)]
         [contract (closure-contract f-closure)]
         [params (closure-params f-closure)])
    (match contract
      [(list con-expr-for-params ... '-> con-expr-for-return)
       (if (equal? (length params) (length con-expr-for-params)) (void)
           (report-error 'invalid-contract id))
       ]
      [else void]
      )
    )
  )

(define (check-contract-violation id args env)
  (let* ([f-closure (hash-ref env id)]
         [contract (closure-contract f-closure)])
    (match contract
      [(list con-expr-for-args ... '-> con-expr-for-result) (and (is-args-good con-expr-for-args args) (is-result-good))]
      [else void])
    )
  )

; we assume at this point that the contract is valid, so that the number of con-exprs is equal to that of args
(define (is-args-good con-exprs args)
  (let* ([update-contracts-violated-list
          (lambda (contract contracts-violated-list)
            (let ([arg (list-ref args (index-of con-exprs contract))])
              (match contract
               ['any contracts-violated-list]
               [else (if (is-arg-satisfy-contract contract arg) (contracts-violated-list) (append contracts-violated-list (list contract))     )])
              )
             )]
          [contracts-violated-list  (foldl update-contracts-violated-list (list) con-exprs)])
    (empty? contracts-violated-list))
  )

(define (is-arg-satisfy-contract contract arg)
  (interpret (hash) (list contract arg))
  )

(define (is-result-good)
  void
  )


#|
(run-interpreter prog) -> any
  prog: datum?
    A syntactically-valid Hubbub program.

  Evaluates the Hubbub program and returns its value, or raises an error if the program is
  not semantically valid.
|#
(define (run-interpreter prog)
  (match prog
    [(list bindings-or-contracts ... expr) (interpret (build-env bindings-or-contracts) expr)]
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
    [(? symbol?)
     (check-unbound-name expr env)
     (hash-ref env expr)] ; handle variable
    [(list '+ addands ...) ; handle builtin functions
     (let ([interpret-with-env (lambda (num) (interpret env num))])
       (apply + (map interpret-with-env addands))
       )
     ] 
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
       [(? symbol?)
        (check-unbound-name possible-procedure env)
        (closure? (hash-ref env possible-procedure))] ; identifier refers to a closure in env; TODO: consider case where possible-procedure isn't even defined
       )]
    ; handle lambda def, return closure
    [(list 'lambda params expr)
     (check-duplicate-param params) (closure params expr env void)]
    ; handle function call
    [(list ID args ...)
     (let* ([interpret-with-env (lambda (arg) (interpret env arg))]
            [evaluated-args (map interpret-with-env args)])
       ; checks
       ;(if (symbol? ID) (check-unbound-name ID env) void)
       ;(check-function ID env)
       ;(check-contract-violation ID args env)
       ; finally we can start interpreting
       (interpret (hash 'args evaluated-args) (interpret env ID))
       ;(interpret env ID)
       ) ; n-ary call; all we do is get the closure, then ask the interpreter to interpret the closure
       
     ]
    ; handle closure
    [(? closure?) (interpret (add-params-mapping (closure-env expr) (closure-params expr) (hash-ref env 'args))  (closure-body expr))] ; our env contains the args; we can use add-params-mapping to construt new env to eval our body
    ;[(? closure?) (add-params-mapping (closure-env expr) (closure-params expr) (hash-ref env 'args))]
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
(struct closure (params body env contract))

; environment builders
(define (build-env bindings-or-contracts) 
  (foldl update_env (hash) bindings-or-contracts))

(define (update_env binding-or-contract env)
  (match binding-or-contract
    [(list 'define ID b) ; case binding 
     (check-duplicate-define ID env)
     (match b 
       [(? symbol?) (hash-set env ID (hash-ref env b))] ; variable define b = a
       [else (hash-set env ID (interpret env b))] ; want ID to val binding, not ID to expr
       )
     ]
    [(list 'define-contract ID contract)
     (check-invalid-contract ID env)
     (let* ([orig-closure (hash-ref env ID)] 
            [params (closure-params orig-closure)]
            [body (closure-body orig-closure)]
            [env (closure-env orig-closure)]
            [new-closure (closure params body env contract)])
       (hash-set env ID new-closure) 
       )

     ] ; case contract
    )
  )

(define (add-params-mapping env params args)
  (if (equal? (length params) (length args)) 
      (let
          ([update-params-mapping (lambda(param params-mapping) (hash-set params-mapping param (list-ref args (index-of params param)) ) )])
        (foldl update-params-mapping env params)
        )
      (report-error 'arity-mismatch (length args) (length params))
      )
  )


;(add-params-mapping (build-env '((define a 4) (define b 4))) (list) (list))

#;(run-interpreter '((define a (+ 4 4))
                   (define b 4)
                   (define c #f)
                   (+ a b) ))



; TODO: builtin shadowing
; TODO: finish contract stuff
; TODO: fix hash table stuff for args >> functions 


                 (run-interpreter `((define a 10) (define b 16) (define g1 (lambda (x1) (+ 1 x1))) (define g2 (lambda (x2) (+ 2 x2))) ((lambda (f1 f2 x1 x2) (+ (f1 x1) (f2 x2))) g1 g2 1 1)))
