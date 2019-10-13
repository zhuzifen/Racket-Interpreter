#lang racket #| ★ CSC324 Fall 2019: Assignment 1 Sample Tests ★ |#
#|
Module: hubbub_test_sample
Description: Sample Tests for Assignment 1
Copyright: (c) University of Toronto
               CSC324 Principles of Programming Languages, Fall 2019

Warning: as usual, these sample tests are very incomplete, and are meant to
give you a sense of the test structure we'll use, but NOT to verify the
complete correctness of your work on this assignment! Please add your own
tests here
|#

(require rackunit)
(require "hubbub.rkt")
(require "hubbub_errors.rkt")


(module+ test
  (test-equal? "Numeric literal"
                 (run-interpreter '(30))
                 30)

  (test-equal? "Multiple independent defines"
                 (run-interpreter '((define a 1)
                                    (define b #t)
                                    (define c #f)
                                    b))
                 #t)

  (test-exn "Identifier with unused define (unbound-name error)"
              (regexp (format (hash-ref error-strings 'unbound-name) 'b))
              (thunk (run-interpreter '((define a 10)
                                        b))))

  (test-equal? "Simple +"
                 (run-interpreter '((+ 30 40)))
                 70)

  (test-equal? "Unary function call"
                 (run-interpreter '(((lambda (x) (+ x 1)) 1)))
                 2)

  (test-equal? "make-adder (like lecture)"
                 (run-interpreter '((define make-adder
                                      (lambda (n)
                                        (lambda (m)
                                          (+ n m))))
                                    (define add-one (make-adder 1))
                                    (define add-two (make-adder 2))
                                    (+ (add-one 5) (add-two 10))))
                 ; We write out explicitly the computation produced using
                 ; correct substitution.
                 (+ (+ 1 5) (+ 2 10)))

  (test-equal? "Contract: (integer? -> boolean?), valid call"
                 (run-interpreter '((define f (lambda (x) (< x 3)))
                                    (define-contract f (integer? -> boolean?))
                                    (f 1)))
                 #t)

  (test-equal? "test #1"
                 (run-interpreter `((define a 10) (define b 16) a))
                 10)

  (test-equal? "test #2"
                 (run-interpreter `((define a 10) (define b 16) (equal? a b)))
                 #f)
  
  (test-equal? "test #3"
                 (run-interpreter `((define a 10) (define b 16) ((lambda () (equal? a b)))))
                 #f)
  
  (test-equal? "test #4"
                 (run-interpreter `((define a 10) (define b 16) ((lambda () (< a b)))))
                 #t)

  (test-equal? "test #5"
                 (run-interpreter `((define a 10) (define b 16) ((lambda () (< b a)))))
                 #f)

  (test-equal? "test #6"
                 (run-interpreter `((define a 10) (define b 16) (define f (lambda () (< a b))) (f)))
                 #t)

  (test-equal? "test #7"
                 (run-interpreter `((define a 10) (define b 16) ((lambda () (< b a)))))
                 #f)

  (test-equal? "test #8"
                 (run-interpreter `((define a 10) (define b 16) ((lambda (x1) (< x1 b)) a)))
                 #t)

  (test-equal? "test #9"
                 (run-interpreter `((define a 10) (define b 16) (define f (lambda (x1) (< x1 b))) (f a)))
                 #t)

  (test-equal? "test #10"
                 (run-interpreter `((define a 10) (define b 16) ((lambda (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)  (+ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) 1 2 3 4 5 6 7 8 9 10)))
                 (+ 1 2 3 4 5 6 7 8 9 10))

  (test-equal? "test #11"
                 (run-interpreter `((define a 10) (define b 16) (define f (lambda (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)  (+ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))) (f 1 2 3 4 5 6 7 8 9 10)))
                 (+ 1 2 3 4 5 6 7 8 9 10))

  (test-equal? "test #12"
                 (run-interpreter `((define a 10) (define b 16) (define g1 (lambda (x1) (+ 1 x1))) (define g2 (lambda (x2) (+ 2 x2))) ((lambda (f1 f2 x1 x2) (+ (f1 x1) (f2 x2))) g1 g2 1 1)))
                 5)

  (test-equal? "test #13"
                 (run-interpreter `((define a 10) (define b 16) (define g1 (lambda (x1) (+ 1 x1))) (define g2 (lambda (x2) (+ 2 x2))) (define f (lambda (f1 f2 x1 x2) (+ (f1 x1) (f2 x2)))) (f g1 g2 1 1)))
                 5)

  (test-equal? "test #14"
                 (run-interpreter `((define a 10) (define b 16) (define f1 (lambda (x1) (+ 1 x1))) (define f2 (lambda (x2) (+ 2 x2))) ((lambda (f1 f2 x1 x2) (+ (f1 x1) (f2 x2))) f1 f2 1 1)))
                 5)

  (test-equal? "test #15"
                 (run-interpreter `((define a 10) (define b 16) (define f1 (lambda (x1) (+ 1 x1))) (define f2 (lambda (x2) (+ 2 x2))) (define f (lambda (f1 f2 x1 x2) (+ (f1 x1) (f2 x2)))) (f f1 f2 1 1)))
                 5)

  (test-equal? "test #16"
                 (run-interpreter `((define a 10) (define b 16) (define f1 (lambda (x1) (+ 1 x1))) (define f2 (lambda (x2) (+ 2 x2))) (((lambda (f1 f2 x1 x2) (lambda (x1) (+ (f1 x2) x1))) f1 f2 27 3) 1)))
                 5)

  (test-equal? "test #17"
                 (run-interpreter `((define a 10) (define b 16) (define f1 (lambda (x1) (+ 1 x1))) (define f2 (lambda (x2) (+ 2 x2))) ((((lambda (x1) (lambda (f1 f2 x x2) (lambda (x2) (+ (f1 x2) x1)))) 5) f1 f2 27 3) 1)))
                 7)

  (test-equal? "test #18"
                 (run-interpreter `((define a 10) (define b 16) (define f1 (lambda (x1) (+ 1 x1))) (define f2 (lambda (x2) (+ 2 x2))) (define f3 (lambda (f1 f2) (lambda (x) (+ (f1 x) (f2 x))))) ((f3 f1 f2) 20)))
                 43)

  (test-equal? "test #19"
                 (run-interpreter `((define a 10) (define b 16) (define f1 (lambda (x1) (+ 1 x1))) (define f2 (lambda (x2) (+ 2 x2))) (define f3 (lambda (f1 f2) (lambda (x) (equal? (f1 0 x) (f2 x))))) ((f3 < integer?) 20)))
                 #t)

  (test-equal? "test #20"
                 (run-interpreter `((define a 10) (define b 16) (define f1 (lambda (x1) (+ 1 x1))) (procedure? < )))
                 #t)

  (test-equal? "test #21"
                 (run-interpreter `((define a 10) (define b 16) (define f1 (lambda (x1) (+ 1 x1))) (procedure? (lambda () 10) )))
                 #t)


  (test-exn "test #e1"
              (regexp (format (hash-ref error-strings 'duplicate-name) 'a))
              (thunk (run-interpreter '((define a 10) (define a 10)
                                        a))))
  (test-exn "test #e2"
              (regexp (format (hash-ref error-strings 'not-a-function) 'a))
              (thunk (run-interpreter '((define a 10)
                                        (a)))))

  (test-exn "test #e3"
              (regexp (format (hash-ref error-strings 'not-a-function) '5))
              (thunk (run-interpreter '((define a 10)
                                        (5)))))

  (test-exn "test #e4"
              (regexp (format (hash-ref error-strings `arity-mismatch) 0 1))
              (thunk (run-interpreter '((define a 10) (define f (lambda (x1) (+ 5 x1)))
                                        (f)))))

  (test-exn "test #e5"
              (regexp (format (hash-ref error-strings 'duplicate-name) 'x))
              (thunk (run-interpreter '((define f (lambda (x x) (< x 0))) (define a 10)
                                        a)))))