#lang racket

(require "project.rkt")

(eval-exp (with "fib" (lam "fib" "x" (ifleq (num 0) (var "x") (plus (apply (var "fib") (minus (var "x") (num 1))) (apply (var "fib") (minus (var "x") (num 2)))) (num 1)))
            (apply (var "fib") (num 3))))


(eval-exp (with "fact" (lam "fact" "x" (ifleq (num 1) (var "x") (mult (apply (var "fact") (minus (var "x") (num 1))) (var "x")) (num 1)))
            (apply (var "fact") (num 5))))