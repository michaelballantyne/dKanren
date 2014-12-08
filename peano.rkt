#lang racket

;(require "mk.rkt")
(require "fairconj.rkt")

(define (peano x)
  (conde
    [(== x '0)]
    [(fresh (y)
       (peano y)
       (== x `(succ ,y)))]))

(define (nums x v)
  (conde
    [(== x v)]
    [(nums x (+ 1 v))]))

(map (lambda (triple) (apply max triple)) (run 100 (a c) (nums a 0) (nums c 0)))


;(pretty-print (run 10 (a b c) (peano a) (peano b)))

