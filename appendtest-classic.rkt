#lang racket


(require "mk.rkt")

(define (appendo l s out)
  (conde
    [(== '() l) (== s out)]
    [(fresh (a d res)
       (== `(,a . ,d) l)
       (== `(,a . ,res) out)
       (appendo d s res))]))

(time (length (run* (q) (fresh (x y) (appendo x y (make-list 1500 1)) (== (list x y) q)))))

