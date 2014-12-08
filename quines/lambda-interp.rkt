#lang racket

;(require "../mk.rkt")
(require "../fairconj.rkt")

(define (noo u v) (absento u v))

(define eval-expo
  (lambda (exp env val)
    (conde
      ((numbero exp) (== exp val))
      ((symbolo exp) (lookupo exp env val))
      ((fresh (rator rand x body env^ a)
         (== `(,rator ,rand) exp)
         (noo 'quote rator)
         (noo 'list rator)
         (eval-expo rator env `(closure ,x ,body ,env^))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env^) val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (== `(closure ,x ,body ,env) val)
         (symbolo x)
         )))))

(define lookupo
  (lambda (x env t)
    (fresh (rest y v)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (lookupo x rest t))))))

; This takes 82 seconds, whereas it comes back instantly in normal mk
(run 1 (q)
     (eval-expo `((((lambda (x) (lambda (y) (lambda (z) ((x z) (y z))))) (lambda (x) (lambda (y) (x y)))) (lambda (y) y)) (lambda (x) 5)) '() 5))

;(run 1 (q)
;     (eval-expo `(((,q (lambda (x) (lambda (y) y))) (lambda (y) y)) 'z) '() 'z)
;     (== q '(lambda (x) (lambda (y) (lambda (z) ((x z) (y z)))))))

;(time (run 1 (q) (eval-expo q '() q)))

;(time (length (run 3 (q) (eval-expo q '() '(I love you)))))
;(time (run 1 (q r v x y z) (== q `((lambda (,x) (,y ,z ,v)) ,r)) (eval-expo q '() q)))

;(run 1 (v q) (== q `(,v '(lambda (_.0) (list _.0 (list 'quote _.0))))) (evalo q q))

;(time (length (run 6 (q) (eval-expo q '() '(I love you)))))

;(time (run* (q) (== q '((lambda (_.0) '(I love you)) (lambda (_.1) _.2))) (eval-expo q '() '(I love you))))

#|
'('(I love you)
  (((lambda (_.0) _.0) '(I love you)) (=/= ((_.0 in))) (sym _.0))
  (((lambda (_.0) '(I love you)) '_.1) (=/= ((_.0 quote))) (absento (in _.0) (in _.1)))
  (((lambda (_.0) '(I love you)) (lambda (_.1) _.2)) (=/= ((_.0 quote))) (absento (in _.0) (in _.1) (in _.2)))
  (((lambda (_.0) '(I love you)) (list)) (=/= ((_.0 quote))) (absento (in _.0)))
  (list 'I 'love 'you))
|#
