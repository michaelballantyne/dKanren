#lang racket

(require "fairconj.rkt")

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (error 'test-check
                    "Failed: ~a~%Expected: ~a~%Computed: ~a"
                    'tested-expression expected produced)))))))

(define max-ticks 1000)

(define succeed
  (== 'a 'a))

(define fail
  (== 'a 'b))

(define-syntax (allw stx)
  (syntax-case stx ()
    [(_ g g* ...)
     #'(fresh ()
         g g* ...)]))

(define-syntax (anyw stx)
  (syntax-case stx ()
    [(_ g g* ...)
     #'(conde
         [g]
         [g*]
         ...)]))

(define-syntax (all stx)
  (syntax-case stx ()
    [(_ g g* ...)
     #'(fresh ()
         g g* ...)]))

(define-syntax (any stx)
  (syntax-case stx ()
    [(_ g g* ...)
     #'(conde
         [g]
         [g*]
         ...)]))

(define
  (any* g)
    (anyw g (any* g)))

(define always (any* succeed))
(define never (any* fail))


;; ----------------------------------------------------------------------------


(define nullo
  (lambda (x)
    (== '() x)))

(define caro
  (lambda (ls a)
    (fresh (d)
      (== (cons a d) ls))))

(define cdro
  (lambda (ls d)
    (fresh (a)
      (== (cons a d) ls))))

(define conso
  (lambda (a d ls)
    (== (cons a d) ls)))

(define (appendw l1 l2 out)
    (anyw
      (allw (nullo l1) (== l2 out))
      (fresh (a d res)
        (allw
          (allw
            (conso a d l1)
            (conso a res out))
          (appendw d l2 res)))))

(define (appendo l1 l2 out)
    (any
      (all (nullo l1) (== l2 out))
      (fresh (a d res)
        (all
          (all
            (conso a d l1)
            (conso a res out))
          (appendo d l2 res)))))

(define (swappendw l1 l2 out)
    (anyw
      (fresh (a d res)
        (allw
          (allw
            (conso a d l1)
            (conso a res out))
          (swappendw d l2 res)))
      (allw (nullo l1) (== l2 out))))



(define (baz x)
    (anyw
      (== 5 x)
      (baz x)))

(define (bat x)
    (anyw
      (bat x)
      (== 5 x)))


(define (quuux x)
    (allw
      (quuux x)
      (allw
        (quuux x)
        (== 5 x))))

(define (blat x)
    (allw
      (allw
        (blat x)
        (blat x))
      (== 5 x)))

(define (blaz x)
    (anyw
      (== 5 x)
      (anyw
        (blaz x)
        (blaz x))))

(define (flaz x)
    (anyw
      (flaz x)
      (anyw
        (flaz x)
        (== 5 x))))

(define (glaz x)
    (anyw
      (anyw
        (glaz x)
        (glaz x))
      (== 5 x)))



;;; anyw/allw tests

(test-check "fairconj1"
  (run* (q) never (== 5 6) never)
  '())

(test-check "fairconj2"
  (run* (q) always (== 5 6) always)
  '())


(test-check "fairconj3"
            (run* (q) (fresh () (fresh () fail) always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        ))
            '())

(test-check "fairconj4"
            (run* (q) (fresh () fail always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        always always always always
                        ))
            '())

(test-check "allw-2"
  (run* (q) (allw fail always))
  '())

(test-check "allw-3"
  (run* (q) (allw (== q 3) (== q 3)))
  '(3))

(test-check "allw-4"
  (run* (q) (allw (== q 3) (== q 4)))
  '())


(test-check "anyw-1"
  (run 1 (q) (anyw never succeed))
  '(_.0))

(test-check "anyw-2"
  (run 1 (q) (anyw succeed never))
  '(_.0))


(test-check "appendw-1"
  (run* (q)
    (appendw '(a b c) '(d e) q))
  '((a b c d e)))


(test-check "swappendw-1"
  (run* (q)
    (swappendw '(a b c) '(d e) q))
  '((a b c d e)))


(test-check "baz-1"
  (run 1 (q)
    (baz q))
  '(5))

(test-check "bat-1"
  (run 1 (q)
    (bat q))
  '(5))

(test-check "blaz-1"
  (run 1 (q)
    (blaz q))
  '(5))

(test-check "blaz-2"
  (run 5 (q)
    (blaz q))
  '(5 5 5 5 5))


(test-check "glaz-1"
  (run 1 (q)
    (glaz q))
  '(5))

(test-check "glaz-2"
  (run 5 (q)
    (glaz q))
  '(5 5 5 5 5))


(test-check "flaz-1"
  (run 1 (q)
    (flaz q))
  '(5))

(test-check "flaz-2"
  (run 5 (q)
    (flaz q))
  '(5 5 5 5 5))


(test-check "appendw-1"
  (run 5 (x)
    (fresh (y z)
      (appendw x y z)))
  '(()
    (_.0)
    (_.0 _.1)
    (_.0 _.1 _.2)
    (_.0 _.1 _.2 _.3)))


(test-check "appendw-2"
  (run 5 (q)
    (fresh (x y z)
      (allw
        (appendw x y z)
        (== `(,x ,y ,z) q))))
  '((() _.0 _.0)
    ((_.0) _.1 (_.0 . _.1))
    ((_.0 _.1) _.2 (_.0 _.1 . _.2))
    ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
    ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))))



(test-check "swappendw-1"
  (run 5 (x)
    (fresh (y z)
      (swappendw x y z)))
  '(()
    (_.0)
    (_.0 _.1)
    (_.0 _.1 _.2)
    (_.0 _.1 _.2 _.3)))

;;; Might give answers back in a different order.
(test-check "swappendw-2"
  (run 5 (q)
    (fresh (x y z)
      (allw
        (swappendw x y z)
        (== `(,x ,y ,z) q))))
  '((() _.0 _.0)
    ((_.0) _.1 (_.0 . _.1))
    ((_.0 _.1) _.2 (_.0 _.1 . _.2))
    ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
    ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))))


;;; Tests adapted from and inspired from 'mktests.scm'

(test-check "testc11.tex-1"
  (run* (q)
    fail)
  `())

(test-check "testc11.tex-2"
  (run* (r)
    (== #t r))
  `(#t))

(test-check "testc11.tex-3"
  (run* (q)
    (all
      fail
      (== #t q)))
  `())

(test-check "testc11.tex-3b"
  (run* (q)
    (allw
      fail
      (== #t q)))
  `())

(define g fail)

(test-check "testc11.tex-4"
  (run* (q) (all g (== #t q)))
  `())

(test-check "testc11.tex-4b"
  (run* (q) (allw g (== #t q)))
  `())

(test-check "testc11.tex-5"
  (run* (q)
    (all
     succeed
     (== #t q)))
  (list #t))

(test-check "testc11.tex-5b"
  (run* (q)
    (allw
      succeed
      (== #t q)))
  (list #t))

(test-check "testc11.tex-6"
  (run* (q)
    (all
     succeed
     (== #t q)))
  `(#t))

(test-check "testc11.tex-6b"
  (run* (q)
    (allw
      succeed
      (== #t q)))
  `(#t))

(test-check "testc11.tex-7"
  (run* (q)
    (all
      succeed
      (== #f q)))
  `(#f))

(test-check "testc11.tex-7b"
  (run* (q)
    (allw
      succeed
      (== #f q)))
  `(#f))

(test-check "testc11.tex-8"
  (run* (r)
    (all
      succeed
      (== 23 r)))
  (list 23))

(test-check "testc11.tex-8b"
  (run* (r)
    (allw
      succeed
      (== 23 r)))
  (list 23))



(test-check "testc11.tex-9"
  (run* (r)
    (all
      succeed
      (== 23 r)))
  `(23))

(test-check "testc11.tex-9b"
  (run* (r)
    (allw
      succeed
      (== 23 r)))
  `(23))


(test-check "testc11.tex-10"
  (run* (r)
    (all
      fail
      (== 23 r)))
  `())

(test-check "testc11.tex-10b"
  (run* (r)
    (allw
      fail
      (== 23 r)))
  `())

(test-check "testc11.tex-11"
  (run* (r)
    (allw
      fail
      (== 23 r)))
  `())

(test-check "testc11.tex-11b"
  (run* (r)
    (allw
      fail
      (== 23 r)))
  `())


(test-check "testc11.tex-12b"
  (run* (q)
    (fresh (x)
      (allw
        (== 0 x)
        (== #t q))))
  (list #t))


(test-check "testc11.tex-13"
  (run* (q)
    (fresh (x)
      (allw
        (== x 0)
        (== #t q))))
  (list #t))

(test-check "testc11.tex-14"
  (run* (q)
    (fresh (x)
      (allw
        (== x 0)
        (== q #t))))
  (list #t))

(test-check "testc11.tex-17"
  (run* (x)
    succeed)
  (list `_.0))

(test-check "testc11.tex-18"
  (run* (x)
    succeed)
  `(_.0))

(test-check "testc11.tex-19"
  (run* (r)
    (fresh (x y)
      (== (cons x (cons y '())) r)))
  (list `(_.0 _.1)))

(test-check "testc11.tex-20"
  (run* (s)
    (fresh (t u)
      (== (cons t (cons u '())) s)))
  (list `(_.0 _.1)))

(test-check "testc11.tex-21"
  (run* (q)
    (fresh (x)
      ((lambda (y)
         (fresh (x)
           (== (cons y (cons x (cons y '()))) q)))
       x)))
  (list `(_.0 _.1 _.0)))

(test-check "testc11.tex-22"
  (run* (q)
    (fresh (x)
      ((lambda (y)
         (fresh (x)
           (== (cons x (cons y (cons x '()))) q)))
       x)))
  (list `(_.0 _.1 _.0)))

(test-check "testc11.tex-25"
  (run* (x)
    (allw
      (== 15 x)
      (== 20 x)))
  `())

(test-check "testc11.tex-26"
  (run* (x)
    (allw
      (== 15 x)
      (== 15 x)))
  (list 15))

(test-check "testc11.tex-28"
  (run* (x)
    (allw
      (== #f x)
      (== #f x)))
  (list #f))

(test-check "testc11.tex-29"
  (run* (x)
    ((lambda (y) (== 5 y))
     x))
  (list 5))

(test-check "testc11.tex-30"
  (run* (y)
    (fresh (x)
      (allw
        (== 5 x)
        (== x y))))
  (list 5))


(test-check "testc11.tex-31"
  (run* (x)
    (fresh (y)
      (== (eq? y x) x)))
  (list #f))


(test-check "testc11.tex-32"
  (run* (x)
    ((lambda (y)
       (fresh (x)
         (== (eq? y x) y)))
     x))
  (list #f))

(test-check "testc11.tex-33"
  (run* (y)
    (fresh (x)
      (allw
        (== y x)
        (== 5 x))))
  (list 5))


(test-check "testc12.tex-1"
  ((lambda (y x) (x y)) 3 (lambda (a) a))
  3)

(test-check "testc12.tex-2"
  (run* (r)
    (fresh (y x)
      (== `(,x ,y) r)))
  (list `(_.0 _.1)))

(test-check "testc12.tex-3"
  (run* (r)
    (fresh (y x)
      (== ((lambda (y x) `(,x ,y)) y x) r)))
  (list `(_.0 _.1)))

(test-check "testc12.tex-8"
  (run* (q)
    (allw
      (caro `(9 6 15 2 7) 9)
      (== #t q)))
  (list #t))


(test-check "testc12.tex-10"
  (run* (r)
    (fresh (x y)
      (allw
        (caro `(,r ,y) x)
        (== 5 x))))
  (list 5))


(test-check "testc12.tex-12"
  (run* (r)
    (fresh (x y)
      (allw
        (caro `(grape raisin prune) x)
        (allw
          (caro `((1) (2) (3)) y)
          (== (cons x y) r)))))
  (list `(grape 1)))

(test-check "testc12.tex-17"
  (run* (r)
    (fresh (x y)
      (allw
        (cdro `(grape raisin prune) x)
        (allw
          (caro `((1) (2) (3)) y)
          (== (cons x y) r)))))
  (list `((raisin prune) 1)))

(test-check "testc12.tex-18"
  (run* (q)
    (allw
      (cdro '(9 6 15 2 7) '(6 15 2 7))
      (== #t q)))
  (list #t))

(test-check "testc12.tex-20"
  (run* (x)
    (cdro '(6 15 2 7) `(,x 2 7)))
  (list 15))

(test-check "testc12.tex-22"
  (run* (ls)
    (fresh (x)
      (allw
        (cdro ls '(1 2 3))
        (allw
          (caro ls x)
          (== 0 x)))))
  (list `(0 1 2 3)))

(define rice
  (lambda (ls2)
    (run* (ls)
      (fresh (d x y)
        (allw
          (allw
            (cdro ls ls2)
            (allw
              (caro ls x)
              (== 5 x)))
          (allw
            (cdro ls d)
            (allw
              (caro d y)
              (== 2 y))))))))

(test-check "testc12.tex-23"
  (run* (r)
    (fresh (w)
      (== (car (rice `(,w 3))) r)))
  (list `(5 2 3)))

(test-check "testc12.tex-24"
  (run* (ls)
    (conso '(1 2 3) '(4 5) ls))
  (list `((1 2 3) 4 5)))

(test-check "testc12.tex-25"
  (run* (x)
    (conso x '(1 2 3) '(4 1 2 3)))
  (list 4))

(test-check "testc12.tex-27"
  (run* (r)
    (fresh (w x y z)
      (allw
        (== `(5 1 4 ,w) r)
        (conso x `(1 ,y 3) r))))
  (list `(5 1 4 3)))

(test-check "testc12.tex-28"
  (run* (x)
    (conso x `(1 ,x 3) `(4 1 ,x 3)))
  (list 4))

(define x 4)


(test-check "testc12.tex-30"
  (run* (ls)
    (fresh (x)
      (allw
        (== `(4 1 ,x 3) ls)
        (conso x `(1 ,x 3) ls))))
  (list `(4 1 4 3)))

(test-check "testc12.tex-31"
  (run* (ls)
    (fresh (x)
      (allw
        (conso x `(1 ,x 3) ls)
        (== `(4 1 ,x 3) ls))))
  (list `(4 1 4 3)))

(test-check "testc12.tex-34"
  (run* (q)
    (allw
      (nullo `(grape raisin prune))
      (== #t q)))
  `())

(test-check "testc12.tex-35"
  (run* (q)
    (allw
      (nullo '())
      (== #t q)))
  `(#t))

(test-check "testc12.tex-36"
  (run* (x)
    (nullo x))
  `(()))

(define eqo
  (lambda (x y)
    (== x y)))

(test-check "testc12.tex-39"
  (run* (q)
    (allw
      (eqo 'prune 'plum)
      (== #t q)))
  `())

(test-check "testc12.tex-40"
  (run* (q)
    (allw
      (eqo 'plum 'plum)
      (== #t q)))
  `(#t))

(test-check "testc12.tex-44"
  (run* (r)
    (fresh (x y)
      (== (cons x (cons y 'salad)) r)))
  (list `(_.0 _.1 . salad)))

(define pairo
  (lambda (ls)
    (fresh (a d)
      (conso a d ls))))

(test-check "testc12.tex-45"
  (run* (q)
    (allw
      (pairo (cons 1 2))
      (== #t q)))
  `(#t))

(test-check "testc12.tex-46"
  (run* (q)
    (allw
      (pairo '())
      (== #t q)))
  `())

(test-check "testc12.tex-47"
  (run* (q)
    (allw
      (pairo 5)
      (== #t q)))
`())

(test-check "testc12.tex-48"
  (run* (x)
    (pairo x))
  (list `(_.0 . _.1)))

(test-check "testc12.tex-49"
  (run* (r)
    (pairo (cons r 3)))
  (list `_.0))







(test-check "testc13.tex-fail1"
  (run* (q)
    (anyw
      (allw fail succeed)
       fail))
  '())


(test-check "testc13.tex-succeed1"
  (not
    (null?
      (run* (q)
        (anyw
          (allw fail fail)
          succeed))))
  #t)


(test-check "testc13.tex-succeed2"
  (not
    (null?
      (run* (q)
        (anyw
          (allw succeed succeed)
          fail))))
  #t)


(test-check "testc13.tex-4"
  (run* (x)
    (anyw
      (allw (== 15 x) succeed)
      (anyw
        (allw (== 20 x) succeed)
        fail)))
  `(15 20))

(test-check "testc13.tex-5"
  (run 1 (x)
    (anyw
      (allw (== 15 x) succeed)
      (anyw
        (allw (== 20 x) succeed)
        fail)))
  `(15))

(test-check "testc13.tex-7"
  (run* (x)
    (anyw
      (anyw
        (allw (== 10 x) fail)
        (allw (== 15 x) succeed))
      (anyw
        (allw (== 20 x) succeed)
        fail)))
  `(15 20))

(test-check "testc13.tex-conde1"
  (run* (x)
    (anyw
      (allw (== 15 x) succeed)
      (anyw
        (allw (== 20 x) succeed)
        fail)))
  `(15 20))

(test-check "testc13.tex-10"
  (run* (q)
    (fresh (x y)
      (allw
        (allw
          (== x y)
          (== 5 x))
        (allw
          (== 17 y)
          (== #t q)))))
  `())

(test-check "testc13.tex-11"
  (run* (q)
    (allw
      (fresh (x y)
        (allw
          (== x y)
          (allw
            (== 5 x)
            (== 5 y))))
      (== #t q)))
  (list #t))

(define
  (any*2 g)
    (anyw
      (allw g succeed)
      (any*2 g)))

(define never2 (any*2 fail))

(define always2 (any*2 succeed))

(test-check "testc13.tex-15"
  (run 1 (q)
    (allw
      always2
      (== #t q)))
  (list #t))

(test-check "testc13.tex-17"
  (run 5 (q)
    (allw
      always2
      (== #t q)))
  `(#t #t #t #t #t))

(test-check "testc13.tex-18"
  (run 1 (q)
    (allw
      (anyw
        (allw succeed succeed)
        always2)
      (== #t q)))
  `(#t))

(define salo
  (lambda (g)
    (anyw
      (allw succeed succeed)
      g)))

(define salo2
  (lambda (g)
    (anyw
      succeed
      g)))


(test-check "testc13.tex-19"
  (run 1 (q)
    (allw
      (salo always2)
      (== #t q)))
  `(#t))

(test-check "testc13.tex-20"
  (run 1 (q)
    (allw
      (salo never2)
      (== #t q)))
  `(#t))

(test-check "testc13.tex-23"
  (run* (q)
    (allw
      (salo never2)
      (allw
        fail
        (== #t q))))
  `())

(test-check "testc13.tex-24"
  (run* (q)
    (allw
      (allw
        always2
        fail)
      (== #t q)))
  `())

(test-check "testc13.tex-26"
  (run 1 (q)
    (allw
      (allw
        (anyw always2 succeed)
        (anyw fail))
      (anyw
        fail
        (== #t q))))
  `())



(test-check "testc13.tex-28"
  (run* (q)
    (allw
      (anyw
        (allw always2 succeed)
        (allw fail))
      (allw
        fail
        (== #t q))))
  `())


(define ten-or-twenty
  (lambda (x)
    (anyw
      (anyw
        (allw (== 10 x) succeed)
        (allw (== 20 x) succeed))
      fail)))

(test-check "testc13.tex-30"
  (run* (x)
    (ten-or-twenty x))
  `(10 20))

(test-check "testc13.tex-27"
  (run 10 (q)
    (allw
      (anyw
        (allw (== 15 q) always2)
        (allw (any*2 (== 20 q))))
      (== 20 q)))
  '(20 20 20 20 20 20 20 20 20 20))


(test-check "testc13.tex-40"
  (run 1 (q)
    (allw
      (anyw
        (allw (== 15 q) always2)
        (== 20 q))
      (== 20 q)))
  `(20))


(test-check "testc13.tex-41a"
  (run* (q)
    (allw
      (== 20 q)
      (anyw
        (allw (== 15 q) always2)
        (== 20 q))))
  `(20))

(test-check "testc13.tex-41b"
  (run* (q)
    (allw
      (anyw
        (allw (== 15 q) always2)
        (== 20 q))
      (== 20 q)))
  `(20))

