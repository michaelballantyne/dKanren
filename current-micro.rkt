#lang racket
(provide == call/fresh conj disj define-goal-constructor call/initial-state ifte once unify)
;; just some racketry.
;; In general, comments are below their corresponding definitions.
(define (var n) n)
(define (var? n) (number? n))
;; de gustibus non est disputandum
(define (walk u s)
  (let ((pr (assv u s)))
    (if pr (walk (cdr pr) s) u)))
;; either it in there, or it aint
(define (ext-s x u s)
  (cond
    ((occurs? x u s) #f)
    (else `((,x . ,u) . ,s))))
;; A lean, mean, extending machine.
(define occurs?
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eqv? x v))
        ((pair? v) (or (occurs? x (car v) s)
                       (occurs? x (cdr v) s)))
        (else #f)))))
;; unify all the things
(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((eqv? u v) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else #f))))
;; even I couldn't countenance inlining the else into an and
(define (== u v)
  (lambda (s/c)
    (let ((s (unify u v (car s/c))))
      (if s (list (cons s (cdr s/c))) `()))))
;; list is short for return
(define (call/fresh f)
  (lambda (s/c)
    (let ((c (cdr s/c)))
      ((f (var c)) `(,(car s/c) . ,(+ 1 c))))))
;; of course, we could just inline number? for var?, and get rid of
;; all (var ...)
(define (disj g1 g2) (lambda (s/c) ($append (g1 s/c) (g2 s/c))))
(define (conj g1 g2) (lambda (s/c) ($append-map g2 (g1 s/c))))
;; obviously non-tail calls. You see the recursion down the tree, and then back up.
(define ($append $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (lambda () ($append $2 ($1))))
    (else (cons (car $1) ($append (cdr $1) $2)))))
(define ($append-map g $)
  (cond
    ((null? $) `())
    ((procedure? $) (lambda () ($append-map g ($))))
    (else ($append (g (car $)) ($append-map g (cdr $))))))
;; I actually don't know which order for these is best.
;; From what I know now, seems like the pair should come first,
;; though.
(define-syntax lambdad
  (syntax-rules ()
    ((_ fs ge) (lambda fs (lambda (s/c) (lambda () (ge s/c)))))))
(define-syntax define-goal-constructor
  (syntax-rules ()
    ((_ (name . fs) ge)
     (define name (lambdad fs ge)))))
;; Congratulations. We just solved the (improperly-named) fresh ()
;; problem.
;; You couldn't more obviously bring recursive defns into the termination monad.
(define (pull $) (if (procedure? $) (pull ($)) $))
(define (call/initial-state g) (pull (g '(() . 0))))
;; Notice, now, we combined runs of the state, a sort-of
;; nondeterminism, and termination monads here.
;; All consructions of variables take place under the monad. If you
;; want to reify, do it as you ext-s, and keep it under the run.
(define (ifte g0 g1 g2)
  (lambda (s/c)
    (let loop (($ (g0 s/c)))
      (cond
        ((procedure? $) (lambda () (loop ($))))
        ((null? $) (g2 s/c))
        (else ($append-map g1 $))))))
(define (once g)
  (lambda (s/c)
    (let loop (($ (g s/c)))
      (cond
        ((procedure? $) (lambda () (loop ($))))
        ((null? $) `())
        (else (list (car $)))))))
;; Yeah, yeah. Sure. I guess these go in too.
;; I'm giving an askance look to (list (car $)) atm.
;(define-goal-constructor (appendo l s out)
;  (disj
;   (conj (== '() l) (== s out))
;   (call/fresh
;    (lambda (a)
;      (call/fresh
;       (lambda (d)
;         (conj
;          (== `(,a . ,d) l)
;          (call/fresh
;           (lambda (res)
;             (conj
;              (== `(,a . ,res) out)
;              (appendo d s res)))))))))))
;; ;; Ye olde appendo.
;((cdr (call/initial-state
;  (call/fresh
;   (lambda (q)
;     (call/fresh
;      (lambda (l)
;        (call/fresh
;         (lambda (s)
;           (call/fresh
;            (lambda (out)
;              (conj
;               (appendo l s out)
;               (== `(,l ,s ,out) q)))))))))))))
;; ... and the pitch

