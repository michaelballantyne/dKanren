#lang racket

(require (prefix-in q: pfds/queue/bankers))

(define (enqueue-all queue l)
  (if (null? l)
    queue
    (enqueue-all (q:enqueue (car l) queue) (cdr l))))

(struct substitution (alist) #:transparent)

(define (empty-s)
  (substitution '()))

(define (unify old-substitution left right)
  (substitution (cons (list left right) (substitution-alist old-substitution))))

(struct conj (substitution children) #:transparent)
(struct disj (children) #:transparent)
(struct unification (left right) #:transparent)

(define (step-top-disj queue)
  (match-define
    (conj substitution conjuncts) (q:head queue))

  (define-values (result new-disjuncts)
    (match conjuncts
      ; Handle a unification
      [(list (and other-children-before (not (unification _ _))) ...
             (unification left right)
             other-children-after ...)
       (let ([new-substitution (unify substitution left right)]
             [other-children (append other-children-before other-children-after)])
         (cond
           [(false? new-substitution) (values #f '())]
           [(null? other-children) (values new-substitution '())]
           [else (values #f (list (conj new-substitution other-children)))]))]
      ; Lift branches of (sole) nested disjunct
      [(list (disj disj-children))
       (values #f (map
                     (lambda (c) (conj substitution (list c)))
                     disj-children))]
      ; Lift branches of any nested conjunct
      [(list (conj #f (list nested-children ...)) other-children ...)
       (values #f (list (conj substitution (append other-children nested-children))))]
      ; If we have a disjunction, distribute the next child into it.
      [(list (disj (and disj-children)) next-child other-children ...)
       (values #f
               (list (conj substitution
                           (list (disj
                           (append (map
                                     (match-lambda
                                       [(conj nested-substitution nested-children)
                                        (conj nested-substitution (append nested-children
                                                                          (list next-child)))])
                                     disj-children)
                                   other-children))))))]
      ; If everything left is a procedure, expand the first of them
      [(list (and p (? procedure?)) (and other-children (? procedure?)) ...)
       (values #f (list (conj substitution (append (list (p)) other-children))))]
      ; Or if there's a procedure but also some other stuff, delay the procedure
      [(list (and p (? procedure?)) other-children ...)
       (values #f (list (conj substitution (append other-children (list p)))))]))

  (values result (enqueue-all (q:tail queue) new-disjuncts)))

(define (show-step n q [r '()])
  (if (> n 0)
    (let-values ([(result new-tree) (step-top-disj q)])
      (show-step (- n 1) new-tree (cons result r)))
    (begin  (pretty-print r)
            (pretty-print (q:queue->list q))
            (displayln ""))))

(step-top-disj (q:queue (conj
                          (substitution '((b b)))
                          (list
                            (disj
                              (list
                                (conj #f (list (unification 'c 'c)))
                                (conj #f (list (unification 'd 'd)))))))
                        (conj (substitution '((a a))) (list (conj #f (list (unification 'c 'c)))))
                        (conj (substitution '((a a))) (list (conj #f (list (unification 'd 'd)))))))

(show-step 8
  (q:queue (conj (empty-s)
                 (list
                   (disj
                     (list
                       (conj #f (list (unification 'a 'a)))
                       (conj #f (list (unification 'b 'b)))
                       ))
                   (disj
                     (list
                       (conj #f (list (unification 'c 'c)))
                       (conj #f (list (unification 'd 'd)))
                       ))))))

(show-step 1
  (q:queue (conj (empty-s)
                 (list
                   (disj (list (unification 'a 'b)
                               (unification 'a 'c)))
                   (unification 'c 'd)))))

(show-step 2
  (q:queue (conj (empty-s)
                 (list
                   (unification 'c 'd)
                   (unification 'a 'b)))))


(show-step 1
  (q:queue (conj (empty-s)
                 (list
                   (conj #f
                     (list
                       (unification 'a 'b)
                       (unification 'b 'c)))))))


(show-step 2
  (q:queue (conj (empty-s)
                 (list
                   (unification 'c 'd)
                   (disj (list (unification 'a 'b)
                               (unification 'a 'c)))))))
