#lang racket

(require (prefix-in q: pfds/queue/implicit))
(require (only-in "current-micro.rkt" unify))
(require profile)

(define (enqueue-all queue l)
  (if (null? l)
    queue
    (enqueue-all (q:enqueue (car l) queue) (cdr l))))

(struct substitution (alist) #:transparent)

(define (empty-s)
  '())

(struct state (unreduced reduced) #:transparent)
(struct conj (substitution children) #:transparent)
(struct disj (children) #:transparent)
(struct unification (left right) #:transparent)

; TODO: Use list-no-order for all clauses and combine the two clauses for disj
(define (reduce-disjunct substitution children)
  (match children
    ; Apply a unification
    [(list-no-order (unification left right) other-children ...)
     (let ([new-substitution (unify left right substitution)])
       (cond
         [(not new-substitution) (values #f '())]
         [(null? other-children) (values new-substitution '())]
         [else (values #f (list (conj new-substitution other-children)))]))]
    ; Lift branches of any nested conjunct
    [(list-no-order (conj #f nested-children) other-children ...)
     (values #f (list (conj substitution (append other-children
                                                 nested-children))))]
    ; If we have a disjunction, distribute the remaining children into it. They won't
    ; be unifications or conjunctions because of the previous cases.
    [(list-no-order (disj disj-children) other-children ...)
     (values #f (map (match-lambda
                       [(conj #f nested-children)
                        (conj substitution (append other-children
                                                   nested-children))])
                     disj-children))]))

(define (step-state current-state)
  (match-define
    (state unreduced-q reduced-q) current-state)
  (cond
    ; There's nothing left. Fail.
    [(and (q:empty? unreduced-q) (q:empty? reduced-q))
     (values #f #f)]
    ; We've reduced everything. Expand a proc.
    [(q:empty? unreduced-q)
     (define expanded-disjunct
       (match (q:head reduced-q)
         [(conj substitution (cons proc other-procs))
          (conj substitution (cons (proc) other-procs))]))
     (values #f (state (q:enqueue expanded-disjunct unreduced-q)
                       (q:tail reduced-q)))]
    ; Else, look at the first element in the unreduced-q
    [else
      (match (q:head unreduced-q)
        ; The element is fully reduced.
        [(conj substitution (list (? procedure?) ...))
        (values #f (state (q:tail unreduced-q)
                          (q:enqueue (q:head unreduced-q) reduced-q)))]
        ; The element needs reducing.
        [(conj substitution children)
         (define-values (result new-disjuncts)
           (reduce-disjunct substitution children))
         (values result (state (enqueue-all (q:tail unreduced-q) new-disjuncts)
                               reduced-q))])]))

(define (inject tree)
  (state (q:queue (conj (empty-s) (list tree))) (q:queue)))

(define (show-step-internal n q [r '()])
  (if (> n 0)
    (let-values ([(result new-tree) (step-state q)])
      (show-step-internal (- n 1) new-tree (cons result r)))
    'a))

(define (show-step n tree)
  (show-step-internal n (state (q:queue (conj (empty-s) (list tree))) (q:queue))))

(define (run-internal n state results)
  (if (and state (> n 0))
    (let-values ([(result new-state) (step-state state)])
      (if result
        (run-internal (- n 1) new-state (cons result results))
        (run-internal n new-state results)))
    'a))

(define (run n tree)
  (run-internal n (state (q:queue (conj (empty-s) (list tree))) (q:queue)) '()))

(run 1 (unification 'a 'b))

(run 1 (unification 'a 'a))

(run 2 (conj #f (list (unification 1 'a)
                      (disj (list (conj #f (list (unification 2 'a)))
                                  (conj #f (list (unification 2 'b))))))))

(define (p1)
  (conj #f  (list (disj (list (conj #f (list (unification 'a 'a)))
                              (conj #f (list p1))))
                  (unification 2 'a))))

(define (p2)
  (conj #f  (list (disj (list (conj #f (list (unification 'a 'a)))
                              (conj #f (list p2))))
                  (unification 2 'b))))

(profile
  (run 1000 (conj #f (list p1 p1))))


#|

(show-step 2 (q:queue (conj (empty-s) (list (unification 'a 'b)))))

(show-step 1 (q:queue (conj
                          (substitution '((b b)))
                          (list
                            (disj
                              (list
                                (conj #f (list (unification 'c 'c)))
                                (conj #f (list (unification 'd 'd)))))))
                        (conj (substitution '((a a))) (list (conj #f (list (unification 'c 'c)))))
                        (conj (substitution '((a a))) (list (conj #f (list (unification 'd 'd)))))))

(show-step 10
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

(show-step 2
  (q:queue (conj (empty-s)
                 (list
                   (disj (list (conj #f (list (unification 'a 'b)))
                               (conj #f (list (unification 'a 'c)))))
                   (unification 'c 'd)))))

(show-step 2
  (q:queue (conj (empty-s)
                 (list
                   (unification 'c 'd)
                   (unification 'a 'b)))))


(show-step 3
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
                   (disj (list (conj #f (list (unification 'a 'b)))
                               (conj #f (list (unification 'a 'c)))))))))
|#
