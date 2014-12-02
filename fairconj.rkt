#lang racket

(require (prefix-in topq: pfds/queue/real-time))
(require (prefix-in disjq: pfds/queue/real-time))
(require (only-in "mk.rkt" unify var reify))

(provide == run run* fresh conde)

(define (empty-s)
  '())

(struct conj (substitution unsorted disjunctions) #:transparent)
(struct disj (children) #:transparent)
(struct unification (left right) #:transparent)
(struct state (unreduced reduced) #:transparent)

(define (reduce-conj substitution unsorted disjunctions)
  (if (null? unsorted)
    (values substitution disjunctions)
    (match (first unsorted)
      [(unification term1 term2)
       (let ([new-substitution (unify term1 term2 substitution)])
         (cond
           [(not new-substitution)
            (values #f #f)]
           [(null? (rest unsorted))
            (values new-substitution disjunctions)]
           [else (reduce-conj new-substitution (rest unsorted) disjunctions)]))]
      [(conj #f nested-unsorted #f)
       (let-values ([(new-substitution new-disjunctions)
                     (reduce-conj substitution nested-unsorted disjunctions)])
         (if new-substitution
           (reduce-conj new-substitution (rest unsorted) new-disjunctions)
           (values #f #f)))]
      ; Only disjunctions are inverse-eta delayed, so evaluate the procedure
      ; and enqueue the resulting disjunction.
      [(and p (? procedure?))
       (reduce-conj substitution
                    (rest unsorted)
                    (and disjunctions
                         (disjq:enqueue
                           (p)
                           disjunctions)))]
      )))

(define (distribute into-disjunction other-disjunctions substitution)
  (map
    (match-lambda
      [(conj #f nested-unsorted #f)
       (conj substitution nested-unsorted other-disjunctions)])
    (disj-children into-disjunction)))

(define (filter-branches disjunction substitution)
  (define new-children
    (filter-map
      (match-lambda
        [(conj #f children #f)
         (define-values (new-substitution new-disjunctions)
           (reduce-conj substitution children #f))
         (and new-substitution
              (conj #f children #f))])
      (disj-children disjunction)))
  (and (pair? new-children) (disj new-children)))

(define (filter-disjunctions remaining substitution acc)
  (if (disjq:empty? remaining)
    acc
    (let ([filtered (filter-branches (disjq:head remaining)
                                     substitution)])
      (and
        filtered
        (filter-disjunctions (disjq:tail remaining)
                             substitution
                             (disjq:enqueue filtered acc))))))

(define (step-state current-state)
  (match-define (state unreduced reduced) current-state)
  (if (pair? unreduced)
    (match-let ([(conj substitution unsorted disjunctions)
                 (first unreduced)])
      (define-values (new-substitution new-disjunctions)
        (reduce-conj substitution unsorted (disjq:queue)))
      (define filtered-disjunctions
        (and new-disjunctions
             (filter-disjunctions new-disjunctions new-substitution disjunctions)))
      (cond
        [(not filtered-disjunctions)
         (values #f (state (rest unreduced) reduced))]
        [(disjq:empty? filtered-disjunctions)
         (values new-substitution (state (rest unreduced) reduced))]
        [else
         (values #f
                 (state (rest unreduced)
                        (topq:enqueue (conj new-substitution '() filtered-disjunctions)
                                      reduced)))]))
    (match-let ([(conj substitution '() disjunctions)
                 (topq:head reduced)])
      (values #f (state
                   (distribute (disjq:head disjunctions)
                               (disjq:tail disjunctions)
                               substitution)
                   (topq:tail reduced))))))


(define (substitution->constraint-store substitution)
  `(() () ,substitution () () () ()))

(define (inject . conjuncts)
  (state (list (conj (empty-s) conjuncts (disjq:queue))) (topq:queue)))

(define-syntax (fresh stx)
  (syntax-case stx ()
    [(_ (x* ...) g g* ...)
     #'(let ([x* (var (quote x*))] ...)
         (conj #f (list g g* ...) #f))]))

(define-syntax (conde stx)
  (syntax-case stx ()
    [(_ [g1 g1* ...] [g g* ...] ...)
     #'(lambda ()
         (disj
           (list
             (conj #f (list g1 g1* ...) #f)
             (conj #f (list g g* ...) #f)
             ...)))]))

(define (== a b)
  (unification a b))

(define (run-internal n query-vars current-state acc)
  (if (and (or (pair? (state-unreduced current-state))
               (not (topq:empty? (state-reduced current-state))))
           (or (false? n) (> n 0)))
    (let-values ([(result new-state) (step-state current-state)])
      (if result
        (run-internal (and n (- n 1)) query-vars new-state (cons result acc))
        (run-internal n query-vars new-state acc)))
    (map (lambda (result)
           ((reify (if (= (length query-vars) 1)
                     (car query-vars)
                     query-vars))
            (substitution->constraint-store result)))
         (reverse acc))))

(define-syntax (run stx)
  (syntax-case stx ()
    [(_ ne (x x* ...) g g* ...)
     #'(let ([n ne]
             [x (var (quote x))]
             [x* (var (quote x*))] ...)
         (run-internal n
                       (list x x* ...)
                       (inject g g* ...)
                       '()))
     ]))

(define-syntax (run* stx)
  (syntax-case stx ()
    [(_ (x x* ...) g g* ...)
     #'(run #f (x x* ...) g g* ...)]))

;; Debugging tools

(define (state-display s)
  (list (state-unreduced s) (topq:queue->list (state-reduced s))))

(define (show-step-internal n q [r '()])
  (if (> n 0)
    (let-values ([(result new-tree) (step-state q)])
      (show-step-internal (- n 1) new-tree (cons result r)))
    (values r (state-display q))))

(define (show-step n tree)
  (show-step-internal n (inject tree)))


