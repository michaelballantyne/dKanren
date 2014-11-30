#lang racket

(require (prefix-in topq: pfds/queue/real-time))
(require (prefix-in disjq: pfds/queue/real-time))
(require (only-in "mk.rkt" unify var reify))

(provide == run run* define-goal fresh conde appendo)

(define (topq:enqueue-all queue l)
  (if (null? l)
    queue
    (topq:enqueue-all (topq:enqueue (car l) queue) (cdr l))))

(struct substitution (alist))

(define (empty-s)
  '())

(struct conj (substitution unsorted disjunctions) #:transparent)
(struct disj (children) #:transparent)
(struct unification (left right) #:transparent)
(struct proc (name p) #:transparent)

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
      [(proc name p)
       (reduce-conj substitution (cons (p) (rest unsorted)) disjunctions)]
      [(and disj-node (? disj?))
       (reduce-conj substitution (rest unsorted) (disjq:enqueue disj-node disjunctions))])))

(define (filter-branches disjunction substitution)
  (define new-children
    (filter-map (match-lambda
                  [(conj #f children #f)
                   (let-values ([(new-substitution new-disjunctions)
                                 (reduce-conj substitution children (disjq:queue))])
                     (if new-substitution
                       (conj #f children #f)
                       #f))])
                (disj-children disjunction)))
  (if (null? new-children)
    #f
    (disj new-children)))

(define (filter-disjunctions q substitution)
  (disjq:map
    (lambda (disjunction)
      (filter-branches disjunction substitution))
    q))

(define (step-state current-state)
  (define-values (substitution disjunctions)
    (match (topq:head current-state)
      [(conj unreduced-substitution unreduced-unsorted unreduced-disjunctions)
       (reduce-conj unreduced-substitution unreduced-unsorted unreduced-disjunctions)]))
  (if (or (not substitution) (disjq:empty? disjunctions))
    (values substitution (topq:tail current-state))
    (values #f
            (let ([filtered-disjunctions (filter-disjunctions disjunctions substitution)])
              (if (not (disjq:andmap (lambda (x) x) filtered-disjunctions))
                (topq:tail current-state)
                (topq:enqueue-all
                  (topq:tail current-state)
                  (map (match-lambda
                         [(conj #f nested-unsorted #f)
                          (conj substitution nested-unsorted (disjq:tail filtered-disjunctions))])
                       (disj-children (disjq:head filtered-disjunctions)))))))))


(define (substitution->constraint-store substitution)
  `(() () ,substitution () () () ()))

(define (inject . conjuncts)
  (topq:queue (conj (empty-s) conjuncts (disjq:queue))))

(define-syntax (fresh stx)
  (syntax-case stx ()
    [(_ (x* ...) g g* ...)
     #'(let ([x* (var (quote x*))] ...)
         (conj #f (list g g* ...) #f))]))

(define-syntax (conde stx)
  (syntax-case stx ()
    [(_ [g1 g1* ...] [g g* ...] ...)
     #'(disj
         (list
           (conj #f (list g1 g1* ...) #f)
           (conj #f (list g g* ...) #f)
           ...))]))

(define (== a b)
  (unification a b))

(define (run-internal n query-vars current-state acc)
  (if (and (not (topq:empty? current-state)) (or (false? n) (> n 0)))
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

(define-syntax (define-goal stx)
  (syntax-case stx ()
    [(_ (name args ...) body)
     #'(define (name args ...)
         (proc name (lambda ()
           body)))]))

(define-goal (appendo l s out)
  (conde
    [(== '() l) (== s out)]
    [(fresh (a d res)
       (== `(,a . ,d) l)
       (== `(,a . ,res) out)
       (appendo d s res))]))

(define (state-display s)
  (topq:queue->list s))

(define (show-step-internal n q [r '()])
  (if (> n 0)
    (let-values ([(result new-tree) (step-state q)])
      (show-step-internal (- n 1) new-tree (cons result r)))
    (values r (state-display q))))

(define (show-step n tree)
  (show-step-internal n (inject tree)))

#|

(run* (q) (== 'a 'b))

(run* (q) (== 'a 'a))

(run* (q) (fresh ()
            (== 'a 'b)
            (== 'a 'a)))

(run* (q) (conde
            [(== 'a q)]
            [(== 'b q)]))

(run* (q) (conde
            [(== 'a 'b)
             (== 'a q)]
            [(== 'b q)]))

(run* (q) (appendo '(a b) '(c d) q))

(define-goal (valueo x v)
  (fresh ()
    (== x v)
    (conde
      [(== 'a 'a)]
      [(valueo x v)])))

(run* (q) (fresh ()
            (valueo q 1)
            (valueo q 2)))

(run 10 (q) (fresh ()
            (valueo q 1)
            (valueo q 1)))

(run* (x y z) (appendo `(a . ,x) y `(b . ,z)))

|#


