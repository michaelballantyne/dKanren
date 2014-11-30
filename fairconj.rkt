#lang racket

(require (prefix-in q: pfds/deque/implicit))
(require (only-in "mk.rkt" unify var reify))

(provide == run run* define-goal fresh conde appendo)

(define (enqueue-all queue l)
  (if (null? l)
    queue
    (enqueue-all (q:enqueue (car l) queue) (cdr l))))

(struct substitution (alist))

(define (empty-s)
  '())

(struct conj (substitution unsorted disjunctions) #:transparent)
(struct disj (children) #:transparent)
(struct unification (left right) #:transparent)
(struct proc (name p) #:transparent)


(define (update-conj current-state
                     #:substitution [substitution (conj-substitution (q:head current-state))]
                     #:unsorted     [unsorted     (conj-unsorted     (q:head current-state))]
                     #:disjunctions [disjunctions (conj-disjunctions (q:head current-state))])
  (values #f (q:enqueue-front (conj substitution unsorted disjunctions)
                              (q:tail current-state))))

(define (step-state current-state)
  (match-define (conj substitution unsorted disjunctions) (q:head current-state))
  (if (pair? unsorted)
    (match (first unsorted)
      [(unification term1 term2)
       (let ([new-substitution (unify term1 term2 substitution)])
         (cond
           [(not new-substitution)
            (values #f (q:tail current-state))]
           [(and (null? (rest unsorted))
                 (q:empty? disjunctions))
            (values new-substitution (q:tail current-state))]
           [else (update-conj current-state
                   #:substitution new-substitution
                   #:unsorted (rest unsorted))]))]
      [(conj #f nested-unsorted #f)
       (update-conj current-state
         #:unsorted (append nested-unsorted
                            (rest unsorted)))]
      [(proc name p)
       (update-conj current-state
         #:unsorted (cons (p) (rest unsorted)))]
      [(and disj-node (? disj?))
       (update-conj current-state
         #:unsorted (rest unsorted)
         #:disjunctions (q:enqueue disj-node disjunctions))])
    (values #f
            (enqueue-all
              (q:tail current-state)
              (map (match-lambda
                     [(conj #f nested-unsorted #f)
                      (conj substitution nested-unsorted (q:tail disjunctions))])
                   (disj-children (q:head disjunctions)))))))

(define (substitution->constraint-store substitution)
  `(() () ,substitution () () () ()))

(define (inject . conjuncts)
  (q:deque (conj (empty-s) conjuncts (q:deque))))

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
  (if (and (not (q:empty? current-state)) (or (false? n) (> n 0)))
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
  (q:deque->list s))

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


