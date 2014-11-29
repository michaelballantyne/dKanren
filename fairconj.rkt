#lang racket

(require (prefix-in q: pfds/queue/implicit))
(require (only-in "mk.rkt" unify var reify))
(require profile)

(provide == run run* define-goal fresh conde appendo)

(define (enqueue-all queue l)
  (if (null? l)
    queue
    (enqueue-all (q:enqueue (car l) queue) (cdr l))))

(struct substitution (alist) )

(define (empty-s)
  '())

(struct state (unreduced reduced) #:transparent)
(struct conj (substitution unsorted disjunctions procs) #:transparent)
(struct disj (children) #:transparent)
(struct unification (left right) #:transparent)
(struct proc (name p) #:transparent)

(define (tree-append t1 t2)
  (if (null? t1)
    t2
    (cons t1 t2)))

(define (tree-first tree)
  (if (pair? (first tree))
    (tree-first (first tree))
    (first tree)))

(define (tree-rest tree)
  (if (pair? (first tree))
    (let ([rest-subtree (tree-rest (first tree))])
      (if (null? rest-subtree)
        (rest tree)
        (cons rest-subtree (rest tree))))
    (rest tree)))

(define (update-conj node
                     #:substitution [sbst (conj-substitution node)]
                     #:unsorted [all-t (conj-unsorted node)]
                     #:disjunctions [disj-t (conj-disjunctions node)]
                     #:procs [proc-t (conj-procs node)])
  (conj sbst all-t disj-t proc-t))

(define (inc disjunct)
  (values #f (list disjunct)))

(define (reduce-disjunct disjunct)
  (match-define (conj substitution unsorted disjunctions procs) disjunct)
  (cond
    [(pair? unsorted)
     (match (tree-first unsorted)
       ; Apply a unification
       [(unification term1 term2)
        (let ([new-substitution (unify term1 term2 substitution)])
          (cond
            [(not new-substitution)
             (values #f '())]
            [(and (null? (tree-rest unsorted))
                  (null? disjunctions)
                  (null? procs))
             (values new-substitution '())]
            [else
              (inc (update-conj disjunct
                     #:substitution new-substitution
                     #:unsorted (tree-rest unsorted)))]))]
       ; Lift branches of a nested conjunct
       [(conj #f nested-unsorted '() '())
        (inc (update-conj disjunct
               #:unsorted (tree-append (tree-rest unsorted) nested-unsorted)))]
       ; Move a disjunct to its delayed list
       [(and disj-node (? disj?))
        (inc (update-conj disjunct
               #:unsorted (tree-rest unsorted)
               #:disjunctions (tree-append disj-node disjunctions)))]
       ; Move a proc to its delayed list
       [(and proc-node (? proc?))
        (inc (update-conj disjunct
               #:unsorted (tree-rest unsorted)
               #:procs (tree-append procs (list proc-node))))])]
    ; If we have a disjunction, distribute the remaining children into it. They won't
    ; be unifications or conjunctions because of the previous cases.
    [(pair? disjunctions)
     (values
       #f
       (map (match-lambda
              [(conj #f nested-unsorted nested-disjunctions nested-procs)
               (conj substitution
                     nested-unsorted
                     (tree-append nested-disjunctions (tree-rest disjunctions))
                     (tree-append nested-procs procs))])
            (disj-children (tree-first disjunctions))))]))

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
         [(conj substitution '() '() procs)
          (conj substitution (list ((proc-p (tree-first procs)))) '() (tree-rest procs))]))
     (values #f (state (q:enqueue expanded-disjunct unreduced-q)
                       (q:tail reduced-q)))]
    ; Else, look at the first element in the unreduced-q
    [else
      (match (q:head unreduced-q)
        ; The element is fully reduced.
        [(conj substitution '() '() _)
        (values #f (state (q:tail unreduced-q)
                          (q:enqueue (q:head unreduced-q) reduced-q)))]
        ; The element needs reducing.
        [disjunct
         (define-values (result new-disjuncts)
           (reduce-disjunct disjunct))
         (values result (state (enqueue-all (q:tail unreduced-q) new-disjuncts)
                               reduced-q))])]))

(define (substitution->constraint-store substitution)
  `(() () ,substitution () () () ()))

(define (inject . conjuncts)
  (state (q:queue (conj (empty-s) conjuncts '() '())) (q:queue)))

(define-syntax (fresh stx)
  (syntax-case stx ()
    [(_ (x* ...) g g* ...)
     #'(let ([x* (var (quote x*))] ...)
         (conj #f (list g g* ...) '() '()))]))

(define-syntax (conde stx)
  (syntax-case stx ()
    [(_ [g1 g1* ...] [g g* ...] ...)
     #'(disj
         (list
           (conj #f (list g1 g1* ...) '() '())
           (conj #f (list g g* ...) '() '())
           ...))]))

(define (== a b)
  (unification a b))

(define (run-internal n query-vars current-state acc)
  (if (and current-state (or (false? n) (> n 0)))
    (let-values ([(result new-state) (step-state current-state)])
      (if result
        (run-internal (and n (- n 1)) query-vars new-state (cons result acc))
        (run-internal n query-vars new-state acc)))
    (list (map (lambda (result)
           ((reify (if (= (length query-vars) 1)
                     (car query-vars)
                     query-vars))
            (substitution->constraint-store result)))
         (reverse acc))
  (if current-state (append (q:queue->list (state-unreduced current-state))
                    (q:queue->list (state-reduced current-state))) #f)
          )))

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
  (state
    (q:queue->list (state-unreduced s))
    (q:queue->list (state-reduced s))))


(define (show-step-internal n q [r '()])
  (if (> n 0)
    (let-values ([(result new-tree) (step-state q)])
      (show-step-internal (- n 1) new-tree (cons result r)))
    (values r (state-display q))))

(define (show-step n tree)
  (show-step-internal n (inject tree)))



#|


(run 2 (q) (== 'a 'a))

(run 2 (q) (== q 'a))

(run 1 (q) (== q `(,q)))

(run* (x y) (== x y))

(run* (q) (conde
            [(== q 1)]
            [(== q 2)]))



(define-goal (valueo x v)
  (fresh ()
    (== x v)
    (conde
      [(== 'a 'a)]
      [(valueo x v)])))

(define-goal (valueo2 x v)
  (conde
    [(== x v)]
    [(== x v)
     (valueo2 x v)]))

(run* (q) (fresh ()
            (valueo2 q 1)
            (valueo2 q 2)))

(run* (q) (fresh ()
            (valueo q 1)
            (valueo q 2)))

(run 10 (q) (fresh ()
            (valueo q 1)
            (valueo q 1)))


(run 10 (x y z) (appendo `(a . ,x) y `(a . ,z)))

(run* (x y z) (appendo `(a . ,x) y `(b . ,z)))

(time (length (run* (q) (fresh (x y) (appendo x y (make-list 1000 1)) (== (list x y) q)))))



(define (p1)
  (conj #f  (list (disj (list (conj #f (list (unification 'a 'a)))
                              (conj #f (list p1))))
                  (unification x 'a))))

(define (p2)
  (conj #f  (list (disj (list (conj #f (list (unification 'a 'a)))
                              (conj #f (list p2))))
                  (unification x 'b))))

(run 1000 (conj #f (list p1 p1)))


(run 1 (unification 'a 'b))

(run 1 (unification 'a 'a))

(run 2 (conj #f (list (unification 1 'a)
                      (disj (list (conj #f (list (unification 2 'a)))
                                  (conj #f (list (unification 2 'b))))))))


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
