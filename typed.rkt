#lang typed/racket

(require (prefix-in q: pfds/queue/implicit))
(require/typed "current-micro.rkt"
               [unify (-> Term Term Substitution Substitution)])

(struct: conj ([substitution : Substitution] [children : (Listof Goal)]))
(struct: disj ([children : (Listof Goal)]))
(struct: unification ([left : Term] [right : Term]))

(define-type Goal (U conj disj unification (-> Goal)))
(define-type Term (U LogicVar Symbol))
(define-type LogicVar Integer)
(define-type Substitution (Listof (Listof Term)))
(define-type Result (U Boolean Substitution))

(: empty-s (-> Substitution))
(define (empty-s)
  '())

(: reduce-disjunct (-> Substitution (Listof Goal) (values Result (Listof Goal))))
(define (reduce-disjunct substitution children)
  (match #{ children : (Listof Goal)}
    ; Apply a unification
    [(list-no-order (unification left right) #{other-children : (Listof Goal)} ...)
     (values #f '())]
    ; Lift branches of any nested conjunct
    [(list-no-order (conj #f #{nested-children : (Listof Goal)}) #{other-children : (Listof Goal)} ...)
     (values #f '())]
    ; If we have a disjunction, distribute the remaining children into it. They won't
    ; be unifications or conjunctions because of the previous cases.
    [(list-no-order (disj #{disj-children : (Listof Goal)}) #{other-children : (Listof Goal)} ...)
     (values #f '())]
    [e (values #f '())]))

