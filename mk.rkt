#lang racket
;; microKanren DLS '16
;; Jason Hemann, Dan Friedman, Will Byrd, & Matt Might

#| Nat → Var |#
(define (var n) n)

#| Term → Bool |#
(define (var? t) (number? t))

#| Term × Subst → Term |#
(define (find u s) 
  (let ((pr (and (var? u) (assv u s))))
    (if pr (find (cdr pr) s) u)))

#| Var × Term × Subst → Maybe Subst |#
(define (ext-s x v s)
  (cond 
    ((occurs? x v s) #f)
    (else (cons `(,x . ,v) s))))

#| Var × Term × Subst → Bool |#
(define (occurs? x u s)
  (cond
    ((var? u) (eqv? x u))
    ((pair? u) (or (occurs? x (find (car u) s) s)
                   (occurs? x (find (cdr u) s) s)))
    (else #f)))

#| Term × Term × Subst → Maybe Subst |#
(define (unify u v s)
  (cond
    ((eqv? u v) s)
    ((var? u) (ext-s u v s))
    ((var? v) (unify v u s))
    ((and (pair? u) (pair? v))
     (let ((s (unify (find (car u) s) (find (car v) s) s)))
       (and s (unify (find (cdr u) s) (find (cdr v) s) s))))
    (else #f)))

#| Term × Term → Goal |#
(define ((== u v) s/c)
  (let ((s (car s/c)))
    (let ((s (unify (find u s) (find v s) s)))
      (if s (list `(,s . ,(cdr s/c))) `()))))

((== '#t 'z) '(() . 0))
'()
((== '#t '#t) '(() . 0))
'((() . 0))
((== '(#t . #f) '(#t . #f)) '(() . 0))
'((() . 0))

#| (Var → Goal) → Goal |#
(define ((call/fresh f) s/c)
  (let ((c (cdr s/c)))
    ((f (var c)) `(,(car s/c) . ,(+ c 1)))))

((call/fresh
    (λ (x) 
       (== x 'a)))
   '(() . 0))
'((((0 . a)) . 1))

(define-syntax-rule (define-relation (defname . args) g)
  (define ((defname . args) s/c) (delay/name (g s/c))))

(define-relation (append l s o)
  (conde
    ((== '() l) (== s o))
    ((fresh (a d)
       (== `(,a . ,d) l)
       (fresh (r)
         (== `(,a . ,r) o)
         (append d s r))))))

(define-relation (peano n)
  (disj
    (== n 'z)
    (call/fresh 
      (λ (r)
        (conj
          (== n `(s ,r))
          (peano r))))))

(define-relation (unproductive n)
  (unproductive n))

(define ($append $1 $2)
  (cond
    ((null? $1) $2)
    ((promise? $1) (delay/name ($append $2 (force $1))))
    (else (cons (car $1) ($append (cdr $1) $2)))))

#| Goal × Stream → Stream |#
(define ($append-map g $)
  (cond
    ((null? $) '())
    ((promise? $) (delay/name ($append-map g (force $))))
    (else ($append (g (car $)) ($append-map g (cdr $))))))

#| Goal × Goal → Goal |#
(define ((disj g1 g2) s/c) ($append (g1 s/c) (g2 s/c)))

#| Goal × Goal → Goal |#
(define ((conj g1 g2) s/c) ($append-map g2 (g1 s/c)))
 ((disj 
     (call/fresh 
       (λ (x) 
         (== 'z x)))
     (call/fresh 
       (λ (x) 
         (== '(s z) x))))
   '(() . 0))
'((((0 . z)) . 1) (((0 . (s z))) . 1))

((call/fresh 
   (λ (x) 
     (call/fresh
       (λ (y) 
         (conj 
           (== y x)
           (== 'z x))))))
 '(() . 0))
'((((0 . z) (1 . 0)) . 2))


((call/fresh
   (λ (n)
     (peano n)))
 '(() . 0))

#| Maybe Nat⁺ × Goal→ Mature |#
(define (call/initial-state n g) 
  (take n (pull (g '(() . 0)))))

#| Stream → Mature |#
(define (pull $) (if (promise? $) (pull (force $)) $))

#| Maybe Nat⁺ × Mature → List |#
(define (take n $)
  (cond
    ((null? $) '())
    ((and n (zero? (- n 1))) (list (car $)))
    (else (cons (car $) 
            (take (and n (- n 1)) (pull (cdr $)))))))

(call/initial-state 2
    (call/fresh
      (λ (n)
        (peano n))))
'((((0 . z)) . 1) (((1 . z) (0 . (s 1))) . 2))

(call/initial-state 1
  (call/fresh
    (λ (n)
      (disj 
        (unproductive n)
        (peano n)))))

(define-relation (church n)
  (call/fresh 
    (λ (b)
      (conj
        (== n `(λ (s) (λ (z) ,b)))
        (peano b)))))

 (call/initial-state 3
    (call/fresh
      (λ (n)
       (disj
         (peano n)
         (church n)))))
'((((0 . z)) . 1)
  (((1 . z) (0 . (s 1))) . 2)
  (((1 . z) (0 . (λ (s) (λ (z) 1)))) . 2))

(define (desugared-append l s o)
  (λ (s/c)
    (delay/name
      ((disj
         (conj 
           (== l '())
           (== s o))
         (call/fresh
           (λ (a)
             (call/fresh 
               (λ (d)
                 (conj 
                   (== l `(,a . ,d))
                   (call/fresh 
                     (λ (r)
                       (conj 
                         (== o `(,a . ,r))
                         (desugared-append d s r))))))))))
       s/c)))) 

 (call/initial-state #f
    (call/fresh
      (λ (q)
        (desugared-append '(t u v) '(w x) q))))

(define ((ifte g0 g1 g2) s/c)
  (let loop (($ (g0 s/c)))
    (cond
      ((null? $) (g2 s/c))
      ((promise? $) (delay/name (loop (force $))))
      (else ($append-map $ g1)))))

(call/initial-state #f
   (call/fresh
     (λ (q)
       (ifte (== 'a 'b) (== q 'a) (== q 'b)))))
'((((0 . b)) . 1))

(define ((once g) s/c)
  (let loop (($ (g s/c)))
    (cond
      ((null? $) '())
      ((promise? $) (delay/name (loop (force $))))
      (else (list (car $))))))

(call/initial-state #f
   (call/fresh
     (λ (q)
       (once (peano q)))))
'((((0 . z)) . 1))

(define-syntax disj+
  (syntax-rules ()
    ((_ g) g)
    ((_ g0 g ...) (disj g0 (disj+ g ...)))))

(define-syntax conj+
  (syntax-rules ()
    ((_ g) g)
    ((_ g0 g ...) (conj g0 (conj+ g ...)))))

(define-syntax-rule (conde (g0 g ...) (g0* g* ...) ...)
  (disj+ (conj+ g0 g ...) (conj+ g0* g* ...) ...))

(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g ...) (conj+ g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/fresh (λ (x0) (fresh (x ...) g0 g ...))))))

(define-syntax ifte*
  (syntax-rules ()
    ((_ g) g)
    ((_ (g0 g1) (g0* g1*) ... g)
     (ifte g0 g1 (ifte* (g0* g1*) ... g)))))

(define-syntax-rule (conda (g0 g1 g ...) ... (gn0 gn ...))
  (ifte* (g0 (conj+ g1 g ...)) ... (conj+ gn0 gn ...)))

(define-syntax-rule (condu (g0 g1 g ...) ... (gn0 gn ...))
  (conda ((once g0) g ...) ... ((once gn0) gn ...)))

(define (apply-subst v s)
  (let ((v (find v s)))
    (cond
      ((var? v) v)
      ((pair? v) (cons (apply-subst (car v) s)
                       (apply-subst (cdr v) s)))
      (else v))))

(define (build-r v s c)
  (cond
    ((var? v) `((,v . ,(+ (length s) c)) . ,s))
    ((pair? v) (build-r (cdr v) (build-r (car v) s c) c))
    (else s)))

(define (project-var0 s/c)
  (let ((v (apply-subst (var 0) (car s/c))))
    (let ((v (apply-subst v (build-r v '() (cdr s/c)))))
      (apply-subst v (build-r v '() 0)))))

(define-syntax-rule (run n (q) g0 g ...)
  (map project-var0 
    (call/initial-state n (fresh (q) g0 g ...))))

(map project-var0
   (call/initial-state #f
     (call/fresh
       (λ (q)
         (call/fresh
           (λ (l)
             (call/fresh
               (λ (s)
                 (conj
                   (== `(,l ,s) q) 
                   (append l s '(t u v w x)))))))))))

(run #f (q) (append '(t u v) '(w x) q))
'((t u v w x))

(run #f (q) (append '(t u v) q '(t u v w x)))
'((w x))

(run #f (q) (fresh (l s) (== `(,l ,s) q) (append l s '(t u v w x))))
