#lang racket
(require redex)

(define-language iswim
  ((M N L K) X (λ X M) (M M) b (o2 M M) (o1 M))
  (o o1 o2)
  (o1 add1 sub1 iszero)
  (o2 + - * ^)
  (b number)
  ((V U W) b X (λ X M))
  (E hole (V E) (E M) (o V ... E M ...))
  ((X Y Z) variable-not-otherwise-mentioned))

(define-metafunction iswim
  [(δ (iszero 0)) (λ x (λ y x))]
  [(δ (iszero b)) (λ x (λ y y))]
  [(δ (add1 b)) ,(add1 (term b))]
  [(δ (sub1 b)) ,(sub1 (term b))]
  [(δ (+ b_1 b_2)) ,(+ (term b_1) (term b_2))]
  [(δ (- b_1 b_2)) ,(- (term b_1) (term b_2))]
  [(δ (* b_1 b_2)) ,(* (term b_1) (term b_2))]
  [(δ (^ b_1 b_2)) ,(expt (term b_1) (term b_2))])

(define-metafunction iswim
  ;; 1. X_1 bound, so don't continue in λ body
  [(subst (λ X_1 any_1) X_1 any_2) 
   (λ X_1 any_1)]
  
  ;; 2. do capture-avoiding substitution 
  [(subst (λ X_1 any_1) X_2 any_2)
   (λ X_3 
     (subst (subst-var any_1 X_1 X_3) X_2 any_2))
   (where X_3 ,(variable-not-in (term (X_2 any_1 any_2))
                                (term X_1)))]
  
  ;; 3. replace X_1 with any_1
  [(subst X_1 X_1 any_1) any_1]
  
  ;; recur on the tree structure of the term
  [(subst (any_2 ...) X_1 any_1)
   ((subst any_2 X_1 any_1) ...)]
  [(subst any_2 X_1 any_1) any_2])

(define-metafunction iswim
  [(subst-var (any_1 ...) variable_1 variable_2)
   ((subst-var any_1 variable_1 variable_2) ...)]
  [(subst-var variable_1 variable_1 variable_2) variable_2]
  [(subst-var any_1 variable_1 variable_2) any_1])

(define iswim-red
  (reduction-relation
   iswim
   (--> (in-hole E ((λ X M) V))
        (in-hole E (subst M X V))
        βv)
   (--> (in-hole E (o b ...))
        (in-hole E (δ (o b ...)))
        δ)))

; (traces iswim-red (term ((λ y (y y)) (λ x (x x)))))

(define iswim-standard
  (reduction-relation
   iswim
   (v ((λ X M) V) (subst M X V) βv)
   (v (o b ...) (δ (o b ...)) δ)
   with
   [(--> (in-hole E M) (in-hole E N)) (v M N)]))

; (traces iswim-standard (term ((λ y (y y)) (λ x (x x)))))

;; Error ISWIM
(define-extended-language e-iswim
  iswim
  (M ....
     (err b))
  (o2 ....
      /))

(define-metafunction e-iswim
  [(δ/ (/ b 0)) (err 0)]
  [(δ/ (/ b_1 b_2)) ,(/ (term b_1) (term b_2))]
  [(δ/ (o V ...)) (δ (o V ...))])

(define e-iswim-red-first-try
  (extend-reduction-relation
   iswim-red
   e-iswim
   (--> (in-hole E (o b ...))
        (in-hole E (δ/ (o b ...)))
        δ)
   (--> (in-hole E (o b ... (λ X M) V ...))
        (in-hole E (err ,(add1 (length (term (b ...))))))
        δerr1)
   (--> (in-hole E (b V))
        (in-hole E (err b))
        δerr2)
   (--> (in-hole E (err b))
        (err b)
        err)))

; (traces e-iswim-red-first-try (term (/ ((λ x (/ 1 x)) 7) 2)))
; (traces e-iswim-red-first-try (term (/ ((λ x (+ (/ 1 x) (err 2))) 7) 2)))

(define e-iswim-red
  (extend-reduction-relation
   iswim-red
   e-iswim
   (--> (in-hole E (o b ...))
        (in-hole E (δ/ (o b ...)))
        δ)
   (--> (in-hole E (o b ... (λ X M) V ...))
        (in-hole E (err ,(add1 (length (term (b ...))))))
        δerr1)
   (--> (in-hole E (b V))
        (in-hole E (err b))
        δerr2)
   (--> (in-hole E (err b))
        (err b)
        err
        (side-condition
         (not (equal? (term hole) (term E)))))))

; (traces e-iswim-red (term (/ ((λ x (+ (/ 1 x) (err 2))) 7) 2)))