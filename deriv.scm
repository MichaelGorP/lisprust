(define (map f l)
  (if (null? l)
      '()
      (cons (f (car l)) (map f (cdr l)))))

(define (deriv a)
  (cond ((not (pair? a))
         (if (eq? a 'x) 1 0))
        ((eq? (car a) '+)
         (cons '+
               (map deriv (cdr a))))
        ((eq? (car a) '-)
         (cons '-
               (map deriv (cdr a))))
        ((eq? (car a) '*)
         (let ((u (cadr a))
               (v (caddr a)))
           (list '+
                 (list '* (deriv u) v)
                 (list '* u (deriv v)))))
        ((eq? (car a) '/)
         (let ((u (cadr a))
               (v (caddr a)))
           (list '/
                 (list '-
                       (list '* (deriv u) v)
                       (list '* u (deriv v)))
                 (list '* v v))))
        (else
         (error #f "No derivation method available"))))

(list
  (deriv '(+ x 3))
  (deriv '(* x 3))
  (deriv '(/ x 3))
)
