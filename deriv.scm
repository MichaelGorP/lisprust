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
         (list '*
                a
                (cons '+
                      (map (lambda (a) (list '/ (deriv a) a)) (cdr a)))))
        ((eq? (car a) '/)
         (list '-
               (list '/
                     (deriv (cadr a))
                     (caddr a))
               (list '/
                     (cadr a)
                     (list '*
                           (caddr a)
                           (caddr a)
                           (deriv (caddr a))))))
        (else
         (error #f "No derivation method available"))))

(list
  (deriv '(+ x 3))
  (deriv '(* x 3))
  (deriv '(/ x 3))
  (deriv '(+ (* (* 3 x x) (+ (/ 0 3) (/ 1 x) (/ 1 x)))
   (* (* a x x) (+ (/ 0 a) (/ 1 x) (/ 1 x)))
   (* (* b x) (+ (/ 0 b) (/ 1 x)))
   0))
)
