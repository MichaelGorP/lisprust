(define (simple x) x)
(simple 42.0)

(define tak-float (lambda (x y z)
  (if (not (< y x))
      z
      (tak-float (tak-float (- x 1.0) y z)
                 (tak-float (- y 1.0) z x)
                 (tak-float (- z 1.0) x y)))))

(tak-float 18.0 12.0 6.0)
