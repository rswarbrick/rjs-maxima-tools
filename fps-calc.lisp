(in-package :maxima)

(defmfun $fps_make_inverse (subvar fps maxorder)
  (unless (integerp maxorder)
    (merror "maxorder must be an integer."))
  (unless ($fpsp fps)
    (merror "fps must be a fps"))
  (unless (symbolp subvar)
    (merror "subvar must be a symbol"))

  (kill1 subvar)
  (let* ((inv (mfunction-call $subvar_to_fps subvar ($second fps) -1))
         (prod (mul fps inv)))
    (loop
       for n below maxorder
       do (let* ((var `((,subvar simp array) ,n))
                 (coeff (fps-get-coeff prod (list (cdr ($second fps)) n)))
                 (soln ($solve (if (= n 0) (add -1 coeff) coeff)
                               `((mlist) ,var))))
            (unless (and ($listp soln)
                         (= 1 (length (cdr soln)))
                         (equal var ($first ($first soln))))
              (merror "Failed solving for the coefficients. Got:" soln))
            (marrayset ($second ($first soln)) subvar n)))))

