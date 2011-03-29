(in-package :maxima)

(defun make-monomial (vars indices)
  (let ((prod 1))
    (loop
       for v in vars
       for i in indices
       do (setf prod (mul prod (power v i))))
    prod))

(defun fps-term (fps indices)
  (mul (make-monomial (cdr ($second fps)) indices)
       ($fps_extract_coeff fps `((mlist) ,@indices))))

(defun fps-terms-of-order (fps order)
  (cond
    ((< order 0) 0)
    ((= order 0) ($fps_get_constant_term fps))
    (t
     (let ((sum 0))
       (dolist (part (cdr ($integer_partitions
                           order (length (cdr ($second fps))))))
         (dolist (perm (cdr (simplify ($permutations part))))
           (setf sum (add sum (mul (num-identical-permutations
                                    (cdr perm))
                                   (fps-term fps (cdr perm)))))))
       sum))))

(defun fps-bound-variables (expr)
  (let ((ht (make-hash-table)) (vars nil))
    (labels ((process (x)
               (cond
                 ((atom x) nil)

                 ((equal (caar x) '$fps) (add-vars (cdr ($second x))))

                 ((equal (caar x) '$compose)
                  (map nil #'process (cddr x)))

                 (t (map nil #'process (cdr x)))))
           (add-vars (vars)
             (dolist (v vars) (setf (gethash v ht) t))))
      (process expr)
      (maphash (lambda (v a) (declare (ignore a)) (push v vars)) ht)
      vars)))

(defmfun $fps_partial_sum (expr maxorder)
  (let (($fpsvars
         (cons '(MLIST) (fps-bound-variables expr))))
    (declare (special $fpsvars))
    (cond
      ((< maxorder 0) 0)
      ((or (atom expr) (freeof '$fps expr)) expr)
      ((equal (caar expr) '$fps)
       (unless (fps-validp expr)
         (merror "Invalid formal power series."))
       (fps-partial-sum-fps expr maxorder))

      ((member (caar expr) '(MPLUS MTIMES))
       ($ratexpand
        (cons (car expr)
              (mapcar (lambda (x) ($fps_partial_sum x maxorder))
                      (cdr expr)))))

      ((and (equal (caar expr) 'MEXPT)
            ($integerp ($second expr))
            (>= ($second expr) 0))
       ($ratexpand
        (list '(MEXPT)
              ($fps_partial_sum ($first expr) maxorder) 
              ($second expr))))

      ((equal (caar expr) '$compose)
       (fps-kill-hidegrees
        (fps-partial-sum-compose ($first expr) (cddr expr) maxorder)
        maxorder))

      (t
       (merror (format nil "Cannot handle operator: ~S" (caar expr)))))))

(defun fps-partial-sum-fps (fps maxorder)
  (let ((sum 0))
    (loop
       for n from 0 to maxorder
       do (setf sum (add sum (fps-terms-of-order fps n))))
    sum))

(defun fps-partial-sum-compose (fps args maxorder)
  (fps-validate-compose fps args)
  (let* ((expansions
          (mapcar (lambda (x) ($fps_partial_sum x maxorder))
                  args))
         (realvars (cdr ($second fps)))
         (dummys
          (mapcar (lambda (v) (declare (ignore v)) ($gensym))
                  realvars))
         fexp)
    (setf (cdr (third fps)) dummys)
    (setf fexp ($fps_partial_sum fps maxorder))
    (setf (cdr (third fps)) realvars)

    (loop
       for e in expansions
       for d in dummys
       do
         (setf fexp ($ratexpand ($substitute e d fexp))))
    fexp))

(defun fps-monomial-order (m)
  (cond
    ((freeof-fpsvars m) 0)
    ((atom m) 1)
    ((varpowp m) ($second m))
    (t
     (unless (equal (caar m) 'MTIMES)
       (merror "Invalid monomial"))
     (let ((sum 0))
       (dolist (e (cdr m))
         (setf sum (add sum (fps-monomial-order e))))
       sum))))

(defun fps-kill-hidegrees (expr maxpow)
  (cond
    ((atom expr) expr)
    (($fps_monomialp expr)
     (if (> (fps-monomial-order expr) maxpow) 0 expr))
    (t
     (simplify
      (cons (remove 'simp (car expr))
            (mapcar (lambda (x) (fps-kill-hidegrees x maxpow))
                    (cdr expr)))))))
