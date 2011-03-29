(in-package :maxima)

(defmfun $fps_make_inverse (subvar fps maxorder)
  (unless (and (integerp maxorder) (<= 0 maxorder))
    (merror "maxorder must be a non-negative integer."))
  (unless (and ($fpsp fps) (= 1 (length (cdr ($second fps)))))
    (merror "fps must be a fps in one variable"))
  (unless (symbolp subvar)
    (merror "subvar must be a symbol"))

  ($fps_populate_subvar
   subvar
   (sub (mul fps ($subvar_to_fps subvar ($second fps) maxorder)) 1)
   maxorder))

(defun ordered-integer-partitions (n length)
  "Return a list of the ordered partitions of N into LENGTH non-negative
  integers. The algorithm used is pretty inefficient..."
  (unless (and (integerp length) (>= length 1))
    (error "Nonsense length: ~A" length))
  (if (> length 1)
      (let ((acc))
        (dotimes (k (1+ n))
          (push (mapcar (lambda (lst) (cons k lst))
                        (ordered-integer-partitions (- n k) (1- length)))
                acc))
        (reduce #'append acc))
      (list (list n))))

(defun all-variables (expr &optional ignore-these)
  (let ((ht (make-hash-table :test 'equalp)) (vars nil))
    (labels ((process (x)
               (cond
                 ((atom x)
                  (when (and (symbolp x)
                             (not (member x ignore-these)))
                    (setf (gethash x ht) t)))
                 ((member 'array (car x))
                  (setf (gethash x ht) t))
                 (t
                  (map nil #'process (cdr x))))))
      (process expr)
      (maphash (lambda (v a) (declare (ignore a)) (push v vars)) ht)
      vars)))

(defun occurrences-of-subvar (sym expr)
  (remove-if-not (lambda (x) (and (not (atom x)) (equal sym (caar x))))
                 (all-variables expr)))

(defun try-to-extract-solutions (vars-to-find solns?)
  (unless (and ($listp solns?) (listp vars-to-find))
    (error "solns? and vars-to-find should be lists."))

  (when (= 0 (length (cdr solns?)))
    (merror "Found no solutions."))

  ;; $solve returns a list of solution sets if given more than one variable.
  (when (> (length (cdr vars-to-find)) 1)
    (when (> (length (cdr solns?)) 1)
      (merror "Found multiple solution sets."))
    (setf solns? ($first solns?)))

  (let ((lh (mapcar #'$first (cdr solns?)))
        (rh (mapcar #'$second (cdr solns?))))
    (mapcar (lambda (v)
              (let ((pos (position v lh :test #'meqp)))
                (unless pos
                  (merror "Can't find solution for var in list."))
                (nth pos rh)))
            (cdr vars-to-find))))

(defmfun $fps_populate_subvar (subvar expr maxorder &optional (kill? t))
  "Consider EXPR, an expression involving SUBVAR, to be equal to zero and fill
  in the coefficients of subvar, finally returning subvar_to_fps(subvar, vars,
  maxorder)."
  (unless (symbolp subvar)
    (merror "subvar must be a symbol"))
  (unless (and (integerp maxorder) (<= 0 maxorder))
    (merror "maxorder must be a non-negative integer."))

  (let ((vars (fps-bound-variables expr)))
    (when kill? (kill1 subvar))
    (loop
       for order from 0 to maxorder do
         (let* ((eqns
                 (cons '(mlist)
                       (mapcar
                        (lambda (part) (fps-get-coeff expr
                                                      (cons vars part)))
                        (ordered-integer-partitions order (length vars)))))
                (solve-for (cons '(mlist) (occurrences-of-subvar subvar eqns))))

           (when (> (length solve-for) (length eqns))
             (merror "Trying to solve for more variables than we have equations."
                     solve-for eqns))

           (unless (= 0 (length (cdr solve-for)))
             (loop
                for var in (cdr solve-for)
                for ans in (try-to-extract-solutions solve-for
                                                     ($solve eqns solve-for))
                do
                  (apply #'marrayset ans subvar (cdr var))))))
    ($subvar_to_fps subvar (cons '(mlist) vars) maxorder)))

