(in-package :maxima)

;; Call as eg
;;
;;   fps_get_coeff (expr, x^2*y^3)
;;
;; The reason for the syntax is that we need to pass the variables as well as
;; the powers, since expr can be any old expression, possibly containing formal
;; power series.
(defmfun $fps_get_coeff (expr indmonomial)
  (let (($fpsvars '(($SET))))
    (declare (special $fpsvars))
    (fps-get-coeff expr (fps-monomial-degrees indmonomial))))

(defmfun $fps_get_constant_term (expr)
  (fps-get-coeff expr '(nil)))

;; INDSET should be of the form (($x $y) 2 3)
(defun fps-get-coeff (expr indset)
  (let ((real-op (unless ($atom expr)
                   (if (listp (car expr)) (caar expr) (car expr)))))
    (cond
      (($atom expr) (fps-get-coeff-atom expr indset))
      ((equal real-op '$FPS) (fps-get-coeff-fps expr indset))
      ((equal real-op 'MPLUS)
       (cons '(MPLUS)
             (mapcar (lambda (x) (fps-get-coeff x indset))
                     (cdr ($args expr)))))
      ((equal real-op 'MTIMES)
       (fps-get-coeff-times expr indset))
      ((equal real-op 'MEXPT)
       (fps-get-coeff-pow expr indset))
      ((equal real-op '$COMPOSE)
       (fps-get-coeff-comp expr indset))
      (t
       (merror
        (format nil "Can't deal with this expression yet (operator: ~A)"
                real-op))))))

;; The coefficients for an atom (might be the only variable with a nonzero power
;; in indset!)
(defun fps-get-coeff-atom (atom indset)
  (let ((nzi nil))
    (do ((pows (cdr indset) (cdr pows))
         (i 0 (1+ i)))
        ((not pows))
      (when (> (car pows) 0) (push i nzi)))
    (cond
      ((> (length nzi) 1) 0)
      ((not nzi)
       (if (or ($numberp atom) (not (member atom (car indset))))
           atom 0))
      (t
       (if (and (eq (nth (first nzi) (car indset)) atom)
                (= (nth (first nzi) (cdr indset)) 1))
           1 0)))))

;; Given an fps and an indset, we first check that there aren't any variables for
;; indset which have a nonzero power and don't appear in fps. If there are, return
;; false.
;;
;; Otherwise, we can reasonably produce a list of indices to pass to
;; the fps's function in order to get a coefficient.
;;
(defun fps-maybe-make-index-list (fps indset)
  (let ((badposn
         (do ((vars (car indset) (cdr vars))
              (pows (cdr indset) (cdr pows))
              (i 0 (1+ i)))
             ((not vars) nil)
           (when (and (> (car pows) 0)
                      (not (member (car vars) (cdr ($second fps)))))
             (return i)))))
    (unless badposn
      (cons '(MLIST)
            (mapcar (lambda (v)
                      (let ((pos (position v (car indset))))
                        (if pos (nth pos (cdr indset)) 0)))
                    (cdr ($second fps)))))))

;; The coefficients for an fps itself.
(defun fps-get-coeff-fps (fps indset)
  (let ((il (fps-maybe-make-index-list fps indset)))
    (if il ($fps_extract_coeff fps il) 0)))

;; The coefficients in a product.
;;
;; Suppose I have a product A*B*C and want the coefficient of x^4*y^2.
;;
;; Then we consider the coefficient of each x^i y^j in A for (i,j) <=
;; (4,2). Whenever this coefficient is not zero, multiply by the coefficient of
;; x^(4-i) y^(2-j) in B*C.
;;
;; Iterating in this way should allow us to make use of known zeros.
(defun fps-get-coeff-times (prod indset)
  (let ((acc 0))
    (each-lst-less-than
     (lambda (pows)
       (let ((coeff (fps-get-coeff ($first prod) (cons (car indset) pows))))
         (unless (equal 0 coeff)
           (let* ((therest (if (= 1 (length (cddr prod)))
                               (caddr prod)
                               (cons (car prod) (cddr prod))))
                  (mult (fps-get-coeff
                         therest
                         (cons (car indset) (mapcar #'- (cdr indset) pows)))))
             (setf acc (add acc (mul coeff mult)))))))
     (cdr indset))
    acc))

(defun each-lst-less-than (fun maxes &optional prev)
  "Call FUN on each list of non-negative integers which is termwise <=
  MAXES. Return (VALUES)."
  (if maxes
      (dotimes (n (1+ (car maxes)))
        (each-lst-less-than fun (cdr maxes) (append prev (list n))))
      (funcall fun prev)))

(defun hist (seq)
  (let ((ht (make-hash-table)))
    (map nil (lambda (x)
               (let ((n (gethash x ht)))
                 (setf (gethash x ht) (if n (1+ n) 1))))
         seq)
    ht))

(defun num-identical-permutations (seq)
  (let ((k 1))
    (maphash (lambda (x n)
               (declare (ignore x))
               (setf k (* k (factorial n))))
             (hist seq))
    k))

(defun fps-get-coeff-pow-1 (down up var power)
  (let ((ht (make-hash-table)) (sum 0))
    (flet ((a-coef (k)
             (let ((hit (gethash k ht)))
               (unless hit
                 (setf hit (fps-get-coeff down (list (list var) k)))
                 (setf (gethash k ht) hit))
               hit)))
      (map nil
           (lambda (partition)
             (let ((prod 1))
               (dolist (k partition)
                 (let ((c (a-coef k)))
                   (if (equal c 0)
                       (progn (setf prod 0) (return))
                       (setf prod (mul prod c)))))
               (setf sum (add sum
                              (mul (/ (factorial (length partition))
                                      (num-identical-permutations partition))
                                   prod)))))
           (mapcar #'cdr (cdr ($integer_partitions power up))))
      sum)))

(defun fps-get-coeff-pow (exp indset)
  (let ((down ($first exp)) (up ($second exp)))
    (unless (integerp up) (merror "Can't deal with this exponent."))
    (unless (> up 0) (merror "Can only deal with positive exponents."))

    (case (length (car indset))
      (0 (power (fps-get-coeff down indset) up))
      (1 (fps-get-coeff-pow-1 down up (caar indset) (cadr indset)))
      (otherwise
       (merror "Currently can only do powers with <= 1 variable.")))))

(defun each-lst-sum-between (fun min max len &optional prev)
  "Call FUN on each list of non-negative integers whose sum is at at least MIN
and at most MAX. Assumes that it gets called with LEN
positive. Return (VALUES)."
  (unless (or (< max min) (< len 1))
    (if (= len 1)
        (loop
           for n from (max 0 min) to max
           do (funcall fun (append prev (list n))))
        (loop
           for n from 0 to max
           do (each-lst-sum-between fun (- min n) (- max n) (1- len)
                                    (append prev (list n)))))))

(defun fps-validate-compose (fps args)
  (unless (and (listp fps) (listp (car fps)) (equal (caar fps) '$FPS))
    (merror "Can only do composition with straight FPS outside."))

  (unless (= (length (cdr ($second fps))) (length args))
    (merror "Number of args not number of variables in outside FPS."))

  (unless (every (lambda (arg) (equal 0 ($fps_get_constant_term arg)))
                 args)
    (merror "Composition of FPS's only makes sense when const coeffs 0")))

(defun fps-get-coeff-comp-1 (fps args var pow)
  (fps-validate-compose fps args)
  (let ((sum 0))
    (each-lst-sum-between
     (lambda (powers)
       (let ((prod 1))
         (do ((powsleft powers (cdr powsleft))
              (argsleft args (cdr argsleft))
              (n 0 (1+ n)))
             ((not powsleft))
           (when (> (car powsleft) 0)
             (setf prod
                   (mul prod
                        (fps-get-coeff (power (car argsleft) (car powsleft))
                                       (list (list var) pow))))))
         (setf sum (add sum (mul ($fps_extract_coeff fps `((mlist) ,@powers))
                                 prod)))))
     1 pow (length args))
    sum))

(defun fps-get-coeff-comp (comp indset)
  (let ((fps ($first comp))
        (args (cddr comp)))
    (fps-validate-compose fps args)

    (case (length (car indset))
      (0 ($fps_get_constant_term fps))
      (1 (fps-get-coeff-comp-1 fps args (caar indset) (cadr indset)))
      (otherwise
       (merror "Can only currently expand composites in one variable.")))))
