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
      ((member real-op '(MPLUS MMINUS))
       (cons (list real-op)
             (mapcar (lambda (x) (fps-get-coeff x indset))
                     (cdr ($args expr)))))
      ((equal real-op 'MTIMES)
       (fps-get-coeff-times expr indset))
      ((equal real-op 'MEXPT)
       (fps-get-coeff-pow expr indset))
      ((equal real-op '$COMPOSE)
       (fps-get-coeff-comp expr indset))
      ((equal real-op '%SUM)
       (fps-get-coeff-sum expr indset))
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
       (let ((prod 1)
             (coeff ($fps_extract_coeff fps `((mlist) ,@powers))))
         ;; I have chosen the powers to which I'm going to raise the
         ;; arguments. I've already extracted the coefficient from the parent
         ;; fps, since that might be zero and I don't want to waste time if so.
         ;;
         ;; Now I want the coefficient of "z^n" in the arguments raised to these
         ;; powers.
         (loop
            for a in args
            for p in powers
            when (> p 0) do (setf prod (mul prod (pow a p))))
         (setf sum
               (add sum (mul coeff (fps-get-coeff prod (list (list var) pow)))))))
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

;; ((%SUM SIMP) ((MTIMES . #1=(SIMP)) (($A SIMP ARRAY) $N) ((MEXPT . #1#) $X
;; $N)) $N 0 $INF)

(defun fps-analyze-sum (expr)
  "Spot sums with terms of the form f(n)*a^l1(n)*b^l2(n) etc. where l1 and l2
are (assumed to be increasing) functions of the form u*n+c.

Returns (const . ((x 3 2) (y 1 0))) for const*x^(3n+2)*y^n."

  (unless (and (not (atom expr)) (eq (caar expr) '%SUM))
    (merror "Cannot analyse expr since it's not a sum."))
  (let ((term ($first expr))
        (var ($second expr)))
    (flet ((analyse-parts (parts)
             (let ((monomials) (const))
               (loop
                  for part in parts do
                    (if (not (and (mexptp part)
                                  (symbolp ($first part))))
                        (push part const)
                        (let ((ana (islinear ($second part) var)))
                          (if ana
                              (push (list ($first part) (car ana)
                                          (cdr ana))
                                    monomials)
                              (push part const)))))
               (cons (reduce #'mul const) monomials))))
      (cond
        ((mtimesp term)
         (analyse-parts (rest term)))
        ((and (mexptp term) (symbolp ($first term)))
         (analyse-parts (list term)))
        (t (cons term nil))))))

(defun fps-get-coeff-sum (sum indset)
  (let* ((ana-coeff (fps-analyze-sum sum))
         (constraints))
    (when (or (not (or (integerp ($third sum))
                       (memq ($third sum) '($INF $MINF))))
              (not (or (integerp ($fourth sum))
                       (memq ($fourth sum) '($INF $MINF)))))
      (merror "Can only cope with numbers and infinities as sum bounds."))

    ;; This is only going to work if, after analysis of the terms of the sum,
    ;; the constant terms remaining are free of each variable in indset.
    (loop
       for x in (car indset)
       unless (freeof x (car ana-coeff))
       do (merror "Can't analyse sum enough to separate out variable."))

    (cond
      ((loop
          for x in (car indset)
          for n in (cdr indset)
          do (let ((c (find x (cdr ana-coeff) :key #'car)))
               (if c
                   ;; Constraints will hold the different things "n" must equal.
                   (push (div (sub n (third c)) (second c)) constraints)
                   ;; Else if n>0, we know there can be no contribution from the
                   ;; entire sum, so return here.
                   (if (> n 0) (return t)))))
       0)

      ((null constraints) sum)

      ;; Look for constraints that conflict with the first one.
      ((loop
          for c in (cdr constraints)
          do (let ((z ($zeroequiv (sub (car constraints) c) 0)))
               (when (eq z '$dontknow)
                 (merror "Can't determine whether there's a contribution here."))
               (unless z (return t))))
       0)

      ((not (numberp (car constraints)))
       (merror "Can't deal with a non-numeric power at the moment."))

      ((or (not (integerp (car constraints)))
           (eq ($third sum) '$INF)
           (eq ($fourth sum) '$MINF)
           (and (numberp ($third sum)) (> ($third sum) (car constraints)))
           (and (numberp ($fourth sum)) (< ($fourth sum) (car constraints))))
       0)

      ;; Use the first constraint to set n.
      (t
       (mul (subst (car constraints) ($second sum) (car ana-coeff))
            (reduce #'mul
                    (mapcar
                     (lambda (monomial)
                       (pow (first monomial)
                            (add (mul (second monomial) (car constraints))
                                 (third monomial))))
                     (remove-if (lambda (monomial)
                                  (member (car monomial) (car indset)))
                                (cdr ana-coeff)))))))))
