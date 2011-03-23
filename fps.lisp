(in-package :maxima)

;; TODO: This assumes that ($second fps) is fps@vars etc.

;; Get the coefficient for the indices list I. If given an integer, treats it as
;; a one-element list.
(defmfun $fps_extract_coeff (fps I)
  (let ((J (if ($integerp I) `((MLIST) ,I) I)))
    (fps-get-coeff-sanity-check fps J)
    ($apply ($first fps) J)))

(defun fps-get-coeff-sanity-check (fps I)
  (unless (and (mfunction-call $fpsp fps)
               ($listp I))
    (merror "Needs a list of indices and a FPS"))
  (unless (= (length (cdr ($second fps)))
             (length (cdr I)))
    (merror "Wrong number of indices."))
  (unless (every (lambda (i) (and ($integerp i) (>= i 0))) (cdr I))
    (merror "I must be a list of non-neg integers"))
  (let ((tot (reduce '+ (cdr I))))
    (unless (or (= -1 ($third fps)) (>= ($third fps) tot))
      (merror "FPS not defined to that degree."))))

;; See fps_monomialp
(defmfun $freeof_fpsvars (expr)
  (declare (special $fpsvars))
  (unless (boundp '$fpsvars) (merror "fpsvars not bound"))
  (unless (or ($setp $fpsvars) ($listp $fpsvars))
    (merror "fpsvars not a list or set"))
  (and (> ($length $fpsvars) 0)
       (every (lambda (v) (freeof v expr)) (cdr $fpsvars))))

;; True for atoms or powers of atoms
(defmfun $varpowp (expr)
  (or ($atom expr)
      (and (string= ($op expr) "^")
           ($atom ($first expr))
           (integerp ($second expr)))))

;; Tests to see whether an expression is a monomial in the variables we care
;; about. Note that we use dynamically bound fpsvars, since if we're looking at
;; an fps in x,y then (a^2+1)*x^2*y will be represented as
;;
;; ((MTIMES SIMP)
;;  ((MPLUS SIMP) 1 ((MEXPT SIMP) $A 2))
;;  ((MEXPT SIMP) $X 2) $Y)
;;
;; and if we drilled down further in code to find monomial orders it'd give the
;; wrong answer!
;;
;; However, if fpsvars is empty then freeof_fpsvars automatically returns false
;; (rather than the more logical true) so that we can use this code to check for
;; general monomials too.
(defmfun $fps_monomialp (expr)
  (or ($varpowp expr)
      (and (string= ($op expr) "*")
           (every (lambda (u) (or ($varpowp u) ($freeof_fpsvars u)))
                  (cdr expr)))))

(defun fps-monomial-degrees_ (m)
  (unless ($fps_monomialp m)
    (merror "This is not a monomial that I can understand"))
  (cond
    (($numberp m) '(($SET)))
    (($atom m) `(($SET) ((MLIST) ,m 1)))
    (($varpowp m) `(($SET)
                    ((MLIST) ,($first m) ,($second m))))
    ((string= ($op m) "*")
     (reduce #'$union (mapcar #'fps-monomial-degrees_ (cdr m))))
    (t
     (merror "Invalid monomial"))))

;; x^2*y^3  => (($x $y) 2 3)
;; so CAR gives the list of vars and CDR the list of powers.
(defun fps-monomial-degrees (m)
  (let* ((pairs (fps-monomial-degrees_ m))
         (vars (mapcar #'second (cdr pairs)))
         (pows (mapcar #'third (cdr pairs))))
    (unless (= (length (remove-duplicates vars)) (length vars))
      (merror "Duplicate variable"))
    (cons vars pows)))

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


;; fps_get_coeff_ (expr, indset) := block(
;;   if is(atom(expr)) then fps_get_coeff_atom_ (expr, indset)
;;   else
;;   block ([o_: op(expr), a_: args(expr)],
;;     if is(o_ = 'fps) then fps_get_coeff_fps_ (expr, indset)
;;     elseif is(o_ = "+")
;;     then apply(o_, map(lambda([x_], fps_get_coeff_ (x_, indset)), a_))
;;     elseif is(o_ = "*")
;;     then fps_get_coeff_times_ (expr, indset)
;;     else error(")))$

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

