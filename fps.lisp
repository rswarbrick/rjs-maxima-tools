(in-package :maxima)

(defun fps-validp (f)
  (and ($listp ($second f))
       (> (length (cdr ($second f))) 0)
       (every #'atom (cdr ($second f)))
       ($integerp ($third f))
       (>= ($third f) -1)))

;; Get the coefficient for the indices list I. If given an integer, treats it as
;; a one-element list.
(defmfun $fps_extract_coeff (fps I)
  (let ((J (if ($integerp I) `((MLIST) ,I) I)))
    (fps-extract-coeff-sanity-check fps J)
    ($apply ($first fps) J)))

(defun fps-extract-coeff-sanity-check (fps I)
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
(defun freeof-fpsvars (expr)
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
           (every (lambda (u) (or ($varpowp u) (freeof-fpsvars u)))
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
