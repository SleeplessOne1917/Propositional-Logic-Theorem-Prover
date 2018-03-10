;;; Variables used in resolution
(defvar *clauses* ())
(defvar *clause-pairs* ())
(defvar *tried-clause-pairs* ())

;;; Logical symbols
(defconstant -> '->)
(defconstant <-> '<->)
(defconstant v 'v)
(defconstant ^ '^)
(defconstant ~ '~)

;;; Predicates
(defun atom-p (prop)
  "Return true if prop is an atom."
  (and (not (symbol-p prop)) (not (listp prop))))

(defun symbol-p (prop) 
  "Return true if prop is one of the defined logical symbol."
  (or (eq prop ->) 
      (eq prop <->) 
      (eq prop ~)
      (eq prop v)
      (eq prop ^)))

(defun literal-p (prop)
  "Return true if an atom is an atom or the
negation of an atom."
  (or (atom-p prop) (and (negation-p prop) 
			 (atom-p (negation-operand prop)))))

(defun conjunction-p (prop)
  "Retrun true if the proposition is a conjunction."
  (and (listp prop) (eq ^ (connector prop))))

(defun disjunction-p (prop)
  "Retrun true if the proposition is a conjunction."
  (and (listp prop) (eq v (connector prop))))

(defun negation-p (prop)
  "Return true if prop is a negation."
  (and (listp prop) (eq (negation-sign prop) ~)))

;;;Selectors
(defun connector (prop)
  (second prop))

(defun prop1 (prop)
  (first prop))

(defun prop2 (prop)
  (third prop))

(defun negation-sign (prop)
  (first prop))

(defun negation-operand (prop)
  (second prop))

;;;Functions for putting into CNF
(defun bring-in-negation (prop &optional (has-even-negs nil negs-supplied-p))
  "Simplify a negation by eliminating extra negations signs
and applying DeMorgan's law to conjunctions and disjunctions."
  (flet ((double-negation-p (p)
	   (eq (negation-operand p) ~)))
    (let ((operand (negation-operand prop)))
      (macrolet ((double-neg-bring-in (p else &optional (even-negs nil))
		   `(if (double-negation-p ,p)
			(bring-in-negation (rest ,p) ,even-negs)
			,else)))
      (cond 
	(negs-supplied-p (if has-even-negs 
			     (double-neg-bring-in prop operand nil)              ;prop is negation with even # of negation symbols
			     (double-neg-bring-in  prop (negate operand) t)))                      ;prop is a negation with an odd # of negation symbols		 
	((disjunction-p operand)                   ;prop is a disjunction
	 `(,(negate (prop1 operand)) ^ ,(negate (prop2 operand))))
	((conjunction-p operand)                   ;prop is a conjunction
	 `(,(negate (prop1 operand)) v ,(negate (prop2 operand))))
	(t (double-neg-bring-in prop (negate operand) t)))))))

(defun distribute-or (prop)
  "Distribute disjunction; e.g. (P v (Q ^ R))
becomes (P v Q) ^ (P v R). Assumes prop is a disjunction
and at least one of the sub propositions is a conjunction."
  (with-props (prop p1 p2)
    (if (conjunction-p p1)
	`((,(prop1 p1) v ,p2) ^ (,(prop2 p1) v ,p2))
	`((,(prop1 p2) v ,p1) ^ (,(prop2 p2) v ,p1)))))

(defun expand-implication (prop)
  "Convert proposition of the form P -> Q to
~P v Q. Assumes prop is a implication."
  (with-props (prop p1 p2) 
    `(,(negate p1) v ,p2)))

(defun expand-biconditional (prop)
  "Convert proposition of the form P <-> Q
to ((~ P) v Q) ^ ((~ Q) v P). Assumes prop is a biconditional."
  (with-props (prop p1 p2)
    `((,(negate p1) v ,p2) ^ (,(negate p2) v ,p1))))

(defun negate (prop)
  "Negate a proposition."
  (if (negation-p prop)
      (cons ~ prop)
      `(~ ,prop)))

;;;UTILITY
(defmacro with-props ((prop prop1 prop2) &body body)
  `(let* ((,prop1 (prop1 ,prop))
	  (,prop2 (prop2 ,prop)))
     ,@body))
