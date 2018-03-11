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
  (or (atom-p prop) (and (neg-p prop) 
			 (atom-p (neg-operand prop)))))

(defun conj-p (prop)
  "Retrun true if the proposition is a conjunction."
  (and (listp prop) (eq ^ (connector prop))))

(defun disj-p (prop)
  "Retrun true if the proposition is a conjunction."
  (and (listp prop) (eq v (connector prop))))

(defun neg-p (prop)
  "Return true if prop is a negation."
  (and (listp prop) (eq (neg-sign prop) ~)))

(defun impl-p (prop)
  "Return true if prop is an implication."
  (and (listp prop) (eq (connector prop) ->)))

(defun bicond-p (prop)
  "Return true if prop is a biconditional."
  (and (listp prop) (eq (connector prop) <->)))

(defun literal-parts-p (prop)
  "Return true if prop is a of the form <literal> <connector> <literal>."
  (and (listp prop)  
       (literal-p (prop1 prop))
       (literal-p (prop2 prop))))

(defun sub-literal-disj-p (prop)
  "Return true if a disjunction is made of a disjunction of literals."
  (and (or (literal-p (prop1 prop)) 
       (and (disj-p (prop1 prop)) (literal-parts-p (prop1 prop))))
      (or (literal-p (prop2 prop))
       (and (disj-p (prop2 prop)) (literal-parts-p (prop2 prop))))))

;;;Selectors
(defun connector (prop)
  (second prop))

(defun prop1 (prop)
  (first prop))

(defun prop2 (prop)
  (third prop))

(defun neg-sign (prop)
  (first prop))

(defun neg-operand (prop)
  (second prop))

;;;Functions for putting into CNF
(defun bring-in-negation (prop &optional (has-even-negs nil negs-supplied-p))
  "Simplify a negation by eliminating extra negations signs
and applying DeMorgan's law to conjunctions and disjunctions."
  (labels ((double-neg-p (p)
	   (eq (neg-operand p) ~))
	 (double-neg-bring-in (p else &optional (even-negs nil))
	   (if (double-neg-p p)
		(bring-in-negation (rest p) even-negs)
		else)))
    (let ((operand (neg-operand prop)))
      (cond 
	(negs-supplied-p (if has-even-negs 
			     (double-neg-bring-in prop operand nil)              ;prop is negation with even # of negation symbols
			     (double-neg-bring-in  prop (negate operand) t)))                      ;prop is a negation with an odd # of negation symbols		 
	((disj-p operand)                   ;prop is a disjunction
	 `(,(negate (prop1 operand)) ^ ,(negate (prop2 operand))))
	((conj-p operand)                   ;prop is a conjunction
	 `(,(negate (prop1 operand)) v ,(negate (prop2 operand))))
	((impl-p operand) (bring-in-negation `(~ ,(expand-impl operand))))
	((bicond-p operand) (bring-in-negation `(~ ,(expand-bicond operand))))
	(t (double-neg-bring-in prop (negate operand) t))))))

(defun distr-disj (prop)
  "Distribute disjunction; e.g. (P v (Q ^ R))
becomes (P v Q) ^ (P v R). Assumes prop is a disjunction
and at least one of the sub propositions is a conjunction."
  (with-props (prop p1 p2)
    (if (conj-p p1)
	`((,(prop1 p1) v ,p2) ^ (,(prop2 p1) v ,p2))
	`((,(prop1 p2) v ,p1) ^ (,(prop2 p2) v ,p1)))))

(defun expand-impl (prop)
  "Convert proposition of the form P -> Q to
~P v Q. Assumes prop is a implication."
  (with-props (prop p1 p2) 
    `(,(negate p1) v ,p2)))

(defun expand-bicond (prop)
  "Convert proposition of the form P <-> Q
to ((~ P) v Q) ^ ((~ Q) v P). Assumes prop is a biconditional."
  (with-props (prop p1 p2)
    `((,(negate p1) v ,p2) ^ (,(negate p2) v ,p1))))

(defun negate (prop)
  "Negate a proposition."
  (if (neg-p prop)
      (cons ~ prop)
      `(~ ,prop)))

(defun expand-sub-bicond (prop)
  "Expand a biconditional that makes up the proposition.
Assumes at least one of the component propositions is a biconditional."
  (with-props (prop p1 p2)
    (if (bicond-p p1)
	`(,(expand-bicond p1) ,(connector prop) ,p2)
	`(,p1 ,(connector prop) ,(expand-bicond p2)))))

(defun expand-sub-impl (prop)
  "Expand an implication that makes up the proposition.
Assumes at least one of the component propositions is an implication."
  (with-props (prop p1 p2)
    (if (impl-p p1)
	`(,(expand-impl p1) ,(connector prop) ,p2)
	`(,p1 ,(connector prop) ,(expand-impl p2)))))

(defmacro cnf-cond-conj-disj (prop &rest conds)
  "Cover conditions common to converting conjunctions or disjunctions
during conversion to CNF in addition to those specified in conds."
  `(cond ((literal-parts-p ,prop) ,prop)
	 ((or (bicond-p (prop1 ,prop)) (bicond-p (prop2 ,prop))) 
	  (cnf (expand-sub-bicond ,prop)))
	 ((or (impl-p (prop1 ,prop)) (impl-p (prop2 ,prop)))
	  (cnf (expand-sub-impl ,prop)))
	 ,@conds))

(defun cnf (prop)
  "Put proposition in CNF if not already."
  (cond ((literal-p prop) prop)
	((neg-p prop) (cnf (bring-in-negation prop)))
	((impl-p prop) (cnf (expand-impl prop)))
	((bicond-p prop) (cnf (expand-bicond prop)))
	((conj-p prop) (cnf-cond-conj-disj prop 
					   (t (list (cnf (prop1 prop)) ^ (cnf (prop2 prop))))))
	((disj-p prop) (cnf-cond-conj-disj prop
					  ((or (conj-p (prop1 prop)) (conj-p (prop2 prop)))
					    (cnf (distr-disj prop)))
					  ((sub-literal-disj-p prop) prop)
					   (t (cnf (list (cnf (prop1 prop)) v (cnf (prop2 prop)))))))
	(t (error "Incorrect input"))))

;;;UTILITY
(defmacro with-props ((prop prop1 prop2) &body body)
  `(let ((,prop1 (prop1 ,prop))
	  (,prop2 (prop2 ,prop)))
     ,@body))
;(P v (Q v (R ^ S)))
;(P v ((Q v R) ^ (Q v S)))
;((P v (Q v R)) ^ (P v (Q v S)))