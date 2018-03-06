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
			 (atom-p (second prop)))))

(defun conjunction-p (prop)
  "Retrun true if the proposition is a conjunction."
  (and (listp prop) (eq ^ (second prop))))

(defun disjunction-p (prop)
  "Retrun true if the proposition is a conjunction."
  (and (listp prop) (eq v (second prop))))

(defun negation-p (prop)
  "Return true if prop is a negation."
  (eq (first prop) ~))

;;;Selectors
(defun connector (prop)
  (second prop))

(defun prop1 (prop)
  (first prop))

(defun prop2 (prop)
  (third prop))

;;;Functions for putting into CNF
(defun make-negation (prop)
  )

(defun distribute-or (prop)
  "Distribute disjunction; e.g. (P v (Q ^ R))
becomes (P v Q) ^ (P v R)."
  ())