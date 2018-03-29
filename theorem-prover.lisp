;;; Variables used in resolution
(defvar *clauses* ())
(defvar *clause-pairs* (make-hash-table :test #'equal))

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

(defun literal-disj-p (prop)
  "Return true if PROP is a disjunction made of literals or disjunctions of literals."
  (labels ((disj-or-lit-p (p)
	     (cond ((literal-p p) t)
		   ((made-of-disj-or-lit-p p)
		    (and (disj-or-lit-p (prop1 p)) (disj-or-lit-p (prop2 p))))
		   (t nil)))
	   (made-of-disj-or-lit-p (p)
	     (and (or (literal-p (prop1 p)) (disj-p (prop1 p)))
		  (or (literal-p (prop2 p)) (disj-p (prop2 p))))))
    (if (disj-p prop)
	(disj-or-lit-p prop)
	nil)))

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
(defmacro with-props ((prop prop1 prop2) &body body)
  `(let ((,prop1 (prop1 ,prop))
	  (,prop2 (prop2 ,prop)))
     ,@body))

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
  `(cond ((literal-parts-p ,prop) (format t "~A~%" ,prop) ,prop)
	 ((or (bicond-p (prop1 ,prop)) (bicond-p (prop2 ,prop))) 
	  (format t "~A~%" ,prop) (cnf (expand-sub-bicond ,prop)))
	 ((or (impl-p (prop1 ,prop)) (impl-p (prop2 ,prop)))
	  (format t "~A~%" prop) (cnf (expand-sub-impl ,prop)))
	 ,@conds))

(defun cnf (prop)
  "Put proposition in CNF if not already."
  (cond ((literal-p prop) prop)
	((neg-p prop) (cnf (bring-in-negation prop)))
	((impl-p prop) (cnf (expand-impl prop)))
	((bicond-p prop) (cnf (expand-bicond prop)))
	((conj-p prop) (cnf-cond-conj-disj prop 
					   (t  (list (cnf (prop1 prop)) ^ (cnf (prop2 prop))))))
	((disj-p prop) (cnf-cond-conj-disj prop
					  ((or (conj-p (prop1 prop)) (conj-p (prop2 prop)))
					   (cnf (distr-disj prop)))
					  ((literal-disj-p prop) prop)
					  (t  (cnf (list (cnf (prop1 prop)) v (cnf (prop2 prop)))))))
	(t (error "Incorrect input"))))

;;; RESOLUTION
(defun make-set (L)
  "Turn L into a set by removing duplicate elements.
Removal is shallow."
  (cond ((literal-p L) (list L))
    ((endp L) nil)
    ((find (first L) (rest L)) (make-set (rest L)))
    (t (cons (first L) (make-set (rest L))))))

(defun set-equal (S1 S2) 
  "Checks to see if sets S1 and S2 are equal."
  (not (set-difference S1 S2)))

(defun set-p (S)
  "Return t is S is a set, nil otherwise."
  (cond ((not (listp S)) nil)
	((endp S) t)
	((member (first S) (rest S)) nil)
	(t (set-p (rest S)))))

(defun literal-lessp (L1 L2)
  "Return true if the string representation of L1 is less than L2 if both are
variables or negations. If a variable is compared to a negation, the variable
is considered less."
  (cond ((and (atom-p L1) (atom-p L2)) (string-lessp (string L1) (string L2)))
	((and (neg-p L1) (neg-p L2)) (string-lessp (string (neg-operand L1)) (string (neg-operand L2))))
	(t (neg-p L2))))

(defun clear ()
  "Clear clauses, clause pairs, and tried clause pairs."
  (setf *clauses* ())
  (setf *clause-pairs* (make-hash-table :test #'equal)))

(defun disj-to-set (P)
  "Convert a P into a set of its literals without connectors.
Assumes P is a disjunction of literals or other disjunctions."
  (if (disj-p P)
      (union (disj-to-set (prop1 P)) (disj-to-set (prop2 P)))
      (make-set P)))

(defun set-to-clause (S)
  "Convert set S into clausal form. Sorts S for hash key comparison
purposes and removes literals that are negations of eachother:
e.g. if both P and (~ P) are present in S, both are removed."
  (labels ((remove-neg-pairs (set)
	   (let ((neg (bring-in-negation (negate (first set)))))
	       (cond ((endp set) nil)
		     ((member neg (rest set) :test #'equal)
		      (remove-neg-pairs (remove neg (rest set) :test #'equal)))
		     (t (cons (first set) (remove-neg-pairs (rest set))))))))
    (sort (remove-neg-pairs S) #'literal-lessp)))

(defun disj-to-clause (D)
  "Convert disj D into clause."
  (set-to-clause (disj-to-set D)))

(defmacro pushnew-not-nil (item place &key (test #'equal))
  `(if ,item
      (pushnew ,item ,place :test ,test)))

(defun add-to-clauses (prop)
  "Takes PROP (assumed to be in CNF), convert each conjunct into
clauses, and add each of those sets to *CLAUSES* if not already present."
  (cond ((conj-p prop) (add-to-clauses (prop1 prop))
	 (add-to-clauses (prop2 prop)))
	((disj-p prop) (pushnew-not-nil (disj-to-clause prop) *clauses* :test #'equal))
	((neg-p prop) (pushnew-not-nil `(,prop) *clauses* :test #'equal))
	((set-p prop) (pushnew (set-to-clause prop) *clauses* :test #'equal))
	(t (pushnew (make-set prop) *clauses* :test #'equal))))

;;;RESOLUTION
(defun resolve (C1 C2)
  "Apply resolution algorithm to clauses C1 and C2. C1 and C2
are expected to be sets of literals. Returns multiple values. First value
is the new clause, if one can be made. The second value returns t if the clauses resolve
or nil otherwise."
  (dolist (literal C1 (values nil nil))
    (if (member (bring-in-negation (negate literal)) C2 :test #'equal)
	(if (and (= (length C1) 1) (= (length C2) 1))
	    (return (values nil t))
	    (return (values (union (remove literal C1 :test #'equal) 
				   (remove (bring-in-negation (negate literal)) C2 :test #'equal))
			    t))))))

(defun clause-lessp (C1 C2)
  "Return whether clause C1 is less than C2. Tests the car of C1 is literal-lessp
C2."
  (cond ((set-equal C1 C2) nil)
	((endp C1) t)
	((endp C2) nil)
	((literal-lessp (first C1) (first C2)) t)
	(t (clause-lessp (rest C1) (rest C2)))))

(defun make-pairs-with-clause (clause)
  "Make every combination of CLAUSE and each member of clauses
and add them to *CLAUSE-PAIRS* if not already present."
  (dolist (cl *clauses*)
    (multiple-value-bind (tried set) (gethash (sort (make-set (list clause cl)) #'clause-lessp) *clause-pairs*)
      (if (not (or set (equal clause cl)))
	  (setf (gethash (sort (make-set (list clause cl)) #'clause-lessp) *clause-pairs*) nil)))))

(defun make-clause-pairs ()
  "Make all combinations of two clauses from CLAUSES and and put them
in clause pairs."
  (dolist (clause *clauses*)
    (make-pairs-with-clause clause)))

(defun all-pairs-tried-p ()
  "Return true if all pairs of clauses have been tried"
  (let ((retval t))
    (loop for val being the hash-values in *clause-pairs*
       do (if (not val) (setf retval nil)))
  retval))

(defun tautology-p (P)
  "Return true if P is a tautology, nil otherwise."
  (clear)
  (add-to-clauses (cnf (negate P)))
  (make-clause-pairs)
  (format t "~a~%" *clauses*)
  (do ((new-clauses nil nil))
      ((all-pairs-tried-p) nil)
    (flet ((resolve-pairs (key val)
	     (multiple-value-bind (clause resolved) (resolve (first key) (second key))	     
	       (if (and (not val) resolved)
		   (progn
		     (add-to-clauses clause)
		     (pushnew clause new-clauses :test #'equal)))
	       (setf (gethash key *clause-pairs*) t))))
      (maphash #'resolve-pairs *clause-pairs*)
      (if (member nil *clauses*) (return t))
      (mapcar #'make-pairs-with-clause new-clauses))))

;;; TEST PROPOSITIONS
(defvar t1 'P)
(defvar t2 '(~ ~ ~ P))
(defvar t3 '(P v (~ P)))
(defvar t4 '((P v Q) -> P)) ;failed
(defvar t5 '((P -> Q) ^ (Q -> R)))
(defvar t6 '(((P -> Q) ^ (Q -> R)) -> (P -> R)))
(defvar t7 '((P -> Q) -> ((~ Q) -> (~ P))))
(defvar t8 '((P -> (~ Q)) v (P ^ Q)))
(defvar t9 '((P ^ Q) -> P))
(defvar t10 '(((~ Q) -> (~ P)) -> (P -> Q)))
(defvar t11 '((P -> (~ Q))  v ((~ P) ^ (~ Q))))
(defvar t12 '(P -> ((~ P) -> Q)))
(defvar t13 '(((~ P) -> P) -> P))
(defvar t14 '(((~ P) -> P) -> (~ P)))
(defvar t15 '((~ (P -> Q)) -> P))
