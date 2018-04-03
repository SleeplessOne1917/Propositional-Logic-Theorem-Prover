;;;; THEOREM-PROVER.LISP
;;;; Author: Anthony Bias
;;;; Propositional logic theorem prover to determine if a well formed formula is a tautology.
;;;; Performs proofs by contradiction by first negating the wff and converting it into cnf.
;;;; Then, each conjunct of the result is turned into a clause. Resolution is applied to both these original
;;;; clauses and new clauses produced during the proof until either nil is produced or all pairs
;;;; of clauses have been tried.

;;;; TABLE OF CONTENTS
;;;;------------------------
;;;; 1: LOGICAL SYMBOLS
;;;; 2: FORM PREDICATES
;;;; 3: SELECTORS
;;;; 4: CNF
;;;; 5: CLAUSE CREATION
;;;; 6: CLAUSE PAIRS
;;;; 7: RESOLUTION
;;;; 8: TESTS

;;;; 1: LOGICAL SYMBOLS ==============================================================================
(defconstant -> '->)           ;Material implication
(defconstant <-> '<->)         ;Biconditional
(defconstant v 'v)             ;Disjunction
(defconstant ^ '^)             ;Conjunction
(defconstant ~ '~)             ;Negation

;;;; 2: FORM PREDICATES ================================================================================

;;;; Forms are are either a variable, the negation of a variable, or any two forms joined
;;;; by a connective.
;;;; <form> ::= <lit> | <form> ("->" | "<->" | "v" | "^") <form>

;;; Variables are forms that consist of a single propositional variable, e.g. P, Q, R, T, etc.
;;; <var> ::= variable
(defun variable-p (F)
  "Return true if F is an variable."
  (and (not (symbol-p F)) (not (listp F))))

;;; A symbol is any of the binary connectives or the negation sign
;;; <sym> ::= "->" | "<->" | "v" | "^" | "~"
(defun symbol-p (F) 
  "Return true if F is one of the defined logical symbol."
  (or (eq F ->) 
      (eq F <->) 
      (eq F ~)
      (eq F v)
      (eq F ^)))

;;; Literals are variables or negations of variables, e.g. P, (~ P), Q, (~ Q), etc.
;;; <lit> ::= ["~"] <var>
(defun literal-p (F)
  "Return true if an variable is an variable or the
negation of an variable."
  (or (variable-p F) (and (neg-p F) 
			 (variable-p (neg-operand F)))))

;;; Conjunctions are forms that consist of two forms joinend with ^,
;;; e.g. (P ^ Q), ((~ Q) ^ (R v (~ T))), etc.
;;; <conj> ::= <form> "^" <form>
(defun conj-p (F)
  "Retrun true if the Fosition is a conjunction."
  (and (listp F) (eq ^ (connector F))))

;;; Disjunctions are forms that consist of two forms joined with v,
;;; e.g. (T v G), ((P ^ R) v (R v (~ Q)))
;;; <disj> ::= <form> "v" <form>
(defun disj-p (F)
  "Retrun true if the Fosition is a conjunction."
  (and (listp F) (eq v (connector F))))

;;; Negations are forms preceded by ~, e.g. (~ P), (~ (R -> T)), (~ R), etc.
;;; <neg> ::= "~" {"~"} <form>
(defun neg-p (F)
  "Return true if F is a negation."
  (and (listp F) (eq (neg-sign F) ~)))

;;; Implications are forms joined by ->, e.g. (P -> Q), ((~ R) -> (T ^ Q)), etc.
;;; <impl> ::= <form> "->" <form>
(defun impl-p (F)
  "Return true if F is an implication."
  (and (listp F) (eq (connector F) ->)))

;;; Biconditionals are forms joined by <->, e.g. (Q <-> R), (((~ P) ^ T) <-> Q), 
;;; ((Q -> R) <-> ((~P) ^ T)), etc.
;;; <bicond> ::= <form> "<->" <form>
(defun bicond-p (F)
  "Return true if F is a biconditional."
  (and (listp F) (eq (connector F) <->)))

;;;; 3: SELECTORS =======================================================================
(defun connector (F)
  (second F))

(defun phi (F)
  (first F))

(defun psy (F)
  (third F))

(defun neg-sign (F)
  (first F))

(defun neg-operand (F)
  (second F))

;;;; 4: CNF =============================================================================================
;;;; The following are functions and macros used to convert a form into cnf

(defmacro with-phi-and-psy ((F phi psy) &body body)
  `(let ((,phi (phi ,F))
	  (,psy (psy ,F)))
     ,@body))

(defun bring-in-neg (F)
  "Simplify negation F by eliminating extra negations signs
and applying DeMorgan's law to conjunctions and disjunctions."
  (labels 
      ;; Return true if P is a negation of a negation
      ((double-neg-p (p)
	 (eq (neg-operand p) ~))
       ;; Recursively bring in negation P. ELSE handles base case when all
       ;; extra "~"s are removed
       (double-neg-bring-in (p else &optional (even-negs nil))
	 (if (double-neg-p p)
	     (bring-in-neg-rec (rest p) even-negs)
	     else))
       ;; Recursive local function to do most of the work. Using a local function prevents
       ;; users from passing in a value for HAS-EVEN-NEGS.
       (bring-in-neg-rec (F &optional (has-even-negs nil negs-supplied-p))
	 (let ((operand (neg-operand F)))
	   (cond 
	     ;; Only true if form from the first call to function is a negation of a negation
	     (negs-supplied-p
	      (if has-even-negs 
		  (double-neg-bring-in F operand nil)                       ;F is negation with even # of negation symbols
		  (double-neg-bring-in  F (weak-negate operand) t)))        ;F is a negation with an odd # of negation symbols		 
	     ((disj-p operand)
	      `(,(weak-negate (phi operand)) ^ ,(weak-negate (psy operand))))
	     ((conj-p operand)                   
	      `(,(weak-negate (phi operand)) v ,(weak-negate (psy operand))))
	     ((impl-p operand) (bring-in-neg-rec `(~ ,(expand-impl operand))))
	     ((bicond-p operand) (bring-in-neg-rec `(~ ,(expand-bicond operand))))
	     (t (double-neg-bring-in F (weak-negate operand) t))))))
    (bring-in-neg-rec F)))

(defun distr-disj (F)
  "Distribute disjunction; e.g. (P v (Q ^ R))
becomes (P v Q) ^ (P v R). Assumes F is a disjunction
and at least one of the sub Fositions is a conjunction."
  (with-phi-and-psy (F phi psy)
    (if (conj-p phi)
	`((,(phi phi) v ,psy) ^ (,(psy phi) v ,psy))
	`((,(phi psy) v ,phi) ^ (,(psy psy) v ,phi)))))

(defun expand-impl (F)
  "Convert form of the form P -> Q to
~P v Q. Assumes F is a implication."
  (with-phi-and-psy (F phi psy) 
    `(,(weak-negate phi) v ,psy)))

(defun expand-bicond (F)
  "Convert form of the form P <-> Q
to ((~ P) v Q) ^ ((~ Q) v P). Assumes F is a biconditional."
  (with-phi-and-psy (F phi psy)
    `((,(weak-negate phi) v ,psy) ^ (,(weak-negate psy) v ,phi))))

(defun weak-negate (F)
  "Add a negation sign to a form without performing negation."
  (if (neg-p F)
      (cons ~ F)
      `(~ ,F)))

(defun negate (F)
  "Negate F"
  (bring-in-neg (weak-negate F)))

(defun expand-sub-bicond (F)
  "Expand a biconditional that makes up the form.
Assumes at least one of the component forms is a biconditional."
  (with-phi-and-psy (F phi psy)
    (if (bicond-p phi)
	`(,(expand-bicond phi) ,(connector F) ,psy)
	`(,phi ,(connector F) ,(expand-bicond psy)))))

(defun expand-sub-impl (F)
  "Expand an implication that makes up the form.
Assumes at least one of the component forms is an implication."
  (with-phi-and-psy (F phi psy)
    (if (impl-p phi)
	`(,(expand-impl phi) ,(connector F) ,psy)
	`(,phi ,(connector F) ,(expand-impl psy)))))

(defun literal-parts-p (F)
  "Return true if F is a of the form: <lit> ("->" | "<->" | "v" | "^") <lit>"
  (and (listp F)  
       (literal-p (phi F))
       (literal-p (psy F))))

(defun literal-disj-p (F)
  "Return true if F is a disjunction made of literals or disjunctions of literals."
  (labels 
      ;; Recursively check if P consists of literals or disjunctions. Called by top level
      ;; function to cause conjunctions to percolate up during conversion to cnf.
      ((disj-or-lit-p (p)
	 (cond ((literal-p p) t)
	       ((made-of-disj-or-lit-p p)
		(and (disj-or-lit-p (phi p)) (disj-or-lit-p (psy p))))
	       (t nil)))
       (made-of-disj-or-lit-p (p)
	 (and (or (literal-p (phi p)) (disj-p (phi p)))
	      (or (literal-p (psy p)) (disj-p (psy p))))))
    ;; Only call local function if F is a disjunction
    (if (disj-p F)
	(disj-or-lit-p F)
	nil)))

;;; Used to remove code repetition from the conditions in the function CNF
;;; that handle conjunctions and disjunctions
(defmacro cnf-cond-conj-disj (F &rest conds)
  "Cover conditions common to converting conjunctions or disjunctions
to CNF in addition to those specified in conds."
  `(cond ((literal-parts-p ,F) ,F)
	 ((or (bicond-p (phi ,F)) (bicond-p (psy ,F))) 
	  (cnf (expand-sub-bicond ,F)))
	 ((or (impl-p (phi ,F)) (impl-p (psy ,F)))
	  (cnf (expand-sub-impl ,F)))
	 ,@conds))

(defun cnf (F)
  "Put form in CNF if not already."
  (cond ((literal-p F) F)
	((neg-p F) (cnf (bring-in-neg F)))
	((impl-p F) (cnf (expand-impl F)))
	((bicond-p F) (cnf (expand-bicond F)))
	((conj-p F) (cnf-cond-conj-disj F 
					   (t  (list (cnf (phi F)) ^ (cnf (psy F))))))
	((disj-p F) (cnf-cond-conj-disj F
					   ((or (conj-p (phi F)) (conj-p (psy F)))
					    (cnf (distr-disj F)))
					   ((literal-disj-p F) F)
					   (t  (cnf (list (cnf (phi F)) v (cnf (psy F)))))))
	(t (error "Incorrect input"))))

;;;; 5: CLAUSE CREATION ===============================================================================
;;;; This section contains functions that convert forms in cnf into clauses. Clauses are implemented as 
;;;; ordered sets. The sets must be orderd because the hash table used for tracking clause pairs only
;;;; accepts four built in equality predicates, precluding the use of the set equality predicate.

;;; Set of each clause produced in the proof so far.
(defvar *clauses* ())

;;; Maps two-element ordered sets of clauses to whether they have already been tried.
;;; T if they have been tried, nil otherwise.
(defvar *clause-pairs* (make-hash-table :test #'equal))

(defun clear ()
  "Clear clauses and clause pairs."
  (setf *clauses* ())
  (setf *clause-pairs* (make-hash-table :test #'equal)))

(defun make-set (L)
  "Turn L into a set by removing duplicate elements.
Removal is shallow."
  (cond ((literal-p L) (list L))
	((endp L) nil)
	((find (first L) (rest L)) (make-set (rest L)))
	(t (cons (first L) (make-set (rest L))))))

(defun set-equal (S1 S2) 
  "Return t if S1 and S2 are equal sets, nil otherwise."
  (not (set-difference S1 S2)))

(defun set-p (S)
  "Return t is S is a set, nil otherwise."
  (cond ((not (listp S)) nil)
	((endp S) t)
	((member (first S) (rest S)) nil)
	(t (set-p (rest S)))))

(defun disj-to-set (P)
  "Convert a P into a set of its literals without connectors.
Assumes P is a disjunction of literals or other disjunctions."
  (if (disj-p P)
      (union (disj-to-set (phi P)) (disj-to-set (psy P)))
      (make-set P)))

(defun set-to-clause (S)
  "Convert set S into clausal form. Sorts S and removes literals that 
are negations of eachother: e.g. if both P and (~ P) are present in S, both are removed."
  (labels
      ;; Recursively step throufh set removing both a variable and its negation if both
      ;; are present. 
      ((remove-neg-pairs (set)
	 (let ((neg (negate (first set))))
	   (cond ((endp set) nil)
		 ((member neg (rest set) :test #'equal)                     
		  (remove-neg-pairs (remove neg (rest set) :test #'equal)))
		 (t (cons (first set) (remove-neg-pairs (rest set))))))))
    (sort (remove-neg-pairs S) #'literal-lessp)))

(defun disj-to-clause (D)
  "Convert disj D into clause."
  (set-to-clause (disj-to-set D)))

(defun literal-lessp (L1 L2)
  "Return t if the string representation of literal L1 is less than L2 if both are
variables or negations. If a variable is compared to a negation, the variable
is considered less."
  (cond ((and (variable-p L1) (variable-p L2)) (string-lessp (string L1) (string L2)))
	((and (neg-p L1) (neg-p L2)) (string-lessp (string (neg-operand L1)) (string (neg-operand L2))))
	(t (neg-p L2))))

(defmacro pushnew-not-nil (item place &key (test #'equal))
  "Add ITEM to PLACE only if ITEM does not already exist in PLACE and ITEM is
not nil. TEST specifies the equality predicate used to determine if ITEM is
in PLACE."
  `(if ,item
       (pushnew ,item ,place :test ,test)))

(defun add-to-clauses (F)
  "Takes F (assumed to be in cnf), converts each conjunct into a
clause, and adds each to the clauss of the current proof if not already present."
  (cond ((conj-p F) (add-to-clauses (phi F))
	 (add-to-clauses (psy F)))
	;; Disjunctions and negations are only added to *clauses* after conversion of forms
	;; into cnf. Nil must not be added at this point as resolution would not have yet been applied
	;; to any pairs of clauses.
	((disj-p F) (pushnew-not-nil (disj-to-clause F) *clauses* :test #'equal))
	((neg-p F) (pushnew-not-nil `(,F) *clauses* :test #'equal))
	;; set-p is t when F is a clause or nil in the context of this program. 
	((set-p F) (pushnew (set-to-clause F) *clauses* :test #'equal))
	(t (pushnew (make-set F) *clauses* :test #'equal))))

;;;; 6: CLAUSE PAIRS ===========================================================================
;;;; Code in this section pertains to creating clause pairs and tracking if they have been used.
;;;; Each ordered set of clauses maps to a whether they have had resolution applied to them in
;;;; the current proof : t if they have, nil if not.

(defun clause-lessp (C1 C2)
  "Return t if the elements in C1 are literal-lessp the elements in C2. If C1 is a proper subset of C2 (meaning 
C1 is smaller than C2) C1 is less than C2."
  (cond ((set-equal C1 C2) nil)
	((endp C1) t)
	((endp C2) nil)
	((literal-lessp (first C1) (first C2)) t)
	((literal-lessp (first C2) (first C1)) nil)
	(t (clause-lessp (rest C1) (rest C2)))))

(defun make-pairs-with-clause (clause)
  "Make every combination of CLAUSE and each member of clauses
and add them to the clause pairs to resolve if not already present."
  (dolist (cl *clauses*)
    ;; tried is not used in this function, but its inclusion is necessary to use set
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

;;;; 7: RESOLUTION ==========================================================================================
;;;; This section contains code to resolve two clauses. The resolution algorithm takes two clauses,
;;;; C1 and C2, and checks if the negation of an element x in C1 is a member of C2. If this is the case,
;;;; the union of the two clauses, without x or its negation, is produced.

(defun resolve (C1 C2)
  "Resolve clauses C1 and C2. Returns multiple values. First value
is the new clause, if one can be made. The second value returns t if the clauses resolve,
nil otherwise."
  (dolist (literal C1 (values nil nil))
    (if (member (negate literal) C2 :test #'equal)
	(if (and (= (length C1) 1) (= (length C2) 1))
	    (return (values nil t))
	    (return (values (union (remove literal C1 :test #'equal) 
				   (remove (negate literal) C2 :test #'equal))
			    t))))))

(defun tautology-p (P)
  "Return t if P is a tautology, nil otherwise."
  (clear)
  (add-to-clauses (cnf (weak-negate P)))
  (make-clause-pairs)
  
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

;;;; 8: TESTS ===========================================================================================
(defvar t1 'P)
(defvar t2 '(~ ~ ~ P))
(defvar t3 '(P v (~ P)))
(defvar t4 '((P v Q) -> P))
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
