(defstruct v
  type value)

(defstruct tlthread
  run?
  PF ;; point to running closure
  PC
  PS
  PSB
  PCL ;; point to closure array
  VAL
  ARI
  FUNC
  ARGN ;; Arguments Array
  STACK ;; Stack Array
  )

(defparameter *support-argument-number* 20)

(defun init-tlthread ()
  (let ((tr (make-tlthread)))
    (setf (tlthread-pc tr) 0)
    (setf (tlthread-ps tr) 0)
    (setf (tlthread-psb tr) 0)
    (setf (tlthread-pcl tr) 0)
    (setf (tlthread-val tr) (make-v :type 0 :value 0))
    (setf (tlthread-ari tr) 0)
    (setf (tlthread-func tr) nil)
    (setf (tlthread-argn tr) (make-array *support-argument-number*))
    (setf (tlthread-stack tr) (make-array 10000 :adjustable t))
    (dotimes (i *support-argument-number*)
      (setf (aref (tlthread-argn tr) i) (make-v :type 0 :value 0)))
    tr))

(defstruct vm-function
  arity
  stack-length
  closure-map ;; a map of number
  closure-ref-c-map
  body)

(defstruct vm-closure
  function ;; vm-function structure
  ref-map)

(defstruct closure-array
  upper
  map)

(defstruct closure-ref
  closure-array
  n)

(defstruct closure-ref-c
  level n)

(defun vm-fix-closure (vm-function tlthread)
  (let* ((cl (make-vm-closure :function vm-function))
	 (upper-array (tlthread-pcl tlthread))
	 (ref-c-map (vm-function-closure-ref-c-map
		     vm-function))
	 (ref-map (make-array (vector-len ref-c-map))))
    (labels ((find-closure-array (level)
	       (labels ((finder (level current-array)
			  (if (= level 0)
			      current-array
			      (finder (1- level)
				      (closure-array-upper
				       current-array)))))
		 (finder level upper-array))))
      (dotimes (i (vector-len ref-c-map))
	(let ((ref-c (aref ref-c-map i)))
	  (setf (aref ref-map i)
		(make-closure-ref
		 :closure-array (find-closure-array
				 (closure-ref-c-level ref-c))
		 :n (closure-ref-c-n ref-c)))))
      (setf (vm-closure-ref-map cl) ref-map)
      cl)))
	     
(progn
  (defvar *ins-table* nil)
  (setf *ins-table* (make-array 200))
  (defvar *ins-table-index* 0)
  (setf *ins-table-index* 0)

  (defvar *type-table* nil)
  (setf *type-table* (make-array 20))
  (defvar *type-table-index* 0)
  (setf *type-table-index* 0)

  (defvar *code-symbol-table* nil)
  (setf *code-symbol-table* (make-hash-table))
  (defvar *symbol-code-table* nil)
  (setf *symbol-code-table* (make-hash-table))
  (defvar *symbol-table-index* 0)
  (setf *symbol-table-index* 0)
  (defvar *symbol-table-lock* nil)
  ;; lock not implemented.
  )

(defun vm-intern-symbol (sym)
  "SYM -> CODE"
  (let ((find (gethash sym *symbol-code-table*)))
    (if find
	find
	(let ((code *symbol-table-index*))
	  (setf (gethash sym *symbol-code-table*) code)
	  (setf (gethash code *code-symbol-table*) sym)
	  (incf *symbol-table-index*)
	  code))))

(defun vm-export-symbol (code)
  (let ((find (gethash code *code-symbol-table*)))
    (if find find
	(error "vm-export-symbol: Unknown symbol code"))))

(progn
  (vm-intern-symbol 't)
  (vm-intern-symbol 'nil)
  (vm-intern-symbol 'a)
  (vm-intern-symbol 'b)
  (vm-intern-symbol 'c))
		   
(defun make-type (name)
  (setf (aref *type-table* *type-table-index*) name)
  (incf *type-table-index*))

(defun code-to-type (code)
  (let ((type (aref *type-table* code)))
    (if (symbolp type)
	type
	(error "CODE-TO-TYPE: Unknown type"))))

(defun type-to-code (name)
  (let ((result nil))
    (dotimes (i 20)
      (let ((type (aref *type-table* i)))
	(if (eq name type)
	    (progn (setf result i)
		   (return))
	    nil)))
    (if result
	result
	(error "TYPE-TO-CODE: Unknown type"))))

(progn
  (make-type 'closure)
  (make-type 'integer)
  (make-type 'cons)
  (make-type 'symbol)
  (make-type 'continuation))

(defun ins-arg (tlthread n)
  (let ((function (tlthread-pf tlthread))
	(shift (tlthread-pc tlthread)))
    (aref (vm-function-body function) (+ shift n 1))))

(defmacro copy-value> (a b)
  `(progn
     (setf (v-type ,b) (v-type ,a))
     (setf (v-value ,b) (v-value ,a))))

(defun incf-stack (tlthread &optional (delta 1))
  (let ((new-ps (incf (tlthread-ps tlthread) delta)))
    (if (>= new-ps (vector-len (tlthread-stack tlthread)))
	(adjust-array (tlthread-stack tlthread)
		      (floor (* 1.6
				(vector-len
				 (tlthread-stack tlthread)))))
	nil)
    new-ps))

(defun push-single (register tlthread)
  (let ((index (tlthread-ps tlthread)))
    (setf (aref (tlthread-stack tlthread) index) register)
    (incf-stack tlthread)))

(defmacro pop-single (register tlthread)
  `(let ((index (decf (tlthread-ps ,tlthread))))
     (setf ,register (aref (tlthread-stack ,tlthread) index))
     index))

(defun push-value (value tlthread)
  (let ((index (tlthread-ps tlthread))
	(v (make-v :type (v-type value)
		   :value (v-value value))))
    (setf (aref (tlthread-stack tlthread) index) v)
    (incf-stack tlthread)))

(defmacro pop-value (vg tlthread)
  `(let* ((index (decf (tlthread-ps ,tlthread)))
	  (v (aref (tlthread-stack ,tlthread) index)))
     (setf (v-type ,vg) (v-type v))
     (setf (v-value ,vg) (v-value v))
     index))

(defstruct instruction
  code
  name
  doc
  lambda)

(defmacro defins (name doc &rest body)
  `(let ((new-instruction
	  (make-instruction :code *ins-table-index*
			    :name (quote ,name)
			    :doc ,doc
			    :lambda (lambda (tlt)
				      ,@body))))
     (setf (aref *ins-table* *ins-table-index*) new-instruction)
     (incf *ins-table-index*)))

(defun code-to-ins (code)
  (instruction-name (aref *ins-table* code)))

(defun ins-to-code (name)
  (dotimes (i (vector-len *ins-table*))
    (let ((ins (aref *ins-table* i)))
      (if (instruction-p ins)
	  (if (eq (instruction-name ins) name)
	      (return i)
	      nil)
	  (error "INS-TO-CODE: Can NOT find instruction code.")))))

(defun print-instruction-set (&optional docp)
  (format t "---- INSTRUCTION SET ----~%")
  (dotimes (i 200)
    (let ((ins (aref *ins-table* i)))
      (if (instruction-p ins)
	  (progn (format t "* ~A, ~A~%"
			 (instruction-code ins)
			 (instruction-name ins))
		 (if docp
		     (format t "~A~%~%" (instruction-doc ins))))
	  (return)))))

(defmacro vm-is-type (target type)
  "VM-IS-TYPE
  the argument TYPE do not need quote."
  (let ((ct (type-to-code type)))
    `(let ((tt (v-type ,target)))
       (= tt ,ct))))

(progn
  (setf *ins-table* (make-array 200))
  (setf *ins-table-index* 0)
  
  (defins HALT
      "HALT -
       Stop interpreting bytecode."
    (setf (tlthread-run? tlt) 'nop))

  (defins PUSH
       "PUSH -. (VAL)
       VAL -> PS[]"
    (push-value (tlthread-val tlt) tlt))

  (defins POP
      "POP -. (VAL)
       PS[] -> VAL"
    (pop-value (tlthread-val tlt) tlt))

  (defins GET-GLOBAL
      "GET-GLOBAL -. (VAL)
       get var from global a list
       VAL.SYMBOL -> global alist reference -> VAL.value"
    tlt
    'not-implemented-yet)

  (defins SET-FUNC
       "SET-FUNC -. (VAL FUNC)
       (val VAL) -> FUNC"
    (if (= (v-type (tlthread-val tlt)) #.(type-to-code 'closure))
	(setf (tlthread-func tlt) (v-value (tlthread-val tlt)))
	(error "VM: SET-FUNC: not a function")))

  (defins SET-ARGN
      "SET-ARGN N -. (VAL ARGN)
       VAL -> ARG(N)"
    (let ((target (ins-arg tlt 0)))
      (copy-value> (tlthread-val tlt)
		   (aref (tlthread-argn tlt) target))))

  (defins GET-ARGN
      "GET-ARGN N -. (VAL ARGN)
       stack(ARGN) -> VAL
       Registers ARGX can be covered, so we can only get these value
       from stack."
    (let ((target (ins-arg tlt 0))
	  (psb (tlthread-psb tlt)))
      (copy-value> (aref (tlthread-stack tlt) (+ psb 1 target))
		   (tlthread-val tlt))))

  (defins SET-ARI
      "SET-ARI N -. (ARI)
       N -> ARI"
    (setf (tlthread-ari tlt) (ins-arg tlt 0)))

  (defins CALL
      "CALL -. (FUNC ARI ARGN)
       FUNC -> PF
       result -> VAL

       Call a closure"
    (push-single (tlthread-ps tlt) tlt)
    (push-single (tlthread-psb tlt) tlt)
    (push-single (tlthread-pc tlt) tlt)
    (push-single (tlthread-pcl tlt) tlt)
    (push-single (tlthread-pf tlt) tlt)

    (let* ((closure (tlthread-func tlt))
	   (func-c (vm-closure-function closure)))
      (if (= (tlthread-ari tlt) (vm-function-arity func-c))
	  t
	  (error "VM: CALL: Error arity."))

      (let ((psb (tlthread-ps tlt)))
	(setf (tlthread-psb tlt) psb)
	(setf (aref (tlthread-stack tlt) psb) closure)

	;; copy ARGN array to stack
	(let ((stack-length (vm-function-stack-length func-c)))
	  ;; use new PS
	  (setf (tlthread-ps tlt) (+ 1 psb stack-length))

	  (dotimes (i stack-length)
	    (copy-value> (aref (tlthread-argn tlt) i)
			 (aref (tlthread-stack tlt)
			       (+ psb 1 i))))

	  (let* ((closure-map (vm-function-closure-map func-c))
		 (closure-length (vector-len closure-map))
		 (new-array-map (make-array closure-length))
		 (new-closure-array
		  (make-closure-array :upper (tlthread-pcl tlt)
				      :map new-array-map)))
	    ;; copy to closure space from stack
	    (dotimes (i closure-length)
	      (copy-value>
	       (aref (tlthread-stack tlt)
		     (+ psb
			(aref (vm-function-closure-map func-c) i)))
	       (aref new-array-map i)))

	    ;; use new closure-array
	    (setf (tlthread-pcl tlt) new-closure-array))

	  (setf (tlthread-pc tlt) 0)))))

  (defins RETURN
      "RETURN -.
       Abandon current stack frame, and use after result is in *VAL*."
    (setf (tlthread-ps tlt) (tlthread-psb tlt))
    (pop-single (tlthread-pf tlt) tlt)
    (pop-single (tlthread-pcl tlt) tlt)
    (pop-single (tlthread-pc tlt) tlt)
    (pop-single (tlthread-psb tlt) tlt)
    (pop-single (tlthread-ps tlt) tlt))
	  
  (defins CONSTANT
      "CONSTANT TYPE VALUE -. (VAL)
       instant value."
    (setf (v-type (tlthread-val tlt)) (ins-arg tlt 0))
    (setf (v-value (tlthread-val tlt)) (ins-arg tlt 1)))

  (defins GET-STACK
      "GET-STACK SHIFT -. (VAL)
       STACK[PSB+SHIFT] -> VAL"
    (copy-value> (aref (tlthread-stack tlt)
		       (+ (tlthread-psb tlt)
			  (ins-arg tlt 0)))
		 (tlthread-val tlt)))

  (defins GET-CLOSURE-LOCAL
      "GET-CLOSURE-LOCAL SHIFT, VAL
       get local closure value by PCL[SHIFT]."
    (let ((array (closure-array-map (tlthread-pcl tlt)))
	  (target (ins-arg tlt 0)))
      (copy-value> (aref array target)
		   (tlthread-val tlt))))

  (defins SET-CLOSURE-LOCAL
      "SET-CLOSURE-LOCAL SHIFT, VAL
       set local closure value by PCL[SHIFT]."
    (let ((array (closure-array-map (tlthread-pcl tlt)))
	  (target (ins-arg tlt 0)))
      (copy-value> (tlthread-val tlt)
		   (aref array target))))

  (defins GET-CLOSURE
      "GET-CLOSURE SHIFT, VAL
       get closure value by vm-closure.ref-map[SHIFT]"
    (let* ((closure (tlthread-pf tlt))
	   (closure-ref-map (vm-closure-ref-map closure))
	   (ref (aref closure-ref-map (ins-arg tlt 0)))
	   (closure-array (closure-ref-closure-array ref))
	   (n (closure-ref-n ref))
	   (closure-array-map (closure-array-map closure-array)))
      (copy-value> (aref closure-array-map n)
		   (tlthread-val tlt))))

  (defins SET-CLOSURE
      "SET-CLOSURE SHIFT, VAL
       Set closure value by vm-closure.ref-map[SHIFT]"
    (let* ((closure (tlthread-pf tlt))
	   (closure-ref-map (vm-closure-ref-map closure))
	   (ref (aref closure-ref-map (ins-arg tlt 0)))
	   (closure-array (closure-ref-closure-array ref))
	   (n (closure-ref-n ref))
	   (closure-array-map (closure-array-map closure-array)))
      (copy-value> (tlthread-val tlt)
		   (aref closure-array-map n))))

  (defins FIX-CLOSURE
      "FIX-CLOSURE FUNCTION, VAL
      make a vm-closure structure, contains function and ref-map."
    (let* ((function (ins-arg tlt 0))
	   (new-closure (vm-fix-closure function tlt)))
      (setf (v-type (tlthread-val tlt)) #.(type-to-code 'closure))
      (setf (v-value (tlthread-val tlt)) new-closure)))
  
  (defins ADD2
      "ADD2 -, ARG1 + ARG2 -> VAL"
    (let ((v1 (aref (tlthread-argn tlt) 0))
	  (v2 (aref (tlthread-argn tlt) 1))
	  (val (tlthread-val tlt)))
      (if (and (vm-is-type v1 integer)
	       (vm-is-type v2 integer))
	  (progn
	    (setf (v-type val) #.(type-to-code 'integer))
	    (setf (v-value val)
		  (+ (v-value v1) (v-value v2))))
	  (error "VM: ADD2: TYPE-ERROR"))))

  (defins SUB2
      "SUB2 -, ARG1 - ARG2 -> VAL"
    (let ((v1 (aref (tlthread-argn tlt) 0))
	  (v2 (aref (tlthread-argn tlt) 1))
	  (val (tlthread-val tlt)))
      (if (and (vm-is-type v1 integer)
	       (vm-is-type v2 integer))
	  (progn
	    (setf (v-type val) #.(type-to-code 'integer))
	    (setf (v-value val)
		  (- (v-value v1) (v-value v2))))
	  (error "VM: ADD2: TYPE-ERROR"))))

  (defins NEQ
      "NEQ -. ARGN1 ARGN2
       number equal"
      (let ((v1 (aref (tlthread-argn tlt) 0))
	    (v2 (aref (tlthread-argn tlt) 1))
	    (val (tlthread-val tlt)))
	(if (and (vm-is-type v1 integer)
		 (vm-is-type v2 integer))
	    (progn
	      (setf (v-type val) #.(type-to-code 'symbol))
	      (setf (v-value val)
		    (if (= (v-value v1) (v-value v2))
			#.(vm-intern-symbol 't)
			#.(vm-intern-symbol 'nil))))
	    (error "VM: NEQ: TYPE-ERROR"))))

  (defins JMPF
       "JMPF SHIFT -. (VAL)
       Jump when get a `nil'."
    (let* ((shift (ins-arg tlt 0)))
      (if (and (= #.(type-to-code 'symbol)
		  (v-type (tlthread-val tlt)))
	       (= #.(vm-intern-symbol 'nil)
		  (v-value (tlthread-val tlt))))
	  (setf (tlthread-pc tlt) (* 4 shift))
	  nil)))

  (defins JMPT
      "JMPT SHIFT -. (VAL)
       Jump when not get a `nil'."
    (let* ((shift (ins-arg tlt 0)))
      (if (not (and (= #.(type-to-code 'symbol)
		       (v-type (tlthread-val tlt)))
		    (= #.(vm-intern-symbol 'nil)
		       (v-value (tlthread-val tlt)))))
	  (setf (tlthread-pc tlt) (* 4 shift))
	  nil)))

  (defins SGOTO
      "SGOTO SHIFT -. (_)
       Jump in current function"
    (let* ((shift (ins-arg tlt 0)))
      (setf (tlthread-pc tlt) (* 4 shift)))))
