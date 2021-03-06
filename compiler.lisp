;;;; =============== COMPILER ===================

;;;; struct: vari
;; name: symbol
;; type: stack, closure, global
(defstruct vari
  name
  type
  n)

(defstruct ref
  vari
  level)

(defun extend-c (env-stack varnames)
  (let ((new-stack nil))
    (dolist (v varnames)
      (push (make-vari :name v
		       :type 'stack
		       :n nil)
	    new-stack))
    (cons (reverse new-stack) env-stack)))

(defun lookup (id env-stack)
  (let ((level 0)
	(vari  nil))
    (block exit
      (dolist (frame env-stack)
	(dolist (v frame)
	  (if (eq (vari-name v) id)
	      (progn (if (= 0 level)
			 nil
			 (setf (vari-type v) 'closure))
		     (setf vari v)
		     (return-from exit))
	      nil))
	(incf level)))
    (if vari
	(make-ref :vari vari :level level)
	(let ((global (gethash id *global-env*)))
	  (if global
	      (make-ref :vari global :level 0)
	      (error (format t "Compiler: lookup: id `~A' not found"
			     id)))))))

(defstruct func-intermediate
  artiy
  closure-map
  env-stack
  body-intermediate
  body-assembly)

(defun boolp (e)
  (or (eq e t)
      (eq e nil)))

(defun self-quote? (e)
  (or (numberp e) (boolp e)))

(defun compiler (e env-stack tailp) e env-stack tailp)
(defun compile-list (e env-stack tailp) e env-stack tailp)
(defun compile-lambda (e env-stack tailp) e env-stack tailp)

(defun compile-lambda (e env-stack tailp)
  tailp
  (let* ((f (make-func-intermediate))
	 (varnames (cadr e))
	 (body (cddr e))
	 (env-stack (extend-c env-stack varnames))
	 (env-top (car env-stack))
	 (closure-list nil)
	 (compiled-body (cons 'begin
			      (compile-list body env-stack t))))
    
    (setf (func-intermediate-artiy f) (length varnames))
    
    (let ((c 0))
      (dolist (v env-top)
	(if (eq (vari-type v) 'closure)
	    (progn (setf (vari-n v) c)
		   (push c closure-list)
		   (incf c)))))
    
    (setf (func-intermediate-closure-map f)
	  (let ((i 0)
		(c 0)
		(m (make-array (length closure-list))))
	    (dolist (v env-top)
	      (if (eq (vari-type v) 'closure)
		  (progn (setf (aref m c) i)
			 (incf c))
		  nil)
	      (incf i))
	    m))

    ;; what the hell is this???
    (let ((i 0))
      (dolist (v env-top)
	(if (not (eq 'closure (vari-type v)))
	    (setf (vari-n v) i)
	    nil)
	(incf i)))

    (setf (func-intermediate-env-stack f) env-stack)
    (setf (func-intermediate-body-intermediate f) compiled-body)
    f))

(defun compile-list (e env-stack tailp)
  (if (cdr e)
      (cons (compiler (car e) env-stack nil)
	    (compile-list (cdr e) env-stack tailp))
      (cons (compiler (car e) env-stack tailp))))

(defun compiler (e env-stack tailp)
  (if (atom e)
      (cond ((self-quote? e) `(constant ,e))
	    ((symbolp e) (lookup e env-stack)))
      (case (car e)
	((quote) `(constant ,e))
	((if) (if (not (= 4 (length e)))
		  (error (format nil "Compiler: malformed IF ~A" e))
		  (list 'if
			(compiler (cadr e) env-stack nil)
			(compiler (caddr e) env-stack tailp)
			(compiler (cadddr e) env-stack tailp))))
	((begin) (cons 'begin
		       (compile-list (cdr e) env-stack tailp)))
	((set!) (list 'set!
		      (lookup (cadr e) env-stack)
		      (compiler (caddr e) env-stack nil)))
	((lambda) (compile-lambda e env-stack nil))
	(t (list (if tailp 'tail-call 'call)
		 (compiler (car e) env-stack nil)
		 (compile-list (cdr e) env-stack nil))))))
