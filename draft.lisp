(let ((v (make-v :type (type-to-code 'integer)
		 :value 1)))
  (vm-is-type v integer))

(macroexpand-1
 '(defins NEQ
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
	 (error "VM: NEQ: TYPE-ERROR")))))

(macroexpand-1
   '(defins SGOTO
      "SGOTO SHIFT -. (_)
       Jump in current function"
    (let* ((shift (ins-arg tlthread 0)))
      (setf (tlthread-pc tlt) (* 4 shift)))))
