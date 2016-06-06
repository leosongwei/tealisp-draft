(defvar *debug-linearlizer* nil)
(setf *debug-linearlizer* nil)

(defstruct ba
  a i)

(defun gen-ba ()
  (make-ba :a (make-array
	       10
	       :initial-element 0
	       :adjustable t)
	   :i 0))
			  
(defun add-to-ba (ba e)
  (let ((length (array-dimension (ba-a ba) 0)))
    (if (> (/ (ba-i ba) length) 0.9)
	(adjust-array (ba-a ba) (floor (* 1.6 length)))
	nil)
    (setf (aref (ba-a ba) (ba-i ba)) e)
    (incf (ba-i ba)))
  ba)

(defun ba2list (ba)
  (let ((r nil))
    (dotimes (i (ba-i ba))
      (push (aref (ba-a ba) i) r))
    (reverse r)))

(defun linearlize (ba body)
  )

(defun linearlizerf (fi)
  (let* ((body-intermediate
	  (func-intermediate-body-intermediate fi))
	 (ba (gen-ba)))
    (linearlize ba body-intermediate)
    (setf (func-intermediate-body-
