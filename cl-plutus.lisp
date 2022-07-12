;;;; cl-plutus.lisp
;; reference: https://github.com/runtimeverification/plutus-core-semantics

(in-package #:cl-plutus)

(declaim (optimize safety debug))

(defgeneric emit-plutus (ast)
  (:documentation "Emit the UPLC source code from the given `ast'"))
(defgeneric eval-plutus (env ast)
  (:documentation "Eval the plutus `ast' in the context `env'"))
(defgeneric to-plutus (v)
  (:documentation "Convert the lisp value `v' to a plutus value"))
(defgeneric from-plutus (v)
  (:documentation "Convert the primitive plutus value `v' to a lisp value"))

(defun intvector< (a b)
  (notevery #'null (map 'vector #'< a b)))

(defun intvector<= (a b)
  (notevery #'null (map 'vector #'<= a b)))

(defun eval-typecheck-plutus (env v type)
  (let ((evaled (eval-plutus env v)))
    (if (eql (type-of evaled) type)
        evaled
        (error 'type-error :datum v :expected-type type))))

(defun apply-to-plutus (lisp-function &rest plutus-args)
  (to-plutus (apply lisp-function (loop for a in plutus-args collecting (from-plutus a)))))

(define-condition plutus-error-signal (error) ())

(define-condition plutus-head-signal (error) ())

(define-condition plutus-tail-signal (error) ())

(defmacro defun-builtin-plutus (name args &body body)
  "Create a class named NAME, a helper ast building function named NAME which stores (LENGTH ARGS) slots,
and an EVAL-PLUTUS method implementation for that class from the BODY.

NAME is a symbol.
ARGS is a list of symbols or (SYMBOL TYPE) lists where TYPE is a plutus type name.
BODY is provided with an implicit argument ENV."
  (labels ((slot-name (class-name arg-name)
             (intern (concatenate 'string (symbol-name class-name) "-" (symbol-name arg-name))))
           (arg->slot (class-name arg-name)
             (list arg-name
                   :initarg (make-keyword (symbol-name arg-name))
                   :accessor (slot-name class-name arg-name)))
           (args->make-instance-plist (args)
             (apply #'append (loop for a in args collecting (list (make-keyword (symbol-name a)) a))))
           (arg->evaled-typechecked (class-object-symbol class-name arg)
             (if (consp arg)
                 `(,(car arg)
                   (eval-typecheck-plutus env (,(slot-name class-name (car arg)) ,class-object-symbol) (quote ,(cadr arg))))
                 `(,arg
                   (eval-plutus env (,(slot-name class-name arg) ,class-object-symbol))))))
    (let* ((arg-names (loop for a in args collecting (if (consp a) (car a) a)))
           (slots (loop for a in arg-names collecting (arg->slot name a)))
           (make-instance-args (args->make-instance-plist arg-names))
           (f (gensym "f"))
           (let-evaled-args (loop for a in args collecting (arg->evaled-typechecked f name a))))
      `(progn
         (defclass ,name () ,slots)
         (defun ,name ,arg-names
           (make-instance (quote ,name) ,@make-instance-args))
         (defmethod eval-plutus (env (,f ,name))
           (let ,let-evaled-args
             ,@body))))))

(defmacro defast-plutus (name args &body body)
  "Create a class named NAME, a helper ast building function named NAME which stores (LENGTH ARGS) slots,
and an EVAL-PLUTUS method implementation for that class from the BODY.

NAME is a symbol.
ARGS is a list of symbols.
BODY is provided with implicit arguments ENV and SELF."
  (labels ((slot-name (class-name arg-name)
             (intern (concatenate 'string (symbol-name class-name) "-" (symbol-name arg-name))))
           (arg->slot (class-name arg-name)
             (list arg-name
                   :initarg (make-keyword (symbol-name arg-name))
                   :accessor (slot-name class-name arg-name)))
           (args->make-instance-plist (args)
             (apply #'append (loop for a in args collecting (list (make-keyword (symbol-name a)) a))))
           (arg->not-evaled (class-object-symbol class-name arg)
             `(,arg (,(slot-name class-name arg) ,class-object-symbol))))
    (let* ((arg-names (loop for a in args collecting (if (consp a) (car a) a)))
           (slots (loop for a in arg-names collecting (arg->slot name a)))
           (make-instance-args (args->make-instance-plist arg-names))
           (let-args (loop for a in args collecting (arg->not-evaled 'self name a))))
      `(progn
         (defclass ,name () ,slots)
         (defun ,name ,arg-names
           (make-instance (quote ,name) ,@make-instance-args))
         (defmethod eval-plutus (env (self ,name))
           (let ,let-args
             (declare (ignorable ,@(loop for e in let-args collecting (car e))))
             ,@body))))))

(defast-plutus plutus-bool (value)
  self)

(defast-plutus plutus-integer (value)
  self)

(defast-plutus plutus-pair (car cdr)
  (plutus-pair (eval-plutus env car) (eval-plutus env cdr)))

(defast-plutus plutus-list (value)
  (plutus-list (loop for e in value collecting (eval-plutus env e))))

(defast-plutus plutus-map (value)
  (plutus-map (loop for e in value collecting (eval-plutus env e))))

(defast-plutus plutus-bytestring (value)
  self)

(defast-plutus plutus-string (value)
  self)

(defast-plutus plutus-unit ()
  self)

(defast-plutus plutus-lambda (name term)
  self)

(defun-builtin-plutus plutus-apply ((lam plutus-lambda) arg)
  (eval-plutus (cons (cons (plutus-lambda-name lam) arg) env) (plutus-lambda-term lam)))

(defmacro p-let (bindings &body body)
  (unless (= (length body) 1)
    (error 'program-error))
  (loop for (name term) in (reverse bindings)
        with result = (car body)
        with id-bindings = ()
        do
           (setf result `(plutus-apply (plutus-lambda (quote ,name) ,result) ,term))
           (setf id-bindings (cons `(,name (to-plutus (quote ,name))) id-bindings))
        finally (return `(let ,id-bindings ,result))))

(defast-plutus plutus-delay (value)
  self)

(defast-plutus plutus-id (symbol)
  (let ((looked-up (assoc symbol env)))
    (if looked-up
        (cdr looked-up)
        (error 'unbound-variable :name symbol))))

(defun-builtin-plutus plutus-add-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'+ a b))

(defun p+ (&rest args)
  (reduce #'plutus-add-integer args))

(defun-builtin-plutus plutus-multiply-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'* a b))

(defun p* (&rest args)
  (reduce #'plutus-multiply-integer args))

(defun-builtin-plutus plutus-subtract-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'- a b))

(defun p- (&rest args)
  (reduce #'plutus-subtract-integer args))

(defun-builtin-plutus plutus-divide-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'floor a b))

(defun p/ (&rest args)
  (reduce #'plutus-divide-integer args))

(defun-builtin-plutus plutus-mod-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'mod a b))

(defun p-mod (&rest args)
  (reduce #'plutus-mod-integer args))

(defun-builtin-plutus plutus-quotient-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'truncate a b))

(defun p-quot (&rest args)
  (reduce #'plutus-quotient-integer args))

(defun-builtin-plutus plutus-remainder-integer ((a plutus-integer) (b plutus-integer))
  (to-plutus (nth-value 1 (truncate (from-plutus a) (from-plutus b)))))

(defun p-rem (&rest args)
  (reduce #'plutus-remainder-integer args))

(defun-builtin-plutus plutus-less-than-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'< a b))

(defun-builtin-plutus plutus-less-than-equals-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'<= a b))

(defun-builtin-plutus plutus-equals-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'eql a b))

(defun-builtin-plutus plutus-force ((a plutus-delay))
  (eval-plutus env (plutus-delay-value a)))

(defun-builtin-plutus plutus-encode-utf8 ((a plutus-string))
  (to-plutus (sb-ext:string-to-octets (from-plutus a) :external-format :utf-8)))

(defun-builtin-plutus plutus-decode-utf8 ((a plutus-bytestring))
  (to-plutus (sb-ext:octets-to-string (from-plutus a) :external-format :utf-8)))

(defun-builtin-plutus plutus-append-string ((a plutus-string) (b plutus-string))
  (to-plutus (concatenate 'string (from-plutus a) (from-plutus b))))

(defun-builtin-plutus plutus-equals-string ((a plutus-string) (b plutus-string))
  (apply-to-plutus #'equal a b))

(defun-builtin-plutus plutus-append-bytestring ((a plutus-bytestring) (b plutus-bytestring))
  (to-plutus (concatenate 'vector (from-plutus a) (from-plutus b))))

(defun-builtin-plutus plutus-cons-bytestring ((a plutus-integer) (b plutus-bytestring))
  (to-plutus (concatenate 'vector (vector (from-plutus a)) (from-plutus b))))

(defun-builtin-plutus plutus-slice-bytestring ((a plutus-integer) (b plutus-integer) (c plutus-bytestring))
  (to-plutus (subseq (from-plutus c) (from-plutus a) (from-plutus b))))

(defun-builtin-plutus plutus-length-of-bytestring ((a plutus-bytestring))
  (apply-to-plutus #'length a))

(defun-builtin-plutus plutus-index-bytestring ((a plutus-bytestring) (b plutus-integer))
  (apply-to-plutus #'elt a b))

(defun-builtin-plutus plutus-equals-bytestring ((a plutus-bytestring) (b plutus-bytestring))
  (apply-to-plutus #'equalp a b))

(defun-builtin-plutus plutus-less-than-bytestring ((a plutus-bytestring) (b plutus-bytestring))
  (apply-to-plutus #'intvector< a b))

(defun-builtin-plutus plutus-less-than-equals-bytestring ((a plutus-bytestring) (b plutus-bytestring))
  (apply-to-plutus #'intvector<= a b))

(defun-builtin-plutus plutus-sha3-256 ((a plutus-bytestring))
  (to-plutus (ironclad:digest-sequence :sha3 (from-plutus a))))

(defun-builtin-plutus plutus-sha2-256 ((a plutus-bytestring))
  (to-plutus (ironclad:digest-sequence :sha256 (from-plutus a))))

(defun-builtin-plutus plutus-blake2b-256 ((a plutus-bytestring))
  (error "TODO"))

(defun-builtin-plutus plutus-verify-signature ((a plutus-bytestring) (b plutus-bytestring) (c plutus-bytestring))
  (error "TODO"))

(defun-builtin-plutus plutus-fst-pair ((a plutus-pair))
  (plutus-pair-car a))

(defun-builtin-plutus plutus-snd-pair ((a plutus-pair))
  (plutus-pair-cdr a))

(defun-builtin-plutus plutus-choose-list ((a plutus-list) b c)
  (if (null (from-plutus a))
      b
      c))

(defun-builtin-plutus plutus-mk-cons (a (b plutus-list))
  (apply-to-plutus #'cons a b))

(defun-builtin-plutus plutus-head-list ((a plutus-list))
  (if (from-plutus a)
      (to-plutus (car (from-plutus a)))
      (error 'plutus-head-signal)))

(defun-builtin-plutus plutus-tail-list (a)
  (if (from-plutus a)
      (let ((r (cdr (from-plutus a))))
        (if r r (make-instance 'plutus-list :value nil)))
      (error 'plutus-tail-signal)))

(defun-builtin-plutus plutus-null-list ((a plutus-list))
  (apply-to-plutus #'null a))

(defun-builtin-plutus plutus-if-then-else ((a plutus-bool) b c)
  (if (from-plutus a) b c))

(defun-builtin-plutus plutus-choose-unit ((a plutus-unit) b)
  (declare (ignore a))
  b)

(defun-builtin-plutus plutus-error ()
  (error 'plutus-error-signal))

(defun-builtin-plutus plutus-trace ((a plutus-string) b)
  (format t "PLUTUS: ~a~%" (from-plutus a))
  b)

(defun-builtin-plutus plutus-choose-data (a p m l i b)
  (case (type-of a)
    (plutus-pair p)
    (plutus-map m)
    (plutus-list l)
    (plutus-integer i)
    (plutus-bool b)))

(defun-builtin-plutus plutus-constr-data (a b)
  (error "TODO"))

(defun-builtin-plutus plutus-map-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-list-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-i-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-b-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-un-constr-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-un-map-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-un-list-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-un-i-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-un-b-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-equals-data (a b)
  (error "TODO"))

(defun-builtin-plutus plutus-mk-pair-data (a b)
  (error "TODO"))

(defun-builtin-plutus plutus-mk-nil-data (a)
  (error "TODO"))

(defun-builtin-plutus plutus-mk-nil-pair-data (a)
  (error "TODO"))

;; utils
(defun alistp (alist)
  (and (listp alist)
       (every #'consp alist)))

;; to-plutus implementations:
(defmethod to-plutus ((b (eql t)))
  (plutus-bool t))

(defmethod to-plutus ((b (eql nil)))
  (plutus-bool nil))

(defmethod to-plutus ((i integer))
  (plutus-integer i))

(defmethod to-plutus ((p cons))
  ;; Possible forms:
  ;; alist ((a . b) (c . d) ...) -> plutus-map
  ;; cons  (a . b)               -> plutus-pair
  ;; list  (a b c ...)           -> plutus-list
  (cond
    ((alistp p)
     (plutus-map (loop for v in p collecting (to-plutus v))))
    ((and (not (consp (cdr p))) (not (null (cdr p))))
     (plutus-pair (to-plutus (car p)) (to-plutus (cdr p))))
    (t
     (plutus-list (loop for v in p collecting (to-plutus v))))))

(defmethod to-plutus ((u (eql 'unit)))
  (plutus-unit))

(defmethod to-plutus ((b array))
  (plutus-bytestring (make-array (length b)
                                 :element-type '(unsigned-byte 8)
                                 :initial-contents b)))

(defmethod to-plutus ((s string))
  (plutus-string s))

(defmethod to-plutus ((s symbol))
  (plutus-id s))

;; from-plutus implementations
(defmethod from-plutus ((b plutus-bool))
  (plutus-bool-value b))
(defmethod from-plutus ((i plutus-integer))
  (plutus-integer-value i))
(defmethod from-plutus ((p plutus-pair))
  (cons (plutus-pair-car p) (plutus-pair-cdr p)))
(defmethod from-plutus ((l plutus-list))
  (loop for e in (plutus-list-value l) collecting (from-plutus e)))
(defmethod from-plutus ((m plutus-map))
  (loop for p in (plutus-map-value m)
        collecting (cons (from-plutus (plutus-pair-car p)) (from-plutus (plutus-pair-cdr p)))))
(defmethod from-plutus ((u plutus-unit))
  'unit)
(defmethod from-plutus ((b plutus-bytestring))
  (plutus-bytestring-value b))
(defmethod from-plutus ((s plutus-string))
  (plutus-string-value s))
