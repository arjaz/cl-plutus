;;;; cl-plutus.lisp
;; reference: https://github.com/runtimeverification/plutus-core-semantics

(in-package #:cl-plutus)

(declaim (optimize safety debug))

(defgeneric emit-plutus (ast)
  (:documentation "Emit the UPLC source code from the given `ast'"))
;; Can we have that automatically derived with a cool macro?
(defgeneric eval-plutus (env ast)
  (:documentation "Eval the plutus `ast' in the context `env'"))
(defgeneric to-plutus (v)
  (:documentation "Convert the lisp value `v' to a plutus value"))
(defgeneric from-plutus (v)
  (:documentation "Convert the primitive plutus value `v' to a lisp value"))

(defun slot-name (class-name arg-name)
  (intern (concatenate 'string (symbol-name class-name) "-" (symbol-name arg-name))))

(defun arg->slot (class-name arg-name)
  (list arg-name
        :initarg (make-keyword (symbol-name arg-name))
        :accessor (slot-name class-name arg-name)))

(defun args->make-instance-plist (args)
  (apply #'append (loop for a in args collecting (list (make-keyword (symbol-name a)) a))))

(defun eval-typecheck-plutus (env v type)
  (let ((evaled (eval-plutus env v)))
    (if (eql (type-of evaled) type)
        evaled
        (error 'type-error :datum v :expected-type type))))

(defun arg->typechecked (class-object-symbol class-name arg)
  (if (consp arg)
      `(,(car arg) (eval-typecheck-plutus env (,(slot-name class-name (car arg)) ,class-object-symbol) (quote ,(cadr arg))))
      `(,arg (eval-plutus env (,(slot-name class-name arg) ,class-object-symbol)))))

(defun apply-to-plutus (lisp-function &rest plutus-args)
  (to-plutus (apply lisp-function (loop for a in plutus-args collecting (from-plutus a)))))

(defmacro def-builtin-plutus-function (name args &rest body)
  "Create a class named NAME, a helper ast building function named NAME which stores (LENGTH ARGS) slots,
and a EVAL-PLUTUS method implementation for that class from the BODY.

NAME is a symbol.
ARGS is a list of symbols or (SYMBOL TYPE) lists where TYPE is a plutus type name."
  (let* ((arg-names (loop for a in args collecting (if (consp a) (car a) a)))
         (slots (loop for a in arg-names collecting (arg->slot name a)))
         (make-instance-args (args->make-instance-plist arg-names))
         (f (gensym "f"))
         (let-evaled-args (loop for a in args collecting (arg->typechecked f name a))))
    `(progn
       (defclass ,name () ,slots)
       (defun ,name ,arg-names
         (make-instance (quote ,name) ,@make-instance-args))
       (defmethod eval-plutus (env (,f ,name))
         (let ,let-evaled-args ,@body)))))

;; Builtin types
(defclass plutus-bool ()
  ((value :initarg :value :accessor plutus-bool-value)))
(defclass plutus-integer ()
  ((value :initarg :value :accessor plutus-integer-value)))
(defclass plutus-pair ()
  ((car :initarg :car :accessor plutus-pair-car)
   (cdr :initarg :cdr :accessor plutus-pair-cdr)))
(defclass plutus-list ()
  ((value :initarg :value :accessor plutus-list-value)))
(defclass plutus-map ()
  ((value :initarg :value :accessor plutus-map-value)))
(defclass plutus-bytestring ()
  ((value :initarg :value :accessor plutus-bytestring-value)))
(defclass plutus-string ()
  ((value :initarg :value :accessor plutus-string-value)))
(defclass plutus-unit ()
  ())

;; Builtin control-structure
;; TODO: application
(defclass plutus-lambda ()
  ((name :initarg :name :accessor plutus-lambda-name)
   (term :initarg :term :accessor plutus-lambda-term)))
(defclass plutus-error ()
  ())
(defclass plutus-id ()
  ((symbol :initarg :symbol :accessor plutus-id-symbol)))
(defclass plutus-delay ()
  ((value :initarg :value :accessor plutus-delay-value)))
(defclass plutus-force ()
  ((value :initarg :value :accessor plutus-force-value)))

(def-builtin-plutus-function plutus-add-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'+ a b))

(def-builtin-plutus-function plutus-multiply-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'* a b))

(def-builtin-plutus-function plutus-subtract-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'- a b))

(def-builtin-plutus-function plutus-divide-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'floor a b))

(def-builtin-plutus-function plutus-mod-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'mod a b))

(def-builtin-plutus-function plutus-quotient-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'truncate a b))

(def-builtin-plutus-function plutus-remainder-integer ((a plutus-integer) (b plutus-integer))
  (to-plutus (nth-value 1 (truncate (from-plutus a) (from-plutus b)))))

(def-builtin-plutus-function plutus-less-than-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'< a b))

(def-builtin-plutus-function plutus-less-than-equals-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'<= a b))

(def-builtin-plutus-function plutus-equals-integer ((a plutus-integer) (b plutus-integer))
  (apply-to-plutus #'eql a b))

;; TODO: that's broken a bit, as it's not actually delaying anything
;;       maybe define it an another way with a different macro as it's
;;       not really a function?
(def-builtin-plutus-function plutus-delay (a)
  a)

(def-builtin-plutus-function plutus-force ((a plutus-delay))
  (eval-plutus env (plutus-delay-a a)))

(def-builtin-plutus-function plutus-encode-utf8 ((a plutus-string))
  (error "TODO"))

(def-builtin-plutus-function plutus-decode-utf8 ((a plutus-bytestring))
  (error "TODO"))

(def-builtin-plutus-function plutus-append-string ((a plutus-string) (b plutus-string))
  (to-plutus (concatenate 'string (from-plutus a) (from-plutus b))))

(def-builtin-plutus-function plutus-equals-string ((a plutus-string) (b plutus-string))
  (apply-to-plutus #'equal a b))

(def-builtin-plutus-function plutus-append-bytestring ((a plutus-bytestring) (b plutus-bytestring))
  (to-plutus (concatenate 'vector (from-plutus a) (from-plutus b))))

(def-builtin-plutus-function plutus-cons-bytestring ((a plutus-integer) (b plutus-bytestring))
  (to-plutus (concatenate 'vector (vector (from-plutus a)) (from-plutus b))))

(def-builtin-plutus-function plutus-slice-bytestring ((a plutus-integer) (b plutus-integer) (c plutus-bytestring))
  (to-plutus (subseq (from-plutus c) (from-plutus a) (from-plutus b))))

(def-builtin-plutus-function plutus-length-of-bytestring ((a plutus-bytestring))
  (apply-to-plutus #'length a))

(def-builtin-plutus-function plutus-index-bytestring ((a plutus-bytestring) (b plutus-integer))
  (apply-to-plutus #'elt a))

(def-builtin-plutus-function plutus-equals-bytestring ((a plutus-bytestring) (b plutus-bytestring))
  (apply-to-plutus #'equalp a))

(def-builtin-plutus-function plutus-less-than-bytestring ((a plutus-bytestring) (b plutus-bytestring))
  (apply-to-plutus #'equalp a))

(def-builtin-plutus-function plutus-less-than-equals-bytestring ((a plutus-bytestring) (b plutus-bytestring))
  (error "TODO"))

(def-builtin-plutus-function plutus-sha3-256 ((a plutus-bytestring))
  (error "TODO"))

(def-builtin-plutus-function plutus-sha2-256 ((a plutus-bytestring))
  (error "TODO"))

(def-builtin-plutus-function plutus-blake2b-256 ((a plutus-bytestring))
  (error "TODO"))

(def-builtin-plutus-function plutus-verify-signature ((a plutus-bytestring) (b plutus-bytestring) (c plutus-bytestring))
  (error "TODO"))

(def-builtin-plutus-function plutus-fst-pair ((a plutus-pair))
  (plutus-pair-car a))

(def-builtin-plutus-function plutus-snd-pair ((a plutus-pair))
  (plutus-pair-cdr a))

(def-builtin-plutus-function plutus-choose-list (a b c)
  (error "TODO"))

(def-builtin-plutus-function plutus-mk-cons (a b)
  (error "TODO"))

(def-builtin-plutus-function plutus-head-list ((a plutus-list))
  (if (from-plutus a)
      (to-plutus (car (from-plutus a)))
      (error 'plutus-head-signal)))

(def-builtin-plutus-function plutus-tail-list (a)
  (if (from-plutus a)
      (let ((r (cdr (from-plutus a))))
        (if r r (make-instance 'plutus-list :value nil)))
      (error 'plutus-tail-signal)))

(def-builtin-plutus-function plutus-null-list (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-if-then-else ((a plutus-bool) b c)
  (if (from-plutus a) b c))

(def-builtin-plutus-function plutus-choose-unit (a b)
  (error "TODO"))

(def-builtin-plutus-function plutus-error ()
  (error 'plutus-error-signal))

(def-builtin-plutus-function plutus-trace (a b)
  (error "TODO"))

(def-builtin-plutus-function plutus-choose-data (a b c d e)
  (error "TODO"))

(def-builtin-plutus-function plutus-constr-data (a b)
  (error "TODO"))

(def-builtin-plutus-function plutus-map-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-list-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-i-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-b-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-un-constr-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-un-map-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-un-list-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-un-i-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-un-b-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-equals-data (a b)
  (error "TODO"))

(def-builtin-plutus-function plutus-mk-pair-data (a b)
  (error "TODO"))

(def-builtin-plutus-function plutus-mk-nil-data (a)
  (error "TODO"))

(def-builtin-plutus-function plutus-mk-nil-pair-data (a)
  (error "TODO"))

;; utils
(defun alistp (alist)
  (and (listp alist)
       (every #'consp alist)))

;; to-plutus implementations:
;; builtin types
(defmethod to-plutus ((b (eql t)))
  (make-instance 'plutus-bool :value t))
(defmethod to-plutus ((b (eql nil)))
  (make-instance 'plutus-bool :value nil))
(defmethod to-plutus ((i integer))
  (make-instance 'plutus-integer :value i))
(defmethod to-plutus ((p cons))
  ;; Possible forms:
  ;; alist ((a . b) (c . d) ...) -> plutus-map
  ;; cons  (a . b)               -> plutus-pair
  ;; list  (a b c ...)           -> plutus-list
  (cond
    ((alistp p)
     (make-instance 'plutus-map :value (loop for v in p collecting (to-plutus v))))
    ((and (not (consp (cdr p))) (not (null (cdr p))))
     (make-instance 'plutus-pair :car (to-plutus (car p)) :cdr (to-plutus (cdr p))))
    (t
     (make-instance 'plutus-list :value (loop for v in p collecting (to-plutus v))))))
(defmethod to-plutus ((u (eql 'unit)))
  (make-instance 'plutus-unit))
(defmethod to-plutus ((b array))
  (make-instance 'plutus-bytestring :value b))
(defmethod to-plutus ((s string))
  (make-instance 'plutus-string :value s))

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

;; eval-plutus implementations:

(define-condition plutus-error-signal (error)
  ())

(define-condition plutus-head-signal (error)
  ())

(define-condition plutus-tail-signal (error)
  ())

(defmethod eval-plutus (env (b plutus-bool))
  b)

(defmethod eval-plutus (env (i plutus-integer))
  i)

(defmethod eval-plutus (env (l plutus-list))
  (make-instance 'plutus-list
                 :value
                 (loop for e in (plutus-list-value l)
                       collect (eval-plutus env e))))

(defmethod eval-plutus (env (m plutus-map))
  (make-instance 'plutus-map
                 :value
                 (loop for e in (plutus-map-value m)
                       collect (eval-plutus env e))))

(defmethod eval-plutus (env (p plutus-pair))
  (make-instance 'plutus-pair
                 :car (eval-plutus env (plutus-pair-car p))
                 :cdr (eval-plutus env (plutus-pair-cdr p))))

(defmethod eval-plutus (env (b plutus-bytestring))
  b)

(defmethod eval-plutus (env (s plutus-string))
  s)

(defmethod eval-plutus (env (u plutus-unit))
  u)

(defmethod eval-plutus (env (f plutus-lambda))
  f)

(defmethod eval-plutus (env (e plutus-error))
  (error 'plutus-error-signal))

(defmethod eval-plutus (env (i plutus-id))
  (let* ((symbol (plutus-id-symbol i))
         (looked-up (assoc symbol env)))
    (if looked-up
        (cdr looked-up)
        (error 'unbound-variable :name symbol))))
