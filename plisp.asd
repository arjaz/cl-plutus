;;;; plisp.asd

(asdf:defsystem #:plisp
  :description "Describe plisp here"
  :author "Your Name <your.name@example.com>"
  :license  "Specify license here"
  :version "0.0.1"
  :serial t
  :depends-on (#:alexandria)
  :components ((:file "package")
               (:file "plisp")))
