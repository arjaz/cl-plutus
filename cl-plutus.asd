;;;; plisp.asd

(asdf:defsystem #:cl-plutus
  :description "Describe cl-plutus here"
  :author "Your Name <your.name@example.com>"
  :license  "Specify license here"
  :version "0.0.1"
  :serial t
  :depends-on (#:alexandria #:ironclad)
  :components ((:file "package")
               (:file "cl-plutus")))
