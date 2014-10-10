;; define several class of keywords
(defvar clafer-keywords
  '("abstract" "else" "in" "no" "not" "opt" "xor" "all" "enum" "lone" "not" "or" "disj" "mux" "one" "some")
  "Clafer keywords.")

(defvar clafer-types
  '("integer" "string" "real" "int")
  "Clafer types.")

(defvar clafer-operators
  '("->" "->>" ":")
  "Clafer Operators.")

(defvar clafer-cardinalities
  '("?" "+" "*")
  "Clafer Cardinalities.")

(defvar clafer-constraints-operators
  '("<" ">" ">=" "<=" "<:" ":>" "=>" "+" "++" "~" "!=" "*" "#" "`" "in" "not in")
  "Clafer Constraints Operators.")

;; create the regex string for each class of keywords
(defvar clafer-keywords-regexp (regexp-opt clafer-keywords 'words))
(defvar clafer-types-regexp (regexp-opt clafer-types 'words))
(defvar clafer-operators-regexp (regexp-opt clafer-operators 'words))
(defvar clafer-cardinalities-regexp (regexp-opt clafer-cardinalities 'words))
(defvar clafer-constraints-operators-regexp (regexp-opt clafer-constraints-operators 'words))

;; clear memory
(setq clafer-keywords nil)
(setq clafer-types nil)
(setq clafer-operators nil)
(setq clafer-cardinalities nil)
(setq clafer-constraints-operators nil)

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq clafer-font-lock-keywords
  `(
    (,clafer-types-regexp . font-lock-type-face)
    (,clafer-operators-regexp . font-lock-constant-face)
    (,clafer-cardinalities-regexp . font-lock-constant-face)
    (,clafer-constraints-operators-regexp . font-lock-function-name-face)
    (,clafer-keywords-regexp . font-lock-keyword-face)
    ;; note: order above matters. “clafer-keywords-regexp” goes last because
    ;; otherwise the keyword “state” in the function “state_entry”
    ;; would be highlighted.
))

;; define the mode
(define-derived-mode clafer-mode fundamental-mode
  "clafer mode"
  "Major mode for editing Clafer"
  ;; ...

  ;; code for syntax highlighting
  (setq font-lock-defaults '((clafer-font-lock-keywords)))

  ;; clear memory
  (setq clafer-keywords-regexp nil)
  (setq clafer-types-regexp nil)
  (setq clafer-operators-regexp nil)
  (setq clafer-cardinalities-regexp nil)
  (setq clafer-constraints-operators-regexp nil)

  ;; ...
)

;; the command to comment/uncomment text
;; (defun clafer-comment-dwim (arg)
;; "Comment or uncomment current line or region in a smart way.
;; For detail, see `comment-dwim'."
;;    (interactive "*P")
;;    (require 'newcomment)
;;    (let ((deactivate-mark nil) (comment-start "--") (comment-end ""))
;;      (comment-dwim arg)))

;; define the major mode.
;; (define-derived-mode clafer-mode fundamental-mode
;; "clafer-mode is a major mode for editing language clafer."

  ;; modify the keymap
;;   (define-key clafer-mode-map [remap comment-dwim] 'clafer-comment-dwim)

  ;; perl style comment: “# ...” 
;;   (modify-syntax-entry ?- "< b" clafer-mode-syntax-table)
;;   (modify-syntax-entry ?\n "> b" clafer-mode-syntax-table)
;; )