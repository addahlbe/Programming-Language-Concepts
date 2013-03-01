;;; gratr.el --- Highlight mode for the gratr syntax.

;;; Commentary:

;; This major mode provides syntax highlighting for the 
;; gratr EBNF syntax.
;; 
;; To use it, add the following lines in your .emacs:
;; (Modify "~/gratr/" to the path to "gratr.el".)
;;
;; (setq load-path (cons (expand-file-name "~/gratr/") load-path))
;; (add-to-list 'auto-mode-alist '("\\.gr$" . gratr-mode))
;; (autoload 'gratr-mode "gratr" "Highlight mode for the gratr syntax." t)
;;

;;; Code:

;;;###autoload
(define-generic-mode 'gratr-mode
  '("%")
  '("Syntactic" "Lexical" "Whitespace" "Rules" "Vars")
  '(
    ("\\<[_a-zA-Z0-9]+\\>[ \t]*:" . font-lock-function-name-face)
    ("\\<[A-Z][_a-zA-Z0-9]*\\>" . font-lock-function-name-face)
    ("['\"].*?['\"]" . font-lock-string-face)
    ("\\<\\(e\\|s\\)os\\>" . font-lock-string-face)
    ("=>?\\|->\\||\\|\\." . font-lock-builtin-face)
    ("(\\|)\\|+\\|-\\|\\*\\|\\?\\|#\\|\\," . font-lock-constant-face)
   )
  '("\\.gr$")
  `(,(lambda () (setq mode-name "gratr")))
  "Highlight mode for the gratr syntax.")

(provide 'gratr-mode)
;;; gratr.el ends here
