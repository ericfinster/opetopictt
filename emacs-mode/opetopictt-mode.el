;; opetopictt-mode.el -- major mode for opetopictt 

(when t
  ;; In order for the package to be usable and installable (and hence
  ;; compilable) without tree-sitter, wrap the `require's within a dummy `when'
  ;; so they're only executed when loading this file but not when compiling it.
  (require 'tree-sitter)
  (require 'tree-sitter-hl)
  (require 'tree-sitter-langs)
  (require 'tree-sitter-load))

;; Vars and functions defined by the above packages:
(defvar tree-sitter-major-mode-language-alist) ;From `tree-sitter-langs'.
;; (declare-function tree-sitter-indent-mode "ext:tree-sitter-indent")
;; (declare-function tree-sitter-indent-line "ext:tree-sitter-indent")
(declare-function tree-sitter-hl-mode "ext:tree-sitter-hl")
(declare-function tsc-node-end-position "ext:tree-sitter")
(declare-function tsc-node-start-position "ext:tree-sitter")
(declare-function tsc-node-to-secp "ext:tree-sitter")
(declare-function tree-sitter-node-at-point "ext:tree-sitter")
(declare-function tree-sitter-load "ext:tree-sitter")

;; Okay, this appears to actually load the language
;; definition.  Now to see what we can do with it!
(tree-sitter-load 'opetopictt "opetopictt")

(defun opetopictt-show-node-at-point ()
  (interactive)
  (message "Node: %s" (tsc-node-to-sexp (tree-sitter-node-at-point))))

(defun opetopictt-list-metas ()
  (interactive)
  (when-let ((caps (tsc-query-captures
		    '(hole) (tree-sitter-node-at-point)
		    #'ts--buffer-substring-no-properties))
	     (node (car (cdr caps))))
    (message "First return: %s" (tsc-node-to-sexp node))))
    
;; (defun opetopictt-next-meta ()
;;   "Skip to the next meta"
;;   (interactive)
;;   ;; TODO: Use a query-cursor
;;   (when-let ((caps (tsc-query-captures
;; 		    ((hole) @hole) (tree-sitter-node-at-point)
;; 		    #'ts--buffer-substring-no-properties)))
    

;; (defun csharp-delete-method-at-point ()
;;   "Deletes the method at point."
;;   (interactive)
;;   (when-let ((method (tree-sitter-node-at-point 'method_declaration)))
;;     (delete-region (tsc-node-start-position method)
;;                    (tsc-node-end-position method))))	    

;; Setting up the mode
(defvar opetopictt-mode-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap used in opetopictt-mode buffers.")

(defvar opetopictt-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?@ "_" table)
    table))

(define-key opetopictt-mode-map (kbd "C-c C-n") `opetopictt-show-node-at-point)

(defconst opetopictt-mode-tree-sitter-patterns
  [ ;; Keywords
   (comment) @comment
   [ "let" "comp" "fill" ] @keyword
   [ ":" "=" "(" ")" ] @punctuation
   [ "[" "]" "{" "}" "|" "⊢" "●" ] @punctuation.special
   [ "lf" "nd" "tt" ] @label
   [ "U" ] @constant

   (var_declaration variable: (identifier) @variable)
   
   (let_command
    name: (identifier) @function)

   (identifier) @function
   ])

;;;###autoload
(define-derived-mode opetopictt-mode prog-mode "Opetopictt"
  "Major mode for editing OpetopicTT code."
  :syntax-table opetopictt-mode-syntax-table

  ;; (setq-local indent-line-function #'tree-sitter-indent-line)
  ;; (setq-local beginning-of-defun-function #'csharp-beginning-of-defun)
  ;; (setq-local end-of-defun-function #'csharp-end-of-defun)

  ;; https://github.com/ubolonton/emacs-tree-sitter/issues/84
  (unless font-lock-defaults
    (setq font-lock-defaults '(nil)))
  (setq-local tree-sitter-hl-default-patterns
	      opetopictt-mode-tree-sitter-patterns)
  ;; Comments
  (setq-local comment-start "#")
  (setq-local comment-start-skip "#+\\s-*")

  (tree-sitter-mode)
  (tree-sitter-hl-mode))

(add-to-list 'tree-sitter-major-mode-language-alist
	     '(opetopictt-mode . opetopictt))

(add-to-list 'auto-mode-alist
	     '("\\.ott\\'" . opetopictt-mode))

(provide 'opetopictt-mode)

