;; opetopictt-mode.el -- major mode for opetopictt

(defvar opetopictt-font-lock-keywords
 '(
   ("#.*" . 'font-lock-comment-face)
   ("\\<\\(let\\|normalize\\|infer\\)\\>" . 'font-lock-keyword-face)
   ("\\<\\(U\\|Pos\\|El\\)\\>" . 'font-lock-builtin-face)
   ("\\<let[ \t]+\\([^ (=]*\\)" 1 'font-lock-function-name-face)
  )
)

(defvar opetopictt-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; Allow some extra characters in words
    (modify-syntax-entry ?_ "w" st)
    ;; Comments
    (modify-syntax-entry ?# "<" st)
    (modify-syntax-entry ?\n ">" st)
    st)
  "Syntax table for OPETOPICTT major mode.")

(defvar opetopictt-tab-width 4)
(defvar opetopictt-mode-hook nil)
(defvar opetopictt-mode-map nil "Keymap for opetopictt-mode")

(progn
  (setq opetopictt-mode-map (make-sparse-keymap))
  (define-key opetopictt-mode-map (kbd "C-c C-c") `compile)
  )

(define-derived-mode opetopictt-mode prog-mode
  "Opetopictt" "Major mode for Opetopictt files."
  :syntax-table opetopictt-mode-syntax-table
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-start-skip) "#+\\s-*")
  (set (make-local-variable 'font-lock-defaults) '(opetopictt-font-lock-keywords))
  (set (make-local-variable 'compile-command)
       (concat "opetopictt " (shell-quote-argument buffer-file-name)))
  (use-local-map opetopictt-mode-map)
  (setq mode-name "OpetopicTT")
  (run-hooks 'opetopictt-mode-hook)
)

(provide 'opetopictt-mode)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ott\\'" . opetopictt-mode))
