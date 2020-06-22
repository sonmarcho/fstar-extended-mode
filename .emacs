(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(custom-enabled-themes (quote (tango-dark)))
 '(package-selected-packages
   (quote
    (fill-column-indicator tuareg merlin markdown-preview-mode markdown-mode proof-general cmake-mode company-rtags fstar-mode))))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )

;; Packages facility
(require 'use-package)

;; disable this annoying bell sound
(setq ring-bell-function 'ignore)

;; show cursor position within line
(column-number-mode 1)

;; to display a vertical line at column 80
(require 'fill-column-indicator)
(setq fci-rule-column 80)
(define-globalized-minor-mode global-fci-mode fci-mode (lambda () (fci-mode 1)))
(global-fci-mode 1)


;; fstar
(setq-default fstar-executable "/home/son/FStar/bin/fstar.exe")
(setq-default fstar-smt-executable "/usr/bin/z3")

(defun my-fstar-compute-prover-args-using-make ()
  "Construct arguments to pass to F* by calling make."
  (interactive)
  (with-demoted-errors "Error when constructing arg string: %S"
    (let* ((fname (file-name-nondirectory buffer-file-name))
            (target (concat fname "-in"))
            (argstr (condition-case nil
                        (car (process-lines "make" "--quiet" target))
                      (error (concat
                              "--include " "/home/son/kremlin/kremlib "
                              "--include " "/home/son/hacl-star/lib"
                              ;; "--debug yes --log_queries --use_hints --cache_checked_modules"
                              )))))
                      ;; (error (concat
                      ;;         "--include " (getenv "HOME") "/kremlin/kremlib "
                      ;;         ;; "--debug yes --log_queries --use_hints --cache_checked_modules"
                      ;;         )))))
            (split-string argstr))))
(setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
(setq fstar-subp-debug t)

;; fstar-mode for .fs and .fsi files
(add-to-list 'auto-mode-alist '("\\.fs\\'" . fstar-mode))
(add-to-list 'auto-mode-alist '("\\.fsi\\'" . fstar-mode))

;; ;; Set the F* specific parameters
;;   (setq fstar-subp-prover-args '(
;;                                 ;; F* options
;;                                 ;;"--detail_errors"
;;                                 "--print_universes"
;;                                 ;; "--print_implicits"
;;                                 "--use_hints"
;;                                 "--record_hints"
;;                                 "--query_stats"
;;                                 "--cache_checked_modules"
;;                                 "--already_cached" "Prims FStar LowStar C Spec.Loops Hacl"
;;                                 ;; "--detail_hint_replay"
;;                                 ;; "--expose_interfaces"
;;                                 ;; Kremlin
;;                                 ;;"--include" "/home/son/kremlin/kremlib"
;;                                 ;; HACL*
;;                                 "--include" "/home/son/hacl-star/lib"
;;                                 ;;"--include" "/home/son/hacl-star/lib/fst"
;;                                 "--include" "/home/son/hacl-star/specs"
;;                                 ;;"--include" "/home/son/hacl-star/specs/experimental"
;;                                 "--include" "/home/son/hacl-star/specs/tests"
;;                                 "--include" "/home/son/hacl-star/specs/lemmas"
;;                                 ;;"--include" "/home/son/hacl-star/code/blake2"
;;                                 "--include" "/home/son/hacl-star/code/chacha20"
;;                                 "--include" "/home/son/hacl-star/code/curve25519"
;;                                 ;;"--include" "/home/son/hacl-star/code/curve25519/lemmas"
;; 				"--include" "/home/son/hacl-star/code/poly1305"
;;                                 "--include" "/home/son/hacl-star/code/chacha20poly1305"
;; 				"--include" "/home/son/hacl-star/code/blake2"
;; 				"--include" "/home/son/hacl-star/code/curve25519"
;;                                 "--include" "/home/son/hacl-star/code/hash"
;;                                 "--include" "/home/son/hacl-star/code/hmac"
;; 				"--include" "/home/son/hacl-star/code/meta"
;; 				"--include" "/home/son/wg-star"
;; 				"--include" "/home/son/libsignal-protocol-wasm-fstar"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/hkdf"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/aes-256-cbc"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/ed25519"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/aes"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/gf128"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/aes-gcm"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/sha2"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/hmac"
;;                                 ;;"--include" "/home/son/hacl-star/code/experimental/hkdf"
;;                                 ))

;;                                "--already_cached" "Prims FStar LowStar C Spec.Loops Hacl"

;;
;; C/C++ development
;;

;; Projectile : project management
(with-eval-after-load 'projectile
  (setq-default
   projectile-mode-line
   '(:eval
     (if (file-remote-p default-directory)
	 " Pr"
       (format " Pr[%s]" (projectile-project-name))))))


;; CEDET : Collection of Emacs Development Environment Tools
;; enable Semantic mode and SemanticDB
(require 'semantic)
(global-semanticdb-minor-mode 1)
(global-semantic-idle-scheduler-mode 1)
(semantic-mode 1)
;; (semantic-enable) ;; doesn't work

;; require cl for 'remove-if'
(require 'cl)

;; remove Semantic mode for Python and HTML (there are better completion tools)
(setq semantic-new-buffer-setup-functions
      (remove-if (lambda (buffer-setup-function)
		   (member (car buffer-setup-function)
			   '(python-mode html-mode)))
		 semantic-new-buffer-setup-functions))

(remove-hook 'python-mode-hook 'wisent-python-default-setup)

;; add completion backend to company-mode for auto-completion
(defun company-semantic-setup ()
  "Configure company-backends for company-semantic and company-yasnippet."
  (delete 'company-irony company-backends)
  (push '(company-semantic :with company-yasnippet) company-backends)
  )

;; enable EDE mode (Emacs Development Environment) to work with projects
(global-ede-mode 1)

(setq ede-custom-file (expand-file-name "cc-mode-projects.el" user-emacs-directory))
(when (file-exists-p ede-custom-file)
  (load ede-custom-file))

;; header files completion
(defun company-c-headers-setup ()
  (add-to-list 'company-backends 'company-c-headers))

;; configure header file paths for company-c header
(defun ede-object-system-include-path ()
  (when ede-object
    (ede-system-include-path ede-object)))
(setq company-c-headers-path-system 'ede-object-system-include-path)

;; local header files
(setq header-custom-file (expand-file-name "cc-mode-header-custom.el" user-emacs-directory))
(when (file-exists-p header-custom-file)
  (load header-custom-file))

;; hooks
(add-hook 'c++-mode-hook 'company-c-headers-setup)
(add-hook 'c-mode-hook 'company-c-headers-setup)
(add-hook 'c++-mode-hook 'company-semantic-setup)
(add-hook 'c-mode-hook 'company-semantic-setup)

;; Don't install RTags for now : can't install clang for development (not enough space)
;; ;; RTags
;; ;; rtags-diagnostics
;; (rtags-enable-standard-keybindings)
;; (setq rtags-autostart-diagnostics t)
;; (rtags-diagnostics)

;; ;; compatny-rtags for code completion
;; (defun company-rtags-setup ()
;;   "Configure company-backends for company-rtags."
;;   (delete 'company-semantic company-backends)
;;   (setq rtags-completions-enabled t)
;;   (push '(company-rtags :with company-yasnippet) company-backends))

;; ;; rtags hook
;; (rtags-start-process-unless-running)
;; (add-hook 'c++-mode-hook 'company-rtags-setup)
;; (add-hook 'c-mode-hook 'company-rtags-setup)

;; ;; enable cmake-mode
;; (setq auto-mode-alist
;;       (append
;;        '(("CMakeLists\\.txt\\'" . cmake-mode))
;;        '(("\\.cmake\\'" . cmake-mode))
;;        auto-mode-alist))

;; ;; configure company-cmake
;; defun company-cmake-setup ()
;;   (add-to-list 'company-backends 'company-cmake))
;; (add-hook 'cmake-mode-hook 'company-cmake-setup)


;; function to enable CEDET
(defun cedet-enable ()
  "Start CEDET."
  (interactive)
  (remove-hook 'c++-mode-hook 'company-rtags-setup)
  (remove-hook 'c-mode-hook 'company-rtags-setup)
  (remove-hook 'c++-mode-hook 'flycheck-rtags-setup)
  (remove-hook 'c-mode-hook 'flycheck-rtags-setup)
  (semantic-enable)
  (add-hook 'c++-mode-hook 'company-c-headers-setup)
  (add-hook 'c-mode-hook 'company-c-headers-setup)
  (add-hook 'c++-mode-hook 'company-semantic-setup)
  (add-hook 'c-mode-hook 'company-semantic-setup)
  )

;; function to enable RTags/Irony-Mode
(defun irony-enable ()
  "Start irony mode."
  (interactive)
  (semantic-disable)
  (remove-hook 'c++-mode-hook 'company-c-headers-setup)
  (remove-hook 'c-mode-hook 'company-c-headers-setup)
  (remove-hook 'c++-mode-hook 'company-semantic-setup)
  (remove-hook 'c-mode-hook 'company-semantic-setup)
  (rtags-start-process-unless-running)
  (add-hook 'c++-mode-hook 'company-rtags-setup)
  (add-hook 'c-mode-hook 'company-rtags-setup)
  (add-hook 'c++-mode-hook 'flycheck-rtags-setup)
  (add-hook 'c-mode-hook 'flycheck-rtags-setup)
  )

;; change the basic indentation offset
(setq-default c-basic-offset 4)

;; always use spaces rather than tabs
(setq-default indent-tabs-mode nil)

;; Markdown-mode
(setq markdown-command "multimarkdown")

;; Tuareg (OCaml)
(load "/home/son/.opam/system/share/emacs/site-lisp/tuareg-site-file")

;; Merlin
(let ((opam-share (ignore-errors (car (process-lines "opam" "config" "var" "share")))))
 (when (and opam-share (file-directory-p opam-share))
  (add-to-list 'load-path (expand-file-name "emacs/site-lisp" opam-share))
  (autoload 'merlin-mode "merlin" nil t nil)
  (add-hook 'tuareg-mode-hook 'merlin-mode t)
  (add-hook 'caml-mode-hook 'merlin-mode t)))

;; Start merlin mode whenever I open an .ml file
(add-hook 'caml-mode-hook 'merlin-mode)

(global-set-key [f5] 'compile)
(global-set-key [f6] 'recompile)
(global-set-key [f7] 'next-error)

;;
;; Custom commands and bindings for the F* mode
;;
(defun back-to-indentation-or-beginning () (interactive)
   (if (= (point) (progn (back-to-indentation) (point)))
       (beginning-of-line)))

(defun current-line-is-whitespaces-p ()
  "Checks if the current line is only made of spaces"
  (save-excursion
    (beginning-of-line)
    (looking-at-p "[[:space:]]*$")))

(defun insert-newline-term (TERM)
  "If the current line is not empty, insert a new line after the current one,
   then insert TERM"
  (interactive)
  (progn
   (if (current-line-is-whitespaces-p) () (progn (end-of-line) (newline)))
   (indent-according-to-mode)
   (insert TERM)))

(defun empty-line ()
  "Delete all the characters on the current line and returns the number of deleted caracters"
  (interactive)
  (let ($p)
   (setq $p (- (line-end-position) (line-beginning-position)))
   (delete-region (line-beginning-position) (line-end-position))
   $p))

(defun empty-delete-line ()
  "Remove all the characters on the line if not empty, delete the line otherwise"
  (interactive)
  (if (equal (line-beginning-position) (line-end-position))
      (progn (delete-backward-char 1) 1) (empty-line)))

(defun delete-always-line ()
  "Remove all the characters on the line if not empty, delete the line otherwise"
  (interactive)
  (let ($c)
    (if (equal (line-beginning-position) (line-end-position))
	(progn (delete-backward-char 1) 1)
	(progn (setq $c (empty-line))
	       (delete-backward-char 1) (+ $c 1)))))

(defun find-region-delimiters (ALLOW_SELECTION INCLUDE_CURRENT_LINE
                               ABOVE_PARAGRAPH BELOW_PARAGRAPH)
 (let ($p $p1 $p2)
   ;; Save the current point
   (setq $p (point))
   ;; Find the region delimiters (and move the pointer back to its original position):
   ;; First check if we need to use the selected region
   (if (and (use-region-p) (ALLOW_SELECTION))
       ;; Use the selected region
       (setq $p1 (region-beginning) $p2 (region-end))
       ;; Compute a new region
       (progn
         ;; - beginning of region
         (progn (if ABOVE_PARAGRAPH (backward-paragraph)
                  (if INCLUDE_CURRENT_LINE (move-beginning-of-line ()) (move-end-of-line ())))
                (setq $p1 (point)) (goto-char $p))
         ;; - end of region
         (progn (if BELOW_PARAGRAPH (forward-paragraph)
                  (if INCLUDE_CURRENT_LINE (move-end-of-line ()) (move-beginning-of-line ())))
                (setq $p2 (point)) (goto-char $p))))
   (list $p1 $p2)))

(defun apply-in-current-region (ACTION ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  "Applies the action given as argument to the current line and/or the current
   paragraph above the pointer.
   It is the responsability of the ACTION function to move the pointer back to its
   (equivalent) original position."
  (let ($delimiters $p1 $p2 $r)
    ;; Find the region delimiters
    (setq $delimiters (find-region-delimiters ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                              ABOVE_PARAGRAPH BELOW_PARAGRAPH))
    (setq $p1 (car $delimiters) $p2 (car (cdr $delimiters)))
    ;; Apply the action in the delimited region
    (save-restriction
      (narrow-to-region $p1 $p2)
      (setq $r (funcall ACTION)))
    ;; return the result of performing the action
    $r))

(defun apply-in-current-line (ACTION)
  "Applies the action given as argument to the current line.
   It is the responsability of the ACTION function to move the pointer back to its
   (equivalent) original position."
  (apply-in-current-region ACTION nil t nil nil))

(defun replace-in-current-region (FROM TO ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                  ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  (let ($p $r $length_dif)
    ;; Define the replace function
    (setq $length_dif (- (length TO) (length FROM)))
    (setq $r
      (defun replace ()
        (let ($p1 $shift)
          (progn
            (setq $p (point))
            (setq $shift 0)
            ;; Replace all the occurrences of FROM
            (beginning-of-buffer)
            (while (search-forward FROM nil t)
              (progn
                ;; Compute the pointer shift
                (setq $p1 (point))
                (if (<= $p1 (+ $p $shift)) (setq $shift (+ $shift $length_dif)) ())
                ;; Replace
                (replace-match TO)))
            ;; Move to the (equivalent) original position and return the shift
            (goto-char (+ $shift $p))
            $shift))))
    ;; Apply the replace function
    (apply-in-current-region $r ALLOW_SELECTION INCLUDE_CURRENT_LINE
                             ABOVE_PARAGRAPH BELOW_PARAGRAPH)))

(defun switch-assert-assume-in-current-region (ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                               ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  (interactive)
  "Check if there are occurrences of 'assert' or 'assert_norm in the current region.
   If so, replace them with 'assume'. Ohterwise, replace all the 'assume' with 'assert'."
  (let ($f $r $p $replace)
    ;; check if there are occurrences of "assert"
    (setq $p (point))
    (setq $f (defun find () (progn (beginning-of-buffer) (search-forward "assert" nil t))))
    (setq $r (funcall 'apply-in-current-region $f ALLOW_SELECTION INCLUDE_CURRENT_LINE
                      ABOVE_PARAGRAPH BELOW_PARAGRAPH))
    (goto-char $p)
    ;; if there are, replace "assert" by "assume", otherwise replace "assume" by "admit"
    (setq $replace
          (lambda (FROM TO)
            (replace-in-current-region FROM TO ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                       ABOVE_PARAGRAPH BELOW_PARAGRAPH)))
    (if $r (progn
             (funcall $replace "assert_norm" "assume(*norm*)")
             (funcall $replace "assert" "assume"))
           (progn
             (funcall $replace "assume(*norm*)" "assert_norm")
             (funcall $replace "assume" "assert")))))

(defun switch-assert-assume-in-above-paragraph ()
  (interactive)
  "In the part of the current paragraph above the cursor and in the current line,
   check if there are occurrences of 'assert' or 'assert_norm'. If so, replace them
   with 'assume'. Otherwise, replace all the 'assume' with 'assert'."
  (switch-assert-assume-in-current-region t t t nil))

(defun switch-assert-assume-in-current-line ()
  (interactive)
  "In the current line, check if there are occurrences of 'assert' or 'assert_norm'.
   If so, replace them with 'assume'. Otherwise, replace all the 'assume' with 'assert'."
  (switch-assert-assume-in-current-region nil t nil nil))

(defun roll-delete-term (TERM FORWARD BEGIN END)
  (interactive)
  "Looks for the last/first occurence of TERM in the region and asks the user
   if he wants to delete it, if there is any, deletes the following semicolon if
   there is any. Leaves the pointer at its original position (before the command was
   called). Returns a tuple: 
   (found term, optional shift if term was deleted, deleted a semicolon)"
  (let ($p $s $f $r $semicol $opt_shift)
    (setq $s 0)
    ;; Retrieve the original position
    (setq $p (point))
    ;; Look for an admit
    (if FORWARD (setq $f (search-forward TERM END t))
		(setq $f (search-backward TERM BEGIN t)))
    ;; If there is an occurrence of TERM, ask for removal
    (when $f
      (when (y-or-n-p (concat "Remove this '" (concat TERM "'?")))
	(progn
	  (replace-match "")
	  (setq $r t)
          ;; Look for a semicolon to delete
          (when (char-equal ?\; (following-char))
            (progn
              (delete-forward-char 1)
              (setq $semicol t)
              (when (not FORWARD) (setq $s 1))))
          ;; Delete the whole line if it is empty
	  (when (current-line-is-whitespaces-p) (setq $s (delete-always-line)))
	  ;; Compute the position shift
	  (when (not FORWARD) (setq $s (+ (length TERM) $s)))
	  )))
    ;; Go to the original position
    (goto-char (- $p $s))
    ;; Return the shift if we deleted a TERM
    (if $r (setq $opt_shift $s) (setq $opt_shift nil))
    ;; Return
    (list (cons 'found $f) (cons 'opt_shift $opt_shift) (cons 'semicol $semicol))))

(defun roll-admit ()
  (interactive)
  "Facility function to ease the rolling admit technique: inserts an admit
   after the current line and check if there is another admit to move (and ask
   for deletion if so). We start by looking for an admit after the cursor
   position, then look before if there isn't."
  (let ($p $p1 $p2 $s)
    ;; Save the current point
    (setq $p (point))
    ;; Find the region delimiters
    (progn (forward-paragraph) (setq $p2 (point))
	   (backward-paragraph) (setq $p1 (point))
	   (goto-char $p))
    ;; Delete forward
    (setq $s (roll-delete-term "admit()" t $p1 $p2))
    ;; Delete backward
    (when (not (cdr (assoc 'opt_shift $s)))
          (setq $s (roll-delete-term "admit()" nil $p1 $p2)))
    ;; Insert the admit
    (if (cdr (assoc 'semicol $s))
        (insert-newline-term "admit();")
        (insert-newline-term "admit()"))))

(define-error 'fstar-meta-parsing "Error while parsing F*")

;; TODO: comes from fstar-mode.el
;;(defconst fstar--spaces "\t\n\r ")

;; From now onwards we use functions from the F* mode
(use-package fstar-mode
  :demand)

(defun skip-comment (FORWARD &optional LIMIT)
  "Move the cursor forward or backward until we are out of a comment or we
   reach the end of the buffer"
  (let ($stop)
    ;; Set the limit to the move
    (if FORWARD (setq $stop (or LIMIT (point-max)))
                (setq $stop (or LIMIT (point-min))))
    (if (fstar-in-comment-p)
        (if FORWARD
            ;; Forward: go forward until we are out of the comment
            (while (and (fstar-in-comment-p) (< (point) $stop)) (forward-char))
            ;; Backward:
            (goto-char (nth 8 (fstar--syntax-ppss (point))))))))

(defun is-at-comment-limit (FORWARD &optional LIMIT)
  (if FORWARD
      ;; If forward: the comments delimiters are always made of two characters
      ;; and we can't know if we are inside a comment unless we process those
      ;; two characters
      (progn
        (if (> (+ (point) 2) (or LIMIT (point-max))) nil
          (fstar-in-comment-p (+ (point) 2))))
      ;; If backward: we just need to go one character back
      (progn
        (if (< (- (point) 1) (or LIMIT (point-min))) nil
          (fstar-in-comment-p (- (point) 1))))))

(defun skip-chars (FORWARD CHARS &optional LIMIT)
  (if FORWARD
      (skip-chars-forward CHARS LIMIT)
      (skip-chars-backward CHARS LIMIT)))

(defun skip-comments-and-spaces (FORWARD &optional LIMIT)
  "Move the cursor forward or backward until we are out of a comment and there
   are no spaces"
  (let ($continue $p1 $p2 $limit $reached-limit)
    (if FORWARD (setq $p1 (point) $p2 (or LIMIT (point-max)))
                (setq $p2 (point) $p1 (or LIMIT (point-min))))
    (if FORWARD (setq $limit $p2) (setq $limit $p1))
    (save-restriction
      (narrow-to-region $p1 $p2)
      (setq $continue t)
      (while $continue
        (skip-comment FORWARD LIMIT)
        (skip-chars FORWARD fstar--spaces)
        (setq $reached-limit (= (point) $limit))
        (if $reached-limit (setq $continue nil)
          (if (is-at-comment-limit FORWARD)
            (if FORWARD (forward-char 2) (backward-char 1))
            (setq $continue nil)))))))

(defun t4 ()
  (interactive)
  (if (fstar-in-comment-p (point))
      (message "In comment") (message "Not in comment")))

(defun t3 ()
  (interactive)
  (if (next-char-is-in-comment t) (message "Next in comment")
    (message "Next not in comment")))

(defun t2 ()
  (interactive)
  (skip-comments-and-spaces t))

(defun t1 ()
  (interactive)
  (insert-assert-pre-post))

(defun insert-assert-pre-post ()
  (interactive)
  "Inserts 'asserts' with appropriate pre and post-conditions around a function call"
  (let ($p $delimiters $p1 $p2)
    ;; Find in which region the term to process is
    (setq $p (point))
    (setq $delimiters (find-region-delimiters t t nil nil))
    (setq $p1 (car $delimiters) $p2 (car (cdr $delimiters)))
    ;; Parse: 3 cases:
    ;; - let _ = _ in
    ;; - _;
    ;; - _
    ;; Restrict to the term region
    (save-restriction
      (narrow-to-region $p1 $p2)
      (let ($p1 $p2 $cp1 $cp2 $tmp $c $is-let-in $has-semicol)
        (setq $p1 (point-min) $p2 (point-max))
        (setq $has-let nil $has-semicol nil)
        ;; Note that there may be a comment/spaces at the beginning and at the end
        ;; of the processed region, so we need to narrow the region further
        ;;
        ;; Narrow the region to remove spaces/comments at the beginning and at the end
        ;; - beginning
        (goto-char $p1)
        (skip-comments-and-spaces t)
        (setq $cp1 (point))
        ;; - end
        (goto-char $p2)
        (skip-comments-and-spaces nil $cp1)
        (setq $cp2 (point))
        (save-restriction
          (narrow-to-region $cp1 $cp2)
          ;; Check if the narrowed region matches: 'let _ = _ in'
          (goto-char (point-min))
          (setq $is-let-in
                (re-search-forward
                 "let[[:ascii:][:nonascii:]]+in" nil t 1))
          (if $is-let-in (message "Is 'let _ = _ in'") (message "Not is 'let _ = _ in'"))
          ;; Check if the narrowed region matches: '_ ;'
          (goto-char (point-min))
          (setq $is-let-in
                (re-search-forward
                 "[[:ascii:][:nonascii:]]+;" nil t 1))
          (if $is-let-in (message "Is '_ ;'") (message "Not is '_ ;'")))
        ;; Switch between cases (depending on the matched regexp)
        ))))

;; Actually already C-M-o
(defun split-line-indent-is-cursor ()
  (interactive)
  (let ($p $c)
    (setq $p (point))
    (setq $c (- $p (line-beginning-position)))
    (newline)
    (dotimes (i $c) (insert " "))
    (goto-char $p)
    $c))

(defun newline-keep-indent ()
  (interactive)
  (let ($p $i)
    (setq $p (point))
    (back-to-indentation)
    (setq $i (- (point) (line-beginning-position)))
    (goto-char $p)
    (newline)
    (dotimes (i $i) (insert " "))
    $i))

;; Key bindings
(global-set-key (kbd "C-c C-s C-r") 'replace-string) ;; "C-c C-r" is already bound in F* mode
(global-set-key (kbd "C-c C-q") 'query-replace)

(global-set-key (kbd "M-n") 'forward-paragraph)
(global-set-key (kbd "M-p") 'backward-paragraph)
(global-set-key (kbd "M-k") 'delete-whole-line)
(global-set-key (kbd "C-d") 'delete-forward-char)
(global-set-key (kbd "C-,") 'delete-backward-char)
(global-set-key (kbd "M-,") 'backward-kill-word)
(global-set-key (kbd "M-m") 'back-to-indentation-or-beginning)

(global-set-key (kbd "C-M-j") 'newline-keep-indent)

(global-set-key (kbd "C-x C-a") 'roll-admit)
(global-set-key (kbd "C-c C-s C-a") 'switch-assert-assume-in-above-paragraph)
(global-set-key (kbd "C-S-a") 'switch-assert-assume-in-current-line)
