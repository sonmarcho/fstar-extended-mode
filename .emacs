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

;; F* extended mode
;; TODO: put the proper directory
(load "~/misc/fstar-mode-extended")
