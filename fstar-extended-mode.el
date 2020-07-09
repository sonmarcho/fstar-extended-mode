;;
;; Custom commands and bindings for the F* mode
;;

;; TODO: many manipulations in the below functions can be simplified by using:
;; - save-current-buffer, with-current-buffer (to switch buffer), with-temp-buffer

;; TODO: make the naming conventions coherent:
;; - capital letters for function parameters
;; - use $ for local variables
;; - 'fem-' prefix for all functions

;; I encountered some problems with undo (for instance, insert-assert-pre-post
;; works properly when executed as a command, but undo performs weird things
;; if it is linked to a key binding). Some very good explanations are provided
;; in the link below:
;; https://stackoverflow.com/questions/15097012/how-to-prevent-emacs-from-setting-an-undo-boundary
;; My current fix is to use temporary buffers which names start with a space.
;; Note that for now I don't want to use functions like to-switch-buffer because
;; I want to keep a trace of the data processing for debugging

(cl-defstruct pair fst snd)
(defvar fstar-extended-debug t)
(defconst fstar-extended-log-buffer "*fstar-extended-debug*")
(defun log-msg (format-string &rest format-params)
  "Log a message in the log buffer. TODO: for now just calls message"
  (apply #'message format-string format-params))
(defun log-dbg (format-string &rest format-params)
  "Log a message in the log buffer if fstar-extended-debug is t.
TODO: for now just calls message"
  (when fstar-extended-debug (apply #'message format-string format-params)))

(define-error 'fstar-meta-parsing "Error while parsing F*")

(defun replace-in-string (FROM TO STR)
  "Replace FROM with TO in string STR."
  (replace-regexp-in-string (regexp-quote FROM) TO STR nil 'literal))

(defun back-to-indentation-or-beginning ()
  "Switch between beginning of line or end of indentation."
  (interactive)
   (if (= (point) (progn (back-to-indentation) (point)))
       (beginning-of-line)))

(defun current-line-is-whitespaces-p ()
  "Check if the current line is only made of spaces."
  (save-excursion
    (beginning-of-line)
    (looking-at-p "[[:space:]]*$")))

(defun insert-newline-term (TERM)
  "Insert a new line if the current one is not empty, then insert TERM."
  (interactive)
  (progn
   (if (current-line-is-whitespaces-p) () (progn (end-of-line) (newline)))
   (indent-according-to-mode)
   (insert TERM)))

(defun newline-keep-indent ()
  "Insert a newline where the indentation is equal to the current column."
  (interactive)
  (let ($p $i)
    (setq $p (point))
    (back-to-indentation)
    (setq $i (- (point) (line-beginning-position)))
    (goto-char $p)
    (newline)
    (dotimes (i $i) (insert " "))
    $i))

(defun empty-line ()
  "Delete all the characters on the current line.
Return the number of deleted characters."
  (interactive)
  (let ($p)
   (setq $p (- (line-end-position) (line-beginning-position)))
   (delete-region (line-beginning-position) (line-end-position))
   $p))

(defun empty-delete-line ()
  "Remove all the characters on the line if not empty, delete the line otherwise."
  (interactive)
  (if (equal (line-beginning-position) (line-end-position))
      (progn (delete-backward-char 1) 1) (empty-line)))

(defun delete-always-line ()
  "Remove all the characters on the line if not empty, delete the line otherwise."
  (interactive)
  (let ($c)
    (if (equal (line-beginning-position) (line-end-position))
	(progn (delete-backward-char 1) 1)
	(progn (setq $c (empty-line))
	       (delete-backward-char 1) (+ $c 1)))))

(defun find-region-delimiters (ALLOW_SELECTION INCLUDE_CURRENT_LINE
                               ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  ""
 (let ($p $p1 $p2)
   ;; Save the current point
   (setq $p (point))
   ;; Find the region delimiters (and move the pointer back to its original position):
   ;; First check if we need to use the selected region
   (if (and (use-region-p) ALLOW_SELECTION)
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
   (make-pair :fst $p1 :snd $p2)))

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
    (setq $p1 (pair-fst $delimiters) $p2 (pair-snd $delimiters))
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

(defun replace-all-in (FROM TO &optional BEG END)
  "Replace all the occurrences of FROM by TO and return the number of characters
by which to shift the pointer, leaving the pointer at the shifted position.
Takes optional region delimiters as arguments."
  (let (($p0 (point)) ;; original position
        ($p (point)) ;; current position
        ($shift 0) ;; number of characters by which we shift the original position
        ($length-dif (- (length TO) (length FROM))) ;; shift of one replacement
        ($beg (or BEG (point-min)))
        ($end (or END (point-max)))
        )
    ;; Replace all the occurrences of FROM
    (goto-char $beg)
    (while (search-forward FROM $end t)
      (progn
        ;; Compute the pointer shift: if the current position is smaller or equal
        ;; than the original position with the current shift, add $length-dif
        ;; to the shift
        (setq $p (point))
        (when (<= $p (+ $p0 $shift)) (setq $shift (+ $shift $length-dif)))
        ;; Replace
        (replace-match TO)))
    ;; Move to the shifted position and return the shift
    (goto-char (+ $p0 $shift))
    $shift))

(defun replace-in-current-region (FROM TO ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                  ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  ""
  (let (($r (apply-partially 'replace-all-in FROM TO)))
    ;; Apply the replace function
    (apply-in-current-region $r ALLOW_SELECTION INCLUDE_CURRENT_LINE
                             ABOVE_PARAGRAPH BELOW_PARAGRAPH)))

(defun switch-assert-assume-in-current-region (ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                               ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  (interactive)
  "Check if there are occurrences of 'assert' or 'assert_norm in the current region.
   If so, replace them with 'assume'. Ohterwise, replace all the 'assume' with 'assert'."
  (let ($p $p1 $p2 $has-asserts $replace)
    ;; Find the region delimiters and restrain the region
    (setq $delimiters (find-region-delimiters ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                              ABOVE_PARAGRAPH BELOW_PARAGRAPH))
    (setq $p1 (pair-fst $delimiters) $p2 (pair-snd $delimiters))
    (save-restriction
      (narrow-to-region $p1 $p2)
      (setq $p (point))
      ;; Check if there are assertions to know whether to replace assertions
      ;; by assumptions or the revert
      (beginning-of-buffer)
      (setq $has-asserts (search-forward "assert" nil t))
      (goto-char $p)
      ;; Replace
      (if $has-asserts
          (progn
             (replace-all-in "assert_norm" "assume(*norm*)")
             (replace-all-in "assert" "assume"))
           (progn
             (replace-all-in "assume(*norm*)" "assert_norm")
             (replace-all-in "assume" "assert"))))))

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

;; From now onwards we use functions from the F* mode
(use-package fstar-mode
  :demand)

(defun consume-string-forward (STR &optional NO_ERROR)
  "If the pointer looks at string STR, moves the pointer after it. Otherwise,
returns nil or raises an error depending on NO_ERROR."
  (if (looking-at-p (regexp-quote STR))
      (progn (forward-char (length STR)) t)
    (if NO_ERROR nil (error (format "consume-string-forward %s failed" STR)))))      

(defun fstar-in-general-comment-p (&optional POS)
  (save-restriction
    (or (fstar-in-comment-p POS) (fstar-in-literate-comment-p))))

(defun search-forward-not-comment (STR &optional LIMIT)
    "Looks for the first occurrence of STR not inside a comment, returns t and
moves the pointer immediately after if it finds one, doesn't move the pointer
and returns nil otherwise."
    (let (($p (point)))
      (fstar--search-predicated-forward
       (lambda () (not (fstar-in-general-comment-p))) STR LIMIT)
      (not (= $p (point)))))

;; TODO: add to fstar-mode.el
(defun fstar--search-predicated-backward (test-fn needle &optional bound)
  "Search backward for matches of NEEDLE before BOUND satisfying TEST-FN."
  (when (fstar--search-predicated #'search-backward test-fn
                             #'fstar--adjust-point-backward needle bound)
    (goto-char (match-beginning 0))))

(defun search-backward-not-comment (STR &optional LIMIT)
    "Looks for the first occurrence of STR not inside a comment, returns t and
moves the pointer immediately before if it finds one, doesn't move the pointer
and returns nil otherwise."
    (let (($p (point)))
      (fstar--search-predicated-backward
       (lambda () (not (fstar-in-general-comment-p))) STR LIMIT)
      (not (= $p (point)))))

;; TODO: use forward-comment
(defun skip-comment (FORWARD &optional LIMIT)
  "Move the cursor forward or backward until we are out of a comment or we
reach the end of the buffer"
  (let ($stop)
    ;; Set the limit to the move
    (if FORWARD (setq $stop (or LIMIT (point-max)))
                (setq $stop (or LIMIT (point-min))))
    (cond
     ;; Inside a comment
     ((fstar-in-comment-p)
      (if FORWARD
          ;; Forward: go forward until we are out of the comment
          (while (and (fstar-in-comment-p) (< (point) $stop)) (forward-char))
        ;; Backward: we can use the parsing state to jump
        (goto-char (nth 8 (fstar--syntax-ppss (point))))))
     ;; Inside a literate comment
     ((fstar-in-literate-comment-p)
      (if FORWARD (if (search-forward "\n" $stop t) (point) (goto-char $stop))
        (if (search-backward "\n" $stop t) (point) (goto-char $stop))))
     (t (point)))))

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
  "Move until the current character is not in CHARS.
FORWARD controls the direction, LIMIT controls where to stop."
  (if FORWARD
      (skip-chars-forward CHARS LIMIT)
      (skip-chars-backward CHARS LIMIT)))

(defun skip-comments-and-spaces (FORWARD &optional LIMIT)
  "Move the cursor until we are out of a comment and there are no spaces.
FORWARD controls the direction, LIMIT delimits the region."
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
            (setq $continue nil)))))
    (point)))

(defun skip-forward-pragma (&optional LIMIT)
    "Skip a pragma instruction (#push-options, #pop-options...).
If we are at the beginning of a #push-options or #pop-options instruction,
move forward until we are out of it or reach LIMIT.
Returns the position where the pointer is left."
  (save-restriction
    (narrow-to-region (point) (if LIMIT LIMIT (point-max)))
    (let (($continue t) $go)
      (defun go (STR)
        (if (looking-at-p (regexp-quote STR))
            (progn (forward-char (length STR)) (setq $continue t) t)
          nil))
      (cond ((go "#set-options") ())
            ((go "#reset-options") ())
            ((go "#push-options") ())
            ((go "#pop-options") ())
            ((go "#restart-solver") ())
            ((go "#ligth") ())
            (t (setq $continue nil)))
      ;; Skip the parameters (the string) - note that there may be comments
      ;; between the pragma and the paramters
      (when $continue
        (skip-comments-and-spaces t)
        (forward-sexp)))))

(defun skip-forward-square-brackets (&optional LIMIT)
  "If look at '[', go after the closing ']'.
LIMIT delimits the end of the search."
  (save-restriction
    (narrow-to-region (point) (if LIMIT LIMIT (point-max)))
    (when (looking-at-p (regexp-quote "["))
      (forward-sexp)))
  (point))

(defun skip-forward-comments-pragmas-spaces (&optional LIMIT)
  "Go forward until there are no comments and pragma instructions.
Stop at LIMIT."
  (save-restriction
    (narrow-to-region (point) (or LIMIT (point-max)))
    (let (($continue t)
          ($p (point)))
      (while $continue
        (skip-comments-and-spaces t)
        (skip-forward-pragma)
        (when (or (= (point) $p) (= (point) (point-max)))
          (setq $continue nil))
        (setq $p (point))))))

(defun region-is-comments-and-spaces (BEG END &optional NO_NEWLINE)
  "Check if a region is only made of spaces and comments.
The region is delimited by BEG and END.
NO_NEWLINE controls whether newline characters are considered spaces or not."
  (let (($p (point)) ($continue t))
    (goto-char BEG)
    (skip-comments-and-spaces t END)
    (if (< (point) END) nil
      ;; If we reached the end: eventually check if there are new line characters
      (goto-char BEG)
      (if NO_NEWLINE (not (search-forward "\n" END t)) t))))

(defconst fstar-message-prefix "[F*] ")
(defconst fstar-tactic-message-prefix "[F*] TAC>> ")

(defconst messages-buffer "*Messages*")
;; Small trick to solve the undo problems: we use temporary buffer names which
;; start with a ' ' so that emacs deactivates undo by default in those buffers,
;; preventing the insertion of problematic undo-boundary.
;; Note that for now we switch buffers "by hand" rather than using the emacs
;; macros like with-current-bufferbecause it leaves a trace which helps debugging.
(defconst fstar-temp-buffer1 " *fstar-temp-buffer1*")
(defconst fstar-temp-buffer2 " *fstar-temp-buffer2*")


;; Meta information generated by tactics and output in the *Messages* buffer:
(cl-defstruct meta-info
  "Meta information extracted from the *Messages* buffer. Contains text as well
as the result returned by the post-processing function called on the data."
  data pp-res)

(cl-defstruct letb-term
  "A parsed let binded term of the form: 'let b = exp in'"
  beg end ;; delimiters for the whole expression
  bind ;; the binding (as a meta-info)
  b-beg b-end ;; delimiters
  exp ;; the expression (as a meta-info)
  e-beg e-end ;; delimiters
  is-var ;; nil if tuple
  )

(defun region-is-tuple (BEG END)
  "Returns t if the text region delimited by BEG and END is a tuple (simply
checks if there is a ',' inside"
  (save-excursion
    (save-restriction
      (goto-char BEG)
      (search-forward-not-comment "," END))))

(defun parse-letb-term (BEG END &optional NO_ERROR)
  "Parses the let binded term in a 'let x = y in' expression. Note that the region
delimited by BEG and END should start exactly with 'let' and end with 'in', put
aside potential whitespaces and comments."
  ;; We do things simple: we just look forward for the next '=' (this character
  ;; shouldn't appear in the 'x' term).
  ;; Then, in order to check whether the term is a variable or not, we just
  ;; look for the presence of ',' in it (in which case it is a tuple).
  (save-excursion
    (let ($beg $end $eq-end $b $b-beg $b-end $exp $e-beg $e-end $is-var $success $error-msg)
      (setq $success nil)
      ;; Restraigning
      (goto-char BEG)
      (skip-comments-and-spaces t END)
      (setq $beg (point))
      (goto-char END)
      (skip-comments-and-spaces nil $beg)
      (setq $end (point))
      (save-restriction
        (narrow-to-region $beg $end)
        (goto-char (point-min))
        ;; Ignore the 'let'
        (if (not (consume-string-forward "let" NO_ERROR))
            (when (not NO_ERROR) (setq $error-msg "could not find the 'let'"))
          ;; Success
          (skip-comments-and-spaces t (point-max))
          ;; Beginning of b
          (setq $b-beg (point))
          ;; Look for '='
          (if (not (search-forward-not-comment "="))
              (when (not NO_ERROR) (setq $error-msg "could not find the '='"))
            (setq $eq-end (point))
            ;; End of b
            (backward-char)
            (skip-comments-and-spaces nil $b-beg)
            (setq $b-end (point))
            ;; Beginning of exp
            (goto-char $eq-end)
            (skip-comments-and-spaces t (point-max))
            (setq $e-beg (point))
            ;; End of exp
            (goto-char (point-max))
            (backward-char (length "in")) ;; TODO: no check
            (skip-comments-and-spaces nil $e-beg)
            (setq $e-end (point))
            (setq $success t)
            ;; Check if b is a tuple
            (setq $is-var (not (region-is-tuple $b-beg $b-end)))
            )))
      ;; Process errors and return
      (if (not $success)
          ;; Failure
          (if NO_ERROR nil
            (error (format "parse-letb-term on '%s' failed: %s"
                           (buffer-substring-no-properties BEG END)
                           $error-msg)))
        ;; Success
        (let* ((bind (buffer-substring-no-properties $b-beg $b-end))
               (bind-mi (make-meta-info :data bind
                                        :pp-res (count-lines-in-string bind)))
               (exp (buffer-substring-no-properties $e-beg $e-end))
               (exp-mi (make-meta-info :data exp
                                       :pp-res (count-lines-in-string exp))))
          (make-letb-term :beg $beg :end $end
                          :bind bind-mi
                          :b-beg $b-beg :b-end $b-end
                          :exp exp-mi
                          :e-beg $e-beg :e-end $e-end
                          :is-var $is-var))
        ))))

(cl-defstruct subexpr
  "An expression of the form 'let _ = _ in', '_;' or '_' (return value)"
  beg end ;; point delimiters
  is-let-in ;; is of the form: 'let _ = _ in'
  has-semicol ;; is of the form: '_;'
  bterm ;; the term binded by the 'let' if of the form 'let _ = _ in'
  )

(defun parse-subexpr (BEG END)
  "Parses a sub-expression of the form 'let _ = _ in', '_;' or '_' (i.e.: a return
value) in the region delimited by BEG and END. Returns a subexpr."
  (let ($delimiters $beg $end $is-let-in $has-semicol $bterm)
    ;; Parse: 3 cases:
    ;; - let _ = _ in
    ;; - _;
    ;; - _
    (setq $is-let-in nil $has-semicol nil)
    ;; Note that there may be a comment/spaces at the beginning and/or at the end
    ;; of the processed region, which we need to skip:
    ;; - beginning
    (goto-char BEG)
    (skip-comments-and-spaces t)
    (setq $beg (point))
    ;; - end
    (goto-char END)
    (skip-comments-and-spaces nil $beg)
    (setq $end (point))
    ;; We do the regexp matching in a narrowed region
    (save-restriction
      (narrow-to-region $beg $end)
      ;; Check if the narrowed region matches: 'let _ = _ in'
      (goto-char (point-min))      
      (setq $is-let-in
            (re-search-forward "\\`let[[:ascii:][:nonascii:]]+in\\'" (point-max) t 1))
      (when $is-let-in (setq $bterm (parse-letb-term $beg $end)))
      ;; Check if the narrowed region matches: '_ ;'
      (goto-char (point-min))
      (setq $has-semicol
            ;; We could just check if the character before last is ';'
            (re-search-forward "\\`[[:ascii:][:nonascii:]]+;\\'" (point-max) t 1))
      ;; Otherwise: it is a return value (end of function)
      ) ;; end of regexp matching
    ;; Return
    (make-subexpr :beg $beg :end $end :is-let-in $is-let-in :has-semicol $has-semicol
                  :bterm $bterm)))


(defun space-after-p (&optional POS)
  "Return t if there is a space at the pointer's position."
  (seq-contains fstar--spaces (char-after POS)))

(defun space-before-p (&optional POS)
  "Return t if there is a space before the pointer's position."
  (seq-contains fstar--spaces (char-before POS)))

(defun is-in-spaces-p (&optional POS)
  "Return t if there are spaces before and after the pointer."
  (and (space-after-p POS) (space-before-p POS)))

(defun safe-backward-sexp (&optional ARG)
  "Same as (backward-sexp ARG) but returns nil instead of raising errors."
  (ignore-errors (backward-sexp ARG)))

(defun safe-forward-sexp (&optional ARG)
  "Same as (forward-sexp ARG) but returns nil instead of raising errors."
  (ignore-errors (forward-sexp ARG)))

(defun sexp-at-p (&optional POS ACCEPT_COMMENTS)
  "Find the sexp at POS.
Returns a pair of positions if succeeds, nil otherwise."
  (save-excursion
    (let (($not-ok nil) $beg $end)
      ;; Must not be in a comment (unless the user wants it) or surrounded by spaces
      (setq $not-ok (or (and (fstar-in-general-comment-p) (not ACCEPT_COMMENTS))
                        (is-in-spaces-p)))
      ;; Find the beginning and end positions
      (if $not-ok nil
        ;; End: if looking at space, this is the end position. Otherwise,
        ;; go to the end of the sexp
        (when (not (space-after-p)) (safe-forward-sexp))
        (setq $end (point))
        ;; Beginning: just go backward
        (safe-backward-sexp)
        (setq $beg (point))
        (make-pair :fst $beg :snd $end)))))

(defun sexp-at-p-as-string (&optional POS)
  "Return the sexp at POS."
  (let (($r (sexp-at-p)))
    (if $r (buffer-substring-no-properties (pair-fst $r) (pair-snd $r))
      nil)))

(defun find-encompassing-assert-assume-p (&optional POS BEG END)
  "Find the encompassing F* assert(_norm)/assume.
Takes an optional pointer position POS and region delimiters BEG and END.
Returns a pair of pairs of positions if found (for the assert identifier and
the content of the assert), nil otherwise."
  (save-excursion
    (save-restriction
      ;; The strategy is very simple: look for the closest previous asset/assume
      ;; which is not in a comment and such that, ignoring comments, the next
      ;; sexp contains the current point
      (let (($rbeg (if BEG BEG (point-min))) ;; region beginning
            ($rend (if END END (point-max))) ;; region end
            ($pos (if POS POS (point)))
            $abeg $aend ;; assert/assume beginning/end positions
            $pbeg $pend ;; proposition beginning/end positions
            $pred ;; predicate function (just for variable shadowing)
            )
        (narrow-to-region $rbeg $rend)
        ;; The predicate function for the search
        (defun $pred ()
          (save-match-data
            (save-excursion
              (let ($ar $str $pr)
                ;; Check that we are looking at an assert(_norm)/assume
                (setq $ar (sexp-at-p))
                (setq $abeg (pair-fst $ar) $aend (pair-snd $ar))
                (setq $str (buffer-substring-no-properties $abeg $aend))
                (if (not (or (string-equal $str "assert")
                             (string-equal $str "assert_norm")
                             (string-equal $str "assume")))
                    ;; Not ok
                    nil
                  ;; Ok: check if the pointer is inside the argument
                  (goto-char $aend)
                  (skip-comments-and-spaces t)
                  (setq $pbeg (point))
                  (safe-forward-sexp)
                  (setq $pend (point))
                  (and (<= $pbeg $pos) (>= $pend $pos)))))))
        ;; Search and return
        (when (fstar--re-search-predicated-backward '$pred "assert\\|assume" $rbeg)
          ;; Return
          (make-pair :fst (make-pair :fst $abeg :snd $aend)
                     :snd (make-pair :fst $pbeg :snd $pend))
          )))))

(defun find-assert-assume-p (&optional POS BEG END)
  "Find the F* assert(_norm)/assume at the pointer position.
Takes an optional pointer position POS and region delimiters BEG and END.
Returns a pair of pairs of positions if found (for the assert identifier and
the content of the assert), nil otherwise.
At the difference of find-encompassing-assert-assume-p, the pointer doesn't
have to be inside the assertion/assumption.  It can for instance be on an
``assert`` identifier."
  (save-excursion
    (save-restriction
      (let (($rbeg (if BEG BEG (point-min))) ;; region beginning
            ($rend (if END END (point-max))) ;; region end
            ($pos (if POS POS (point)))
            $sexp $pbeg $pend $str)
        ;; First check if we are not exactly on the identifier, otherwise
        ;; call find-encompassing-assert-assume-p
        (goto-char $pos)
        (setq $sexp (sexp-at-p))
        (setq $str (buffer-substring-no-properties (pair-fst $sexp) (pair-snd $sexp)))
        (if (or (string-equal $str "assert")
                (string-equal $str "assert_norm")
                (string-equal $str "assume"))
            ;; Ignore comments and parse the next sexp
            (progn
              (goto-char (pair-snd $sexp))
              (skip-comments-and-spaces t)
              (setq $pbeg (point))
              (safe-forward-sexp)
              (setq $pend (point))
              (make-pair :fst $sexp :snd (make-pair :fst $pbeg :snd $pend)))
          ;; Otherwise, call find-encompassing-assert-assume-p
          (goto-char $pos)
          (find-encompassing-assert-assume-p POS BEG END))))))

(defun find-encompassing-let-in (TERM_BEG TERM_END &optional BEG END)
  "Look for the 'let _ = _ in' or '_;' expression around the term.
The term is indicated by TERM_BEG and TERM_END.
Region is delimited by BEG and END.
Returns an optional subexpr."
  (save-excursion
    (save-restriction
      (let (($rbeg (if BEG BEG (point-min))) ;; region beginning
            ($rend (if END END (point-max))) ;; region end
            $has-semicol
            $beg $end
            $b-beg $b-end
            $e-beg $e-end
            $bterm
            $tmp
            )
        ;; First look for a subsequent ';'
        (goto-char TERM_END)
        (skip-comments-and-spaces t)
        (setq $has-semicol (looking-at-p (regexp-quote ";")))
        (if $has-semicol
            ;; If found a semicol
            (progn
              (setq $end (+ (point) 1))
              (make-subexpr :beg TERM_BEG :end $end :is-let-in nil :has-semicol t :bterm nil))
          ;; Otherwise: look for a 'let _ = _ in' construct
          ;; First look for the '=' (note that it doesn't work with sexpressions)
          (goto-char TERM_BEG)
          (skip-comments-and-spaces nil)
          (backward-char)
          ;; We should look at an '=' and not be preceded by a '=' (not sure it
          ;; is necessary to check the character before)
          (if (not (and (char-equal (char-after) ?=)
                        (not (char-equal (char-before) ?=))))
              ;; Failed
              (make-subexpr :beg TERM_BEG :end TERM_END :is-let-in nil :has-semicol nil :bterm nil)
            ;; Save position
            (skip-comments-and-spaces nil)
            (setq $b-end (point))
            ;; Look for the closest previous let which is not in a comment
            (if (not (search-backward-not-comment "let"))
                ;; Failed
                (make-subexpr :beg TERM_BEG :end TERM_END :is-let-in nil :has-semicol nil :bterm nil)
              ;; Return
              (setq $beg (point))
              (forward-sexp)
              (skip-comments-and-spaces t)
              (setq $b-beg (point)) ;; $b-end set previously
              ;; Look for the 'in'
              (goto-char TERM_END)
              (skip-comments-and-spaces t)
              (setq $tmp (sexp-at-p))
              (if (not (string-equal "in" (sexp-at-p-as-string)))
                  ;; Failed
                  (make-subexpr :beg TERM_BEG :end TERM_END :is-let-in nil :has-semicol nil :bterm nil)
                (forward-sexp)
                (setq $end (point))                
                (setq $bterm (make-letb-term :beg $beg :end $end :bind
                                             (make-meta-info :data (buffer-substring-no-properties $b-beg $b-end)
                                                             :pp-res nil)
                                             :b-beg $b-beg :b-end $b-end
                                             :exp
                                             (make-meta-info :data (buffer-substring-no-properties TERM_BEG TERM_END)
                                                             :pp-res nil)
                                             :e-beg TERM_BEG :e-end TERM_END))
                (make-subexpr :beg $beg :end $end :is-let-in t :has-semicol nil :bterm $bterm))
                )))))))                                    
          

;; We duplicate the assertions structure from the F* side
(cl-defstruct assertions pres posts)

(defun type-info-rawest-type (ty)
  "Returns the 'rawest' type from a type-info"
  (or (type-info-rty-raw ty) (type-info-ty ty)))

(defun param-info-requires-cast (param)
  "Returns t if the types-comparison from param is 'Unknown'"
  (string= (meta-info-data (param-info-types-comparison param)) "Unknown"))

(defun param-info-requires-refinement (param)
  "Returns t if the types-comparison from param is 'Same_raw_type' or 'Unknown'"
  (or
   (string= (meta-info-data (param-info-types-comparison param)) "Unknown")
   (string= (meta-info-data (param-info-types-comparison param)) "Same_raw_type")))

(defun search-data-delimiter (delimiter backward consume-delimiter no-error
                              &optional BEG END)
  "Searchs for delimiter in the direction given by backward. consume-delimiter
controls whether to leave the pointer where it is or backtrack to put it just
before the delimiter. If the delimiter could not be found, raises an error if
no-error is nil, returns nil otherwise."
  (let ((beg (or BEG (point-min)))
        (end (or END (point-max)))
        p)
    (if backward
        (setq p (search-backward delimiter beg t))
      (setq p (search-forward delimiter end t)))
    (unless (or no-error p)
      (error (concat "Could not find the delimiter: " delimiter)))
    (when (and p (not consume-delimiter))
      (if backward (goto-char (+ p (length delimiter)))
        (goto-char (- p (length delimiter)))))
    (if p (point) nil)))

(defun extract-info-from-buffer (prefix id &optional no-error post-process LIMIT)
  "Extracts meta data from the current buffer and optionally post-processes it.
Returns a meta-info structure (or nil if we we couldn't find the information)
Leaves the pointer at the end of the parsed data (just before the next data)."
  ;; Find where the data is
  (let* ((beg (point))
         (end (or LIMIT (point-max)))
         (full-id (concat prefix id ":\n"))
         (full-id-length (length full-id))
         p p1 p2 (res nil) (pp-res nil))
    ;; Find the delimiters
    (setq p (search-data-delimiter full-id nil t no-error beg end))
    ;; If we found the full-id, extract the data
    (when p
      ;; Retrieve the boundaries of the information sub-buffer
      ;; - beginning:
      (setq p1 (point))
      ;; - end: we look for the next occurence of 'prefix' followed by a '\n'
      (backward-char 1)
      (setq p2 (search-data-delimiter (concat "\n" prefix ":") nil nil no-error (point) end))
      ;; From now onwards, the pointer is at the position where it should be
      ;; left in the original buffer
      (setq p2 (point))
      (when (< p2 (- p1 1)) (error "extract-info-from-messages bug")) ;; should not happen
      ;; If the data is not null, post-process it in place
      (when (>= p2 p1)
        ;; Start by restreigning the region
        (save-restriction
          (narrow-to-region p1 p2)
          ;; Post-process the data
          (when post-process (setq pp-res (funcall post-process)))
          ;; Save the content of the whole narrowed region
          (setq res (buffer-substring-no-properties (point-min) (point-max)))
          ;; The size of the region might have changed: go to the end, save
          ;; save the new point to p2
          (goto-char (point-max)))
        ;; Update the end of the region
        (setq p2 (point))))
    ;; Return
    (when fstar-extended-debug
      (let ((res-str (if res (concat "[" res "]") "nil")))
        (log-dbg "extract-info-from-messages:\n- prefix: %s\n- id: %s\n- res: %s "
                 prefix id res-str)))
    (if res (make-meta-info :data res :pp-res pp-res) nil))) ;; end of function

(defun count-lines-in-string (STR)
  "Count the number of lines in a string"
  (save-match-data
    (let (($num-lines 1))
      (while (string-match (regexp-quote "\n") STR)
        (setq $num-lines (+ $num-lines 1)))
      $num-lines)))

(defun meta-info-post-process ()
  "Data post-processing function: counts the number of lines.
Also greedily replaces some identifiers (Prims.l_True -> True...).
Returns the number of lines."
  ;; Count the lines
  (let ((num-lines (count-lines (point-min) (point-max))))
    ;; Greedy replacements
    (replace-all-in "Prims.l_True" "True")
    (replace-all-in "Prims.l_False" "False")
    ;; Return the number of lines
    num-lines
    )) ;; end of post-process fun  

(defun extract-string-from-buffer (prefix id &optional no-error LIMIT)
  (log-dbg "extract-string-from-buffer:\n- prefix: %s\n- id: %s" prefix id)
  (extract-info-from-buffer prefix id no-error nil LIMIT))

(defun extract-term-from-buffer (prefix id &optional no-error LIMIT)
  (log-dbg "extract-term-from-buffer:\n- prefix: %s\n- id: %s" prefix id)
  (extract-info-from-buffer prefix id no-error
                            (apply-partially 'meta-info-post-process)
                            LIMIT))

(defun extract-assertion-from-buffer (prefix id index &optional no-error LIMIT)
  "Extracts an assertion from the current buffer. Returns a meta-info structure."
  (log-dbg "extract-assertion-from-buffer:\n- prefix: %s\n- id: %s\n- index: %s"
           prefix id (number-to-string index))
  (let* ((full-id (concat id (number-to-string index))))
    (extract-term-from-buffer prefix full-id no-error LIMIT)))

(defun extract-assertion-list-from-buffer (prefix id index num
                                           &optional no-error LIMIT)
  "Extract a given number of assertions as a list of meta-info."
  (log-dbg "extract-assertion-list-from-buffer:\n\
- prefix: %s\n- id: %s\n- index: %s\n- num: "
           prefix id (number-to-string index) (number-to-string num))
  (if (>= index num) nil
    (let ((param nil) (params nil))
      ;; Extract (forward) the assertion given by 'index'
      (setq param
            (extract-assertion-from-buffer prefix id index no-error LIMIT))
      ;; Recursive call
      (setq params
            (extract-assertion-list-from-buffer prefix id (+ index 1) num
                                                no-error LIMIT))
      (cons param params))))

(defun extract-assertion-num-and-list-from-buffer (prefix id
                                                   &optional no-error LIMIT)
  "Reads how many assertions to extract from the current buffer, then
extracts those assertions."
  (log-dbg "extract-assertion-num-and-list-from-buffer:\n\
- prefix: %s\n- id: %s" prefix id)
  ;; Extract the number of assertions
  (let ((id-num (concat id ":num"))
        (id-prop (concat id ":prop"))
        num num-data)
    (setq num-data (extract-string-from-buffer prefix id-num no-error LIMIT))
    (setq num (string-to-number (meta-info-data num-data)))
    (log-dbg "> extracting %s terms" num)
    ;; Extract the proper number of parameters
    (extract-assertion-list-from-buffer prefix id-prop 0 num no-error
                                        LIMIT)))

(defun extract-assertions-from-buffer (prefix id
                                                   &optional no-error LIMIT)
  "Extracts an assertion structure from the current buffer"
  (log-dbg "extract-assertions-from-buffer:\n\
- prefix: %s\n- id: %s" prefix id)
  ;; Extract the number of assertions
  (let ((id-pres (concat id ":pres"))
        (id-posts (concat id ":posts"))
        pres posts)
    (setq pres (extract-assertion-num-and-list-from-buffer prefix id-pres no-error LIMIT))
    (setq posts (extract-assertion-num-and-list-from-buffer prefix id-posts no-error LIMIT))
    (make-assertions :pres pres :posts posts)))

(defun copy-data-from-messages-to-buffer (beg-delimiter end-delimiter
                                          include-delimiters dest-buffer
                                          &optional no-error clear-dest-buffer)
    "When extracting information from the *Messages* buffer, we start by locating
it by finding its begin and end delimiters, then copy it to another buffer where
we can parse/modify it. The reasons are that it is easier to modify the data in
place (while the *Messages* buffer is read-only) and that more messages
may be sent to the *Messages* buffer (by the current process or other process)
which may mess up with the data treatment and prevents us from using commands
like narrow-to-region. Moreover, it makes debugging easier. The function returns
the pair of point coordinates delimiting the copied data in the destination
buffer.
include-delimiters controls whether to copy the delimiters or not"
    ;; This command MUST NOT send any message to the *Messages* buffer
    (let ((prev-buffer (current-buffer))
          (backward t)
          (beg nil) (end nil) (p1 nil) (p2 nil))
      ;; Switch to the *Messages* buffer
      (switch-to-buffer messages-buffer)
      ;; Find the delimiters
      (goto-char (point-max))
      (setq beg (search-data-delimiter beg-delimiter t include-delimiters no-error))
      (setq end (search-data-delimiter end-delimiter nil include-delimiters no-error))
      ;; Check if successful
      (if (or (not beg) (not end))
          ;; Failure
          (progn
            (when (not no-error)
              (error (concat "copy-data-from-messages-to-buffer: "
                             "could not find the delimiters: "
                             beg-delimiter ", " end-delimiter)))
            nil)
        ;; Success
        ;; Copy in the dest-buffer
        (kill-ring-save beg end)
        (switch-to-buffer dest-buffer)
        (goto-char (point-max))
        (when clear-dest-buffer (erase-buffer))
        (setq p1 (point))
        (yank)
        (setq p2 (point))
        ;; Switch back to the original buffer
        (switch-to-buffer prev-buffer)
        ;; Return
        (make-pair :fst p1 :snd p2))))

(defun clean-data-from-messages (&optional BEG END)
    "Once data has been copied from the messages buffer, it needs some processing
to be cleaned before being parsed: this function cleans the data in the current
buffer."
    (let (new-end)
      (setq-default BEG (point))
      (setq-default END (point-max))
      (save-restriction
        (narrow-to-region BEG END)
        ;; Start by removing all the occurrences of '[F*] TAC' and '[F*]':
        ;; - make sure they all start by '\n'
        (goto-char (point-min))
        (insert "\n")
        ;; - replace (the order is important)
        (replace-all-in (concat "\n" fstar-tactic-message-prefix) "\n")
        (replace-all-in (concat "\n" fstar-message-prefix) "\n")
        ;; - remove the introduced '\n' (note that the pointer will be left at
        ;; its original position
        (goto-char (point-min))
        (delete-char 1)
        ;; Save the new region end
        (goto-char (point-max))
        (setq new-end (point))
        (goto-char (point-min)))
      ;; Return the new end of the region
      (+ (point) new-end)))

(defun extract-assertions-from-messages (prefix id &optional process-buffer no-error
                                         clear-process-buffer)
  "Extracts assertions from the *Messages* buffer. Returns an assertions structure.
process-buffer is the buffer to use to copy and process the raw data
(*fstar-data1* by default)."
  (setq-default process-buffer fstar-temp-buffer2)
  (log-dbg "extract-assertions-from-messages:\n\
- prefix: %s\n- id: %s\n- process buffer: '%s'\n" prefix id process-buffer)
  (let ((prev-buffer (current-buffer))
        (region nil)
        (result nil)
        (beg-delimiter (concat "[F*] TAC>> " prefix id ":BEGIN"))
        (end-delimiter (concat "[F*] TAC>> " prefix id ":END")))
    ;; Copy the data
    (setq region (copy-data-from-messages-to-buffer beg-delimiter end-delimiter
                                                    t process-buffer no-error
                                                    clear-process-buffer))
    (if (not region)
        (progn
          (when (not no-error)
            (error (concat "extract-eterm-info-from-messages (prefix: "
                           prefix ") (id: " id "): "
                           "could not find the region to copy from *Messages*")))
          nil)
      ;; Switch to the process buffer
      (switch-to-buffer process-buffer)
      (goto-char (pair-fst region))
      ;; Restrain the region and process it
      (save-restriction
        (narrow-to-region (pair-fst region) (pair-snd region))
        ;; Clean
        (clean-data-from-messages)
        ;; Extract the eterm-info
        (setq result (extract-assertions-from-buffer prefix id no-error)))
      ;; Switch back to the original buffer
      (switch-to-buffer prev-buffer)
      ;; Return
      result)))

(defun insert-with-indent (indent-str txt &optional indent-first-line)
  (when indent-first-line (insert indent-str))
  (insert (replace-in-string "\n" (concat "\n" indent-str) txt)))

(defun generate-assert-from-term (indent-str after-term data &optional comment)
  "Inserts an assertion in the code. after-term must be t if the assert is
after the focused term, nil otherwise. comment is an optional comment"
  (when data
    ;; If we are after the studied term: insert a newline
    (when after-term (insert "\n"))
    (when comment
      (insert indent-str)
      (insert comment)
      (insert "\n"))
    (insert indent-str)
    (insert "assert(")
    (when (> (meta-info-pp-res data) 1)
      (insert "\n")
      (insert indent-str)
      (insert "  "))
    (insert-with-indent (concat indent-str "  ") (meta-info-data data))
    (insert ");")
    ;; If we are before the studied term: insert a newline
    (when (not after-term) (insert "\n"))))

(defun insert-assert-pre-post--continuation (indent-str p1 p2 PARSE_RESULT overlay
                                             status response)
  "Process the information output by F* to add it to the user code.
If F* succeeded, extracts the information and adds it to the proof"
  (unless (eq status 'interrupted)
    ;; Delete the overlay
    (delete-overlay overlay)
    ;; Display the message and exit if error
    (if (eq status 'success)
        (progn
          (log-dbg "F* succeeded")
          ;; The sent query "counts for nothing" so we need to pop it to reset
          ;; F* to its previous state
          (fstar-subp--pop))
      (progn
        (when (y-or-n-p "F* failed: do you want to see the F* query?")
          (switch-to-buffer fstar-temp-buffer1))
        (error "F* failed")))
    ;; If we reach this point it means there was no error: we can extract
    ;; the generated information and add it to the code
    ;;
    ;; Extract the data. Note that we add two spaces to the indentation, because
    ;; if we need to indent the data, it is because it will be in an assertion.
    (let ((assertions (extract-assertions-from-messages "ainfo" ""
                                                  fstar-temp-buffer2 t t)))
      ;; Print the information
      ;; - before the focused term
      (goto-char p1)
      (dolist (a (assertions-pres assertions))
        (generate-assert-from-term indent-str nil a))
      ;; - after the focused term
      (forward-char (- p2 p1))
      (dolist (a (assertions-posts assertions))
        (generate-assert-from-term indent-str t a))
      )))

(defun shift-letb-term-pos (SHIFT TERM)
  "Shift hy SHIFT the positions in the letb-term TERM.
Return the updated letb-term"
  (setf (letb-term-beg TERM) (+ SHIFT (letb-term-beg TERM)))
  (setf (letb-term-end TERM) (+ SHIFT (letb-term-end TERM)))
  (setf (letb-term-e-beg TERM) (+ SHIFT (letb-term-e-beg TERM)))
  (setf (letb-term-e-end TERM) (+ SHIFT (letb-term-e-end TERM)))
  TERM)

(defun shift-subexpr-pos (SHIFT SUBEXPR)
  "Shift by SHIFT the positions in the subexpr SUBEXPR.
Return the updated subexpr."
  (setf (subexpr-beg SUBEXPR) (+ SHIFT (subexpr-beg SUBEXPR)))
  (setf (subexpr-end SUBEXPR) (+ SHIFT (subexpr-end SUBEXPR)))
  (when (subexpr-bterm SUBEXPR) (shift-letb-term-pos SHIFT (subexpr-bterm SUBEXPR)))
  SUBEXPR)

(defun copy-def-for-meta-process (END SUBEXPR DEST_BUFFER PP_INSTR)
  "Copy code for meta-processing and update the parsed result positions.
Leaves the pointer at the end of the DEST_BUFFER where the code has been copied.
PP_INSTR is the post-processing instruction to insert just before the definition."
  (let ($beg $attr-beg $original-length $new-length $shift $res)
    (goto-char (fstar-subp--untracked-beginning-position))
    (setq $beg (point))
    ;; - copy to the destination buffer
    (kill-ring-save $beg END)
    (switch-to-buffer DEST_BUFFER)
    (erase-buffer)
    (yank)
    ;; Remove the attributes before the definition (we will replace them)
    (goto-char (point-min))
    (skip-forward-comments-pragmas-spaces)
    (setq $attr-beg (point)) ;; if there is an attribute, it should be here
    (skip-forward-square-brackets) ;; (optionally) go over the attribute
    (delete-region $attr-beg (point)) ;; delete the attribute
    (skip-forward-comments-pragmas-spaces)
    ;; Insert an option to deactivate the proof obligations
    (insert "#push-options \"--admit_smt_queries true\"\n")
    ;; Insert the post-processing instruction
    (insert "[@(FStar.Tactics.postprocess_with (")
    (insert PP_INSTR)
    (insert "))]\n")
    ;; Compute the shift: the shift is just the difference of length between the
    ;; content in the destination buffer and the original content, because all
    ;; the deletion/insertion should have happened before the points of interest
    (setq $original-length (- END $beg)
          $new-length (- (point-max) (point-min)))
    (setq $shift (- $new-length $original-length))
    (setq $shift (- $shift $beg))
    ;; Shift and return the parsing information
    (setq $res (copy-subexpr SUBEXPR))
    (when (subexpr-bterm SUBEXPR)
      (setf (subexpr-bterm $res) (copy-letb-term (subexpr-bterm SUBEXPR))))
    (shift-subexpr-pos $shift $res)))

(defun query-fstar-on-buffer-content (OVERLAY_END PAYLOAD CONTINUATION)
  "Send PAYLOAD to F* and call CONTINUATION on the result.
CONTINUATION must an overlay, a status and a response as arguments.
OVERLAY_END gives the position at which to stop the overlay."
  (let* (($beg (fstar-subp--untracked-beginning-position))
         $overlay)
  ;; Create the overlay
  (setq $overlay (make-overlay (fstar-subp--untracked-beginning-position)
                               OVERLAY_END (current-buffer) nil nil))
  (fstar-subp-remove-orphaned-issue-overlays (point-min) (point-max))
  (overlay-put $overlay 'fstar-subp--lax nil)
  (fstar-subp-set-status $overlay 'busy)
  ;; Query F*
  (log-dbg "sending query to F*:[\n%s\n]" PAYLOAD)
  (fstar-subp--query (fstar-subp--push-query $beg `full PAYLOAD)
                     (apply-partially CONTINUATION $overlay))))

(defun insert-assert-pre-post--process (INDENT_STR P1 P2 SUBEXPR)
  "Generate the F* query for insert-assert-pre-post and query F*."
  (let ($cbuffer $subexpr $p1 $p2 $prefix $prefix-length $payload)
    ;; Remember which is the original buffer
    (setq $cbuffer (current-buffer))
    ;; Copy and start processing the content
    (setq $subexpr (copy-def-for-meta-process P2 SUBEXPR fstar-temp-buffer1
                                              "PrintTactics.pp_analyze_effectful_term false"))
    ;; We are now in the destination buffer
    ;; Modify the copied content and leave the pointer at the end of the region
    ;; to send to F*
    ;;
    ;; Insert the ``focus_on_term`` indicator at the proper place, together
    ;; with an admit after the focused term.
    ;; Note that we don't need to keep track of the positions modifications:
    ;; we will send the whole buffer to F*.
    (setq $p1 (subexpr-beg $subexpr) $p2 (subexpr-end $subexpr))
    ;; Prefix
    (goto-char $p1)
    (setq $prefix "let _ = PrintTactics.focus_on_term in ")
    (setq $prefix-length (length $prefix))
    (insert $prefix)
    ;; Suffix
    (goto-char (+ $p2 $prefix-length))
    ;; Insert an admit if it is a 'let' or a ';' expression
    (when (or (subexpr-is-let-in $subexpr) (subexpr-has-semicol $subexpr))
      (end-of-line) (newline) (indent-according-to-mode) (insert "admit()"))
    ;; Copy the buffer content
    (setq $payload (buffer-substring-no-properties (point-min) (point-max)))
    ;; We need to switch back to the original buffer to query the F* process
    (switch-to-buffer $cbuffer)    
    ;; Query F*
    (query-fstar-on-buffer-content P2 $payload
                                   (apply-partially #'insert-assert-pre-post--continuation
                                                    INDENT_STR P1 P2 SUBEXPR))))

(defun generate-fstar-check-conditions ()
  "Check that it is safe to run some F* meta-processing."
  (save-excursion
    (let (($p (point)) $next-point)
      ;; F* mustn't be busy as we won't push a query to the queue but will directly
      ;; query the F* sub-process: if some processes are queued, we will mess up
      ;; with the internal proof state
      (when (fstar-subp--busy-p) (user-error "The F* process must be live and idle"))
      ;; Retract so that the current point is not in a processed region
      (fstar-subp-retract-until $p)
      ;; Check if the point is in the next block to process: if not, abort.
      ;; If we can't compute the next block it is (quite) likely that there are
      ;; no previous blocks to process.
      (setq $next-point (fstar-subp--find-point-to-process 1))
      (when (and $next-point (< $next-point $p))
        (user-error (concat "There may be unprocessed definitions above the "
                            "current position: they must be processed"))))))

(defun compute-local-indent-p (&optional POS)
  "Return a string corresponding to the indentation up to POS.
If the characters between the beginning of the line and the current position
are comments and spaces, the returned string is equal to those - the reason
is that it allows formatting of ghosted code (which uses (**)).
Otherwise, the string is made of a number of spaces equal to the column position"
  (save-restriction
    (let* (($ip2 (if POS POS (point)))
           ($ip1 (progn (beginning-of-line) (point)))
           ($indent (- $ip2 $ip1)))
      (if (region-is-comments-and-spaces $ip1 $ip2)
          (buffer-substring-no-properties $ip1 $ip2)
        (make-string $indent ? )))))

(defun split-assert-assume-conjuncts ()
  "Split the conjunctions in an assertion/assumption."
  (interactive)
  (let ($tbeg $passert $a-beg $a-end $p-beg $p-end $subexpr $subexpr1 $indent-str $beg $end
        $cbuffer $prefix $prefix-length $payload)
  (log-dbg "split-assert-conjuncts")
  ;; Sanity check
  (generate-fstar-check-conditions)
  ;; Parse the assertion/assumption. Note that we may be at the beginning of a
  ;; line with an assertion/assumption, so we first try to move. More
  ;; specifically, it is safe to ignore comments and space if we are surrounded
  ;; by spaces or inside a comment.
  (setq $tbeg (fstar-subp--untracked-beginning-position))
  (when (or (is-in-spaces-p) (fstar-in-comment-p)) (skip-comments-and-spaces t))
  (setq $passert (find-assert-assume-p (point) $tbeg))
  (when (not $passert) (error "Pointer not over an assert/assert_norm/assume"))
  ;; Parse the encompassing let (if there is)
  (setq $a-beg (pair-fst (pair-fst $passert))
        $a-end (pair-snd (pair-fst $passert))
        $p-beg (pair-fst (pair-snd $passert))
        $p-end (pair-snd (pair-snd $passert)))
  (setq $subexpr (find-encompassing-let-in $a-beg $p-end))
  (when (not $subexpr) (error "Could not parse the enclosing expression"))
  ;; Compute the indentation
  (setq $indent-str (compute-local-indent-p (subexpr-beg $subexpr)))
  ;; Expand the region to ignore comments
  (goto-char (subexpr-beg $subexpr))
  (skip-comments-and-spaces nil (point-at-bol))
  (setq $beg (point))
  (goto-char (subexpr-end $subexpr))
  (skip-comments-and-spaces t (point-at-eol))
  (setq $end (point))
  ;; Remember which is the original buffer
  (setq $cbuffer (current-buffer))
  ;; Copy and start processing the content
  (setq $subexpr1 (copy-def-for-meta-process $end $subexpr fstar-temp-buffer1
                                            "PrintTactics.pp_split_assert_conjs false"))
  ;; We are now in the destination buffer
  ;; Insert the ``focus_on_term`` indicator at the proper place, together
  ;; with an admit after the focused term.
  ;; Note that we don't need to keep track of the positions modifications:
  ;; we will send the whole buffer to F*.
  ;; Prefix
  (goto-char (subexpr-beg $subexpr1))
  (setq $prefix "let _ = PrintTactics.focus_on_term in ")
  (setq $prefix-length (length $prefix))
  (insert $prefix)
  ;; Suffix
  (goto-char (+ (subexpr-end $subexpr1) $prefix-length))
  ;; Insert an admit if it is a 'let' or a ';' expression
  (when (or (subexpr-is-let-in $subexpr1) (subexpr-has-semicol $subexpr1))
    (end-of-line) (newline) (indent-according-to-mode) (insert "admit()"))
  ;; Copy the buffer content
  (setq $payload (buffer-substring-no-properties (point-min) (point-max)))
  ;; We need to switch back to the original buffer to query the F* process
  (switch-to-buffer $cbuffer)
  ;; Query F*
  (query-fstar-on-buffer-content $end $payload
                                 (apply-partially #'insert-assert-pre-post--continuation
                                                  $indent-str $beg $end $subexpr1))))

(defun unfold-in-assert-assume ()
  "Unfold an identifier in an assertion/assumption."
  (interactive)
  (let ($id $tbeg $passert $a-beg $a-end $p-beg $p-end $subexpr $subexpr1 $shift
        $indent-str $beg $end $cbuffer $payload $insert-shift $insert-and-shift)
  (log-dbg "unfold-in-assert-assume")
  ;; Sanity check
  (generate-fstar-check-conditions)
  ;; Find the identifier
  (setq $id (sexp-at-p))
  (when (not $id) (error "Pointer not over a term"))
  ;; Parse the assertion/assumption.
  (setq $tbeg (fstar-subp--untracked-beginning-position))
  (setq $passert (find-assert-assume-p (point) $tbeg))
  (when (not $passert) (error "Pointer not over an assert/assert_norm/assume"))
  ;; Parse the encompassing let (if there is)
  (setq $a-beg (pair-fst (pair-fst $passert))
        $a-end (pair-snd (pair-fst $passert))
        $p-beg (pair-fst (pair-snd $passert))
        $p-end (pair-snd (pair-snd $passert)))
  (setq $subexpr (find-encompassing-let-in $a-beg $p-end))
  (when (not $subexpr) (error "Could not parse the enclosing expression"))
  ;; Compute the indentation
  (setq $indent-str (compute-local-indent-p (subexpr-beg $subexpr)))
  ;; Expand the region to ignore comments
  (goto-char (subexpr-beg $subexpr))
  (skip-comments-and-spaces nil (point-at-bol))
  (setq $beg (point))
  (goto-char (subexpr-end $subexpr))
  (skip-comments-and-spaces t (point-at-eol))
  (setq $end (point))
  ;; Remember which is the original buffer
  (setq $cbuffer (current-buffer))
  ;; Copy and start processing the content
  (setq $subexpr1 (copy-def-for-meta-process $end $subexpr fstar-temp-buffer1
                                            "PrintTactics.pp_unfold_in_assert_or_assume false"))
  ;; We are now in the destination buffer
  ;; Insert the ``focus_on_term`` indicators at the proper places, together
  ;; with an admit after the focused term.
  ;; Prefixes:
  (setq $insert-shift 0)
  (defun $insert-and-shift (STR)
    (setq $insert-shift (+ $insert-shift (length STR)))
    (insert STR))
  ;; - for the identifier - note that we need to compute the shift between the
  ;;   buffers
  (setq $shift (+ (- (subexpr-beg $subexpr1) (subexpr-beg $subexpr)) 1))
  (goto-char (+ (pair-snd $id) $shift))
  ($insert-and-shift "))")
  (goto-char (+ (pair-fst $id) $shift))
  ($insert-and-shift "(let _ = PrintTactics.focus_on_term in (")
  ;; - for the admit - note that the above insertion should have been made
  ;;   below the point where we now insert
  (goto-char (subexpr-beg $subexpr1))
  ($insert-and-shift "let _ = PrintTactics.focus_on_term in\n")
  ;; Suffix
  (goto-char (+ (subexpr-end $subexpr1) $insert-shift))
  ;; Insert an admit if it is a 'let' or a ';' expression
  (when (or (subexpr-is-let-in $subexpr1) (subexpr-has-semicol $subexpr1))
    (end-of-line) (newline) (indent-according-to-mode) (insert "admit()"))
  ;; Copy the buffer content
  (setq $payload (buffer-substring-no-properties (point-min) (point-max)))
  ;; We need to switch back to the original buffer to query the F* process
  (switch-to-buffer $cbuffer)
  ;; Query F*
  (query-fstar-on-buffer-content $end $payload
                                 (apply-partially #'insert-assert-pre-post--continuation
                                                  $indent-str $beg $end $subexpr1))))

(defun insert-assert-pre-post ()
  "Insert assertions with proof obligations and postconditions around a term.
TODO: take into account if/match branches"
  (interactive)
  (log-dbg "insert-assert-pre-post")
  ;; Sanity check
  (generate-fstar-check-conditions)
  (let ($next-point $beg $p $delimiters $indent $indent-str
        $p1 $p2 $parse-result $cp1 $cp2
        $is-let-in $has-semicol $current-buffer)
    ;; Restrict the region
    (setq $p (point))
    (setq $beg (fstar-subp--untracked-beginning-position))
    (setq $p (- $p $beg))
    ;; Find in which region the term to process is
    (setq $delimiters (find-region-delimiters t t nil nil))
    (setq $p1 (pair-fst $delimiters) $p2 (pair-snd $delimiters))
    ;; Expand the region: ignore comments, and try to reach a beginning/end of
    ;; line for the beginning/end of the region
    ;; - beginning:
    ;; -- if we are inside a comment, get out of it
    (goto-char $p1)
    (skip-comment nil)
    (setq $p1 (point))
    ;; -- then try to reach the beginning of the line
    (let ($limit)
      (beginning-of-line)
      (setq $limit (point))
      (goto-char $p1)
      (skip-comments-and-spaces nil $limit)
      (setq $p1 (point)))
    ;; - end: same
    ;; -- if we are inside a comment, get out of it
    (goto-char $p2)
    (skip-comment t)
    (setq $p2 (point))
    ;; -- then try to reach the beginning of the line
    (let ($limit)
      (end-of-line)
      (setq $limit (point))
      (goto-char $p2)
      (skip-comments-and-spaces t $limit)
      (setq $p2 (point)))
    ;; Parse the term
    (setq $parse-result (parse-subexpr $p1 $p2))
    (setq $cp1 (subexpr-beg $parse-result))
    ;; Debug information
    (cond ((subexpr-is-let-in $parse-result) (log-dbg "Parsed expression: 'let _ = _ in'"))
          ((subexpr-has-semicol $parse-result) (log-dbg "Parsed expression: '_;'"))
          (t (log-dbg "Parsed expression: '_'")))
    ;; Compute the indentation
    (setq $indent-str (compute-local-indent-p $cp1))
    ;; Process the term
    (insert-assert-pre-post--process $indent-str $p1 $p2 $parse-result)))

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

(global-set-key (kbd "C-c C-e") 'insert-assert-pre-post)
(global-set-key (kbd "C-c C-s C-u") 'split-assert-assume-conjuncts)
(global-set-key (kbd "C-c C-s C-f") 'unfold-in-assert-assume)


