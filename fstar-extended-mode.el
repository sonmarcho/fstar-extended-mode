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

;;; Code:

;;; Imports
(use-package fstar-mode :demand)

;;; Customization

;;; Constants
(defconst fem-log-buffer "*fstar-extended-debug*")

(defconst fem-message-prefix "[F*] ")
(defconst fem-tactic-message-prefix "[F*] TAC>> ")

(defconst fem-messages-buffer "*Messages*")

;; Small trick to solve the undo problems: we use temporary buffer names which
;; start with a ' ' so that emacs deactivates undo by default in those buffers,
;; preventing the insertion of problematic undo-boundary.
;; Note that for now we switch buffers "by hand" rather than using the emacs
;; macros like with-current-buffer because it leaves a trace which helps debugging.
(defconst fem-process-buffer1 " *fstar-temp-buffer1*")
(defconst fem-process-buffer2 " *fstar-temp-buffer2*")

(defconst fem-pos-marker "(*[_#%s#_]*) ")
(defvar fem-pos-marker-overlay nil)
(defvar fem-saved-pos nil)
;;  (make-fem-pair :fst nil :snd nil))

;;; Type definitions

(cl-defstruct fem-pair
  fst snd)

(cl-defstruct fem-letb-term
  "A parsed let binded term of the form: 'let b = exp in'"
  beg end ;; delimiters for the whole expression
  bind ;; the binding
  b-beg b-end ;; delimiters
  exp ;; the expression
  e-beg e-end ;; delimiters
  is-var ;; nil if tuple
  )

(cl-defstruct fem-subexpr
  "A parsed expression of the form 'let _ = _ in', '_;' or '_' (return value)"
  beg end ;; point delimiters
  is-let-in ;; is of the form: 'let _ = _ in'
  has-semicol ;; is of the form: '_;'
  bterm ;; the term binded by the 'let' if of the form 'let _ = _ in'
  )

(cl-defstruct fem-assertions
  "Counterpart of the F* assertions record type."
  pres posts)

;;; Debugging and errors

(define-error 'fstar-meta-parsing "Error while parsing F*")

(defvar fem-debug
  "Toggle debug mode"
  t)

(defun fem-log-msg (format-string &rest format-params)
  "Log a message in the log buffer.
Format FORMAT-PARAMS according to FORMAT-STRING."
  (apply #'message format-string format-params))

(defun fem-log-dbg (format-string &rest format-params)
  "Log a message in the log buffer if fem-debug is t.
Format FORMAT-PARAMS according to FORMAT-STRING."
  (when fem-debug (apply #'message format-string format-params)))

;;; Utilities

(defun fem-replace-in-string (FROM TO STR)
  "Replace FROM with TO in string STR."
  (replace-regexp-in-string (regexp-quote FROM) TO STR nil 'literal))

(defun fem-back-to-indentation-or-beginning ()
  "Switch between beginning of line or end of indentation."
  (interactive)
   (if (= (point) (progn (back-to-indentation) (point)))
       (beginning-of-line)))

(defun fem-current-line-is-whitespaces-p ()
  "Check if the current line is only made of spaces."
  (save-excursion
    (beginning-of-line)
    (looking-at-p "[[:space:]]*$")))

(defun fem-count-lines-in-string (STR)
  "Count the number of lines in a string"
  (save-match-data
    (let (($num-lines 1) (pos 0))
      (while (string-match (regexp-quote "\n") STR pos)
        (setq pos (match-end 0))
        (setq $num-lines (+ $num-lines 1)))
      $num-lines)))

(defun fem-consume-string-forward (STR &optional NO_ERROR)
  "If the pointer looks at string STR, moves the pointer after it. Otherwise,
returns nil or raises an error depending on NO_ERROR."
  (if (looking-at-p (regexp-quote STR))
      (progn (forward-char (length STR)) t)
    (if NO_ERROR nil (error (format "fem-consume-string-forward %s failed" STR)))))      

(defun fem-insert-newline-term (TERM)
  "Insert a new line if the current one is not empty, then insert TERM."
  (interactive)
  (progn
   (if (fem-current-line-is-whitespaces-p) () (progn (end-of-line) (newline)))
   (indent-according-to-mode)
   (insert TERM)))

(defun fem-newline-keep-indent ()
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

(defun fem-empty-line ()
  "Delete all the characters on the current line.
Return the number of deleted characters."
  (interactive)
  (let ($p)
   (setq $p (- (line-end-position) (line-beginning-position)))
   (delete-region (line-beginning-position) (line-end-position))
   $p))

(defun fem-empty-delete-line ()
  "Remove all the characters on the line if not empty, delete the line otherwise."
  (interactive)
  (if (equal (line-beginning-position) (line-end-position))
      (progn (delete-backward-char 1) 1) (fem-empty-line)))

(defun fem-delete-always-line ()
  "Remove all the characters on the line if not empty, delete the line otherwise."
  (interactive)
  (let ($c)
    (if (equal (line-beginning-position) (line-end-position))
	(progn (delete-backward-char 1) 1)
	(progn (setq $c (fem-empty-line))
	       (delete-backward-char 1) (+ $c 1)))))

(defun fem-find-region-delimiters (ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                   ABOVE_PARAGRAPH BELOW_PARAGRAPH &optional POS)
  ""
  (save-excursion
    (let ($p $p1 $p2)
      ;; Save the current point
      (when POS (goto-char POS))
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
      (make-fem-pair :fst $p1 :snd $p2))))

(defun fem-apply-in-current-region (ACTION ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  "Applies the action given as argument to the current line and/or the current
   paragraph above the pointer.
   It is the responsability of the ACTION function to move the pointer back to its
   (equivalent) original position."
  (let ($delimiters $p1 $p2 $r)
    ;; Find the region delimiters
    (setq $delimiters (fem-find-region-delimiters ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                              ABOVE_PARAGRAPH BELOW_PARAGRAPH))
    (setq $p1 (fem-pair-fst $delimiters) $p2 (fem-pair-snd $delimiters))
    ;; Apply the action in the delimited region
    (save-restriction
      (narrow-to-region $p1 $p2)
      (setq $r (funcall ACTION)))
    ;; return the result of performing the action
    $r))

(defun fem-apply-in-current-line (ACTION)
  "Applies the action given as argument to the current line.
   It is the responsability of the ACTION function to move the pointer back to its
   (equivalent) original position."
  (fem-apply-in-current-region ACTION nil t nil nil))

(defun fem-replace-all-in (FROM TO &optional BEG END)
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

(defun fem-replace-in-current-region (FROM TO ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                  ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  ""
  (let (($r (apply-partially 'fem-replace-all-in FROM TO)))
    ;; Apply the replace function
    (fem-apply-in-current-region $r ALLOW_SELECTION INCLUDE_CURRENT_LINE
                             ABOVE_PARAGRAPH BELOW_PARAGRAPH)))

;;; General F* code management commands

(defun fem-switch-assert-assume-in-current-region (ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                               ABOVE_PARAGRAPH BELOW_PARAGRAPH)
  (interactive)
  "Check if there are occurrences of 'assert' or 'assert_norm in the current region.
   If so, replace them with 'assume'. Ohterwise, replace all the 'assume' with 'assert'."
  (let ($p $p1 $p2 $has-asserts $replace)
    ;; Find the region delimiters and restrain the region
    (setq $delimiters (fem-find-region-delimiters ALLOW_SELECTION INCLUDE_CURRENT_LINE
                                              ABOVE_PARAGRAPH BELOW_PARAGRAPH))
    (setq $p1 (fem-pair-fst $delimiters) $p2 (fem-pair-snd $delimiters))
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
             (fem-replace-all-in "assert_norm" "assume(*norm*)")
             (fem-replace-all-in "assert" "assume"))
           (progn
             (fem-replace-all-in "assume(*norm*)" "assert_norm")
             (fem-replace-all-in "assume" "assert"))))))

(defun fem-switch-assert-assume-in-above-paragraph ()
  (interactive)
  "In the part of the current paragraph above the cursor and in the current line,
   check if there are occurrences of 'assert' or 'assert_norm'. If so, replace them
   with 'assume'. Otherwise, replace all the 'assume' with 'assert'."
  (fem-switch-assert-assume-in-current-region t t t nil))

(defun fem-switch-assert-assume-in-current-line ()
  (interactive)
  "In the current line, check if there are occurrences of 'assert' or 'assert_norm'.
   If so, replace them with 'assume'. Otherwise, replace all the 'assume' with 'assert'."
  (fem-switch-assert-assume-in-current-region nil t nil nil))

(defun fem-roll-delete-term (TERM FORWARD BEGIN END)
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
	  (when (fem-current-line-is-whitespaces-p) (setq $s (fem-delete-always-line)))
	  ;; Compute the position shift
	  (when (not FORWARD) (setq $s (+ (length TERM) $s)))
	  )))
    ;; Go to the original position
    (goto-char (- $p $s))
    ;; Return the shift if we deleted a TERM
    (if $r (setq $opt_shift $s) (setq $opt_shift nil))
    ;; Return
    (list (cons 'found $f) (cons 'opt_shift $opt_shift) (cons 'semicol $semicol))))

(defun fem-roll-admit ()
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
    (setq $s (fem-roll-delete-term "admit()" t $p1 $p2))
    ;; Delete backward
    (when (not (cdr (assoc 'opt_shift $s)))
          (setq $s (fem-roll-delete-term "admit()" nil $p1 $p2)))
    ;; Insert the admit
    (if (cdr (assoc 'semicol $s))
        (fem-insert-newline-term "admit();")
        (fem-insert-newline-term "admit()"))))

;;; Parsing commands

(defun fem-in-general-comment-p (&optional POS)
  (save-restriction
    (or (fstar-in-comment-p POS) (fstar-in-literate-comment-p))))

(defun fem-search-forward-not-comment (STR &optional LIMIT)
    "Looks for the first occurrence of STR not inside a comment, returns t and
moves the pointer immediately after if it finds one, doesn't move the pointer
and returns nil otherwise."
    (let (($p (point)))
      (fstar--search-predicated-forward
       (lambda () (not (fem-in-general-comment-p))) STR LIMIT)
      (not (= $p (point)))))

;; TODO: add to fstar-mode.el
(defun fem-fstar--search-predicated-backward (test-fn needle &optional bound)
  "Search backward for matches of NEEDLE before BOUND satisfying TEST-FN."
  (when (fstar--search-predicated #'search-backward test-fn
                             #'fstar--adjust-point-backward needle bound)
    (goto-char (match-beginning 0))))

(defun fem-search-backward-not-comment (STR &optional LIMIT)
    "Looks for the first occurrence of STR not inside a comment, returns t and
moves the pointer immediately before if it finds one, doesn't move the pointer
and returns nil otherwise."
    (let (($p (point)))
      (fem-fstar--search-predicated-backward
       (lambda () (not (fem-in-general-comment-p))) STR LIMIT)
      (not (= $p (point)))))

;; TODO: use forward-comment
(defun fem-skip-comment (FORWARD &optional LIMIT)
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

(defun fem-is-at-comment-limit (FORWARD &optional LIMIT)
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

(defun fem-skip-chars (FORWARD CHARS &optional LIMIT)
  "Move until the current character is not in CHARS.
FORWARD controls the direction, LIMIT controls where to stop."
  (if FORWARD
      (skip-chars-forward CHARS LIMIT)
      (skip-chars-backward CHARS LIMIT)))

(defun fem-skip-comments-and-spaces (FORWARD &optional LIMIT)
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
        (fem-skip-comment FORWARD LIMIT)
        (fem-skip-chars FORWARD fstar--spaces)
        (setq $reached-limit (= (point) $limit))
        (if $reached-limit (setq $continue nil)
          (if (fem-is-at-comment-limit FORWARD)
            (if FORWARD (forward-char 2) (backward-char 1))
            (setq $continue nil)))))
    (point)))

(defun fem-skip-forward-pragma (&optional LIMIT)
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
        (fem-skip-comments-and-spaces t)
        (forward-sexp)))))

(defun fem-skip-forward-square-brackets (&optional LIMIT)
  "If look at '[', go after the closing ']'.
LIMIT delimits the end of the search."
  (save-restriction
    (narrow-to-region (point) (if LIMIT LIMIT (point-max)))
    (when (looking-at-p (regexp-quote "["))
      (forward-sexp)))
  (point))

(defun fem-skip-forward-comments-pragmas-spaces (&optional LIMIT)
  "Go forward until there are no comments and pragma instructions.
Stop at LIMIT."
  (save-restriction
    (narrow-to-region (point) (or LIMIT (point-max)))
    (let (($continue t)
          ($p (point)))
      (while $continue
        (fem-skip-comments-and-spaces t)
        (fem-skip-forward-pragma)
        (when (or (= (point) $p) (= (point) (point-max)))
          (setq $continue nil))
        (setq $p (point))))))

(defun fem-region-is-comments-and-spaces (BEG END &optional NO_NEWLINE)
  "Check if a region is only made of spaces and comments.
The region is delimited by BEG and END.
NO_NEWLINE controls whether newline characters are considered spaces or not."
  (let (($p (point)) ($continue t))
    (goto-char BEG)
    (fem-skip-comments-and-spaces t END)
    (if (< (point) END) nil
      ;; If we reached the end: eventually check if there are new line characters
      (goto-char BEG)
      (if NO_NEWLINE (not (search-forward "\n" END t)) t))))

(defun fem-region-is-tuple (BEG END)
  "Return t if the text region delimited by BEG and END is a tuple.
In practice, simply check if there is a ',' inside."
  (save-excursion
    (save-restriction
      (goto-char BEG)
      (fem-search-forward-not-comment "," END))))

(defun fem-space-after-p (&optional POS)
  "Return t if there is a space at POS.
POS defaults to the pointer's position."
  (seq-contains fstar--spaces (char-after POS)))

(defun fem-space-before-p (&optional POS)
  "Return t if there is a space before POS.
POS defaults to the pointer's position."
  (seq-contains fstar--spaces (char-before POS)))

(defun fem-is-in-spaces-p (&optional POS)
  "Return t if there are spaces before and after POS.
POS defaults to the pointer's position."
  (and (fem-space-after-p POS) (fem-space-before-p POS)))

(defun fem-safe-backward-sexp (&optional ARG)
  "Call (backward-sexp ARG) and return nil instead of raising errors."
  (ignore-errors (backward-sexp ARG)))

(defun fem-safe-forward-sexp (&optional ARG)
  "Call (forward-sexp ARG) and return nil instead of raising errors."
  (ignore-errors (forward-sexp ARG)))

(defun fem-sexp-at-p (&optional POS ACCEPT_COMMENTS)
  "Find the sexp at POS.
POS defaults to the pointer's position.
Returns a fem-pair of positions if succeeds, nil otherwise.
If ACCEPT_COMMENTS is nil, return nil if we are inside a comment."
  (save-excursion
    (let (($p0 (or POS (point))) ($not-ok nil) $beg $end)
      ;; Must not be in a comment (unless the user wants it) or surrounded by spaces
      (setq $not-ok (or (and (fem-in-general-comment-p) (not ACCEPT_COMMENTS))
                        (fem-is-in-spaces-p)))
      ;; Find the beginning and end positions
      (if $not-ok nil
        ;; End: if looking at space, this is the end position. Otherwise,
        ;; go to the end of the sexp
        (when (not (fem-space-after-p)) (fem-safe-forward-sexp))
        (setq $end (point))
        ;; Beginning: just go backward
        (fem-safe-backward-sexp)
        (setq $beg (point))
        ;; Sanity check
        (if (and (<= $beg $p0) (>= $end $p0))
            (make-fem-pair :fst $beg :snd $end)
          nil)))))

(defun fem-sexp-at-p-as-string (&optional POS)
  "Return the sexp at POS."
  (let (($r (fem-sexp-at-p)))
    (if $r (buffer-substring-no-properties (fem-pair-fst $r) (fem-pair-snd $r))
      nil)))

(defun fem-parse-letb-term (BEG END &optional NO_ERROR)
  "Parse the let binded term in a 'let x = y in' expression.
Note that the region delimited by BEG and END should start exactly with 'let'
and end with 'in', put aside potential whitespaces and comments.
Returns nil if fails and NO_ERROR is t, raises an error otherwise."
  ;; We do things simple: we just look forward for the next '=' (this character
  ;; shouldn't appear in the 'x' term).
  ;; Then, in order to check whether the term is a variable or not, we just
  ;; look for the presence of ',' in it (in which case it is a tuple).
  (save-excursion
    (let ($beg $end $eq-end $b $b-beg $b-end $exp $e-beg $e-end $is-var $success $error-msg)
      (setq $success nil)
      ;; Restraigning
      (goto-char BEG)
      (fem-skip-comments-and-spaces t END)
      (setq $beg (point))
      (goto-char END)
      (fem-skip-comments-and-spaces nil $beg)
      (setq $end (point))
      (save-restriction
        (narrow-to-region $beg $end)
        (goto-char (point-min))
        ;; Ignore the 'let'
        (if (not (fem-consume-string-forward "let" NO_ERROR))
            (when (not NO_ERROR) (setq $error-msg "could not find the 'let'"))
          ;; Success
          (fem-skip-comments-and-spaces t (point-max))
          ;; Beginning of b
          (setq $b-beg (point))
          ;; Look for '='
          (if (not (fem-search-forward-not-comment "="))
              (when (not NO_ERROR) (setq $error-msg "could not find the '='"))
            (setq $eq-end (point))
            ;; End of b
            (backward-char)
            (fem-skip-comments-and-spaces nil $b-beg)
            (setq $b-end (point))
            ;; Beginning of exp
            (goto-char $eq-end)
            (fem-skip-comments-and-spaces t (point-max))
            (setq $e-beg (point))
            ;; End of exp
            (goto-char (point-max))
            (backward-char (length "in")) ;; TODO: no check
            (fem-skip-comments-and-spaces nil $e-beg)
            (setq $e-end (point))
            (setq $success t)
            ;; Check if b is a tuple
            (setq $is-var (not (fem-region-is-tuple $b-beg $b-end)))
            )))
      ;; Process errors and return
      (if (not $success)
          ;; Failure
          (if NO_ERROR nil
            (error (format "fem-parse-letb-term on '%s' failed: %s"
                           (buffer-substring-no-properties BEG END)
                           $error-msg)))
        ;; Success
        (let* ((bind (buffer-substring-no-properties $b-beg $b-end))
               (exp (buffer-substring-no-properties $e-beg $e-end)))
          (make-fem-letb-term :beg $beg :end $end
                          :bind bind
                          :b-beg $b-beg :b-end $b-end
                          :exp exp
                          :e-beg $e-beg :e-end $e-end
                          :is-var $is-var))
        ))))

(defun fem-shift-letb-term-pos (SHIFT TERM)
  "Shift hy SHIFT the positions in the fem-letb-term TERM.
Return the updated fem-letb-term"
  (setf (fem-letb-term-beg TERM) (+ SHIFT (fem-letb-term-beg TERM)))
  (setf (fem-letb-term-end TERM) (+ SHIFT (fem-letb-term-end TERM)))
  (setf (fem-letb-term-e-beg TERM) (+ SHIFT (fem-letb-term-e-beg TERM)))
  (setf (fem-letb-term-e-end TERM) (+ SHIFT (fem-letb-term-e-end TERM)))
  TERM)

(defun fem-parse-subexpr (BEG END)
  "Parse a sub-expression of the form 'let _ = _ in', '_;' or '_'.
Parses in the region delimited by BEG and END.
Returns a fem-subexpr."
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
    (fem-skip-comments-and-spaces t)
    (setq $beg (point))
    ;; - end
    (goto-char END)
    (fem-skip-comments-and-spaces nil $beg)
    (setq $end (point))
    ;; We do the regexp matching in a narrowed region
    (save-restriction
      (narrow-to-region $beg $end)
      ;; Check if the narrowed region matches: 'let _ = _ in'
      (goto-char (point-min))      
      (setq $is-let-in
            (re-search-forward "\\`let[[:ascii:][:nonascii:]]+in\\'" (point-max) t 1))
      (when $is-let-in (setq $bterm (fem-parse-letb-term $beg $end)))
      ;; Check if the narrowed region matches: '_ ;'
      (goto-char (point-min))
      (setq $has-semicol
            ;; We could just check if the character before last is ';'
            (re-search-forward "\\`[[:ascii:][:nonascii:]]+;\\'" (point-max) t 1))
      ;; Otherwise: it is a return value (end of function)
      ) ;; end of regexp matching
    ;; Return
    (make-fem-subexpr :beg $beg :end $end :is-let-in $is-let-in :has-semicol $has-semicol
                  :bterm $bterm)))

(defun fem-shift-subexpr-pos (SHIFT SUBEXPR)
  "Shift by SHIFT the positions in the fem-subexpr SUBEXPR.
Return the updated fem-subexpr."
  (setf (fem-subexpr-beg SUBEXPR) (+ SHIFT (fem-subexpr-beg SUBEXPR)))
  (setf (fem-subexpr-end SUBEXPR) (+ SHIFT (fem-subexpr-end SUBEXPR)))
  (when (fem-subexpr-bterm SUBEXPR) (fem-shift-letb-term-pos SHIFT (fem-subexpr-bterm SUBEXPR)))
  SUBEXPR)


(defun fem-find-encompassing-assert-assume-p (&optional POS BEG END)
  "Find the encompassing F* assert(_norm)/assume.
Takes an optional pointer position POS and region delimiters BEG and END.
Returns a fem-pair of fem-pair of positions if found (for the assert identifier and
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
                (setq $ar (fem-sexp-at-p))
                (setq $abeg (fem-pair-fst $ar) $aend (fem-pair-snd $ar))
                (setq $str (buffer-substring-no-properties $abeg $aend))
                (if (not (or (string-equal $str "assert")
                             (string-equal $str "assert_norm")
                             (string-equal $str "assume")))
                    ;; Not ok
                    nil
                  ;; Ok: check if the pointer is inside the argument
                  (goto-char $aend)
                  (fem-skip-comments-and-spaces t)
                  (setq $pbeg (point))
                  (fem-safe-forward-sexp)
                  (setq $pend (point))
                  (and (<= $pbeg $pos) (>= $pend $pos)))))))
        ;; Search and return
        (when (fstar--re-search-predicated-backward '$pred "assert\\|assume" $rbeg)
          ;; Return
          (make-fem-pair :fst (make-fem-pair :fst $abeg :snd $aend)
                     :snd (make-fem-pair :fst $pbeg :snd $pend))
          )))))

(defun fem-find-assert-assume-p (&optional POS BEG END)
  "Find the F* assert(_norm)/assume at the pointer position.
Takes an optional pointer position POS and region delimiters BEG and END.
Returns a fem-pair of fem-pair of positions if found (for the assert identifier and
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
        (setq $sexp (fem-sexp-at-p))
        (if $sexp
            (setq $str (buffer-substring-no-properties (fem-pair-fst $sexp)
                                                       (fem-pair-snd $sexp)))
          (setq $str ""))
        (if (or (string-equal $str "assert")
                (string-equal $str "assert_norm")
                (string-equal $str "assume"))
            ;; Ignore comments and parse the next sexp
            (progn
              (goto-char (fem-pair-snd $sexp))
              (fem-skip-comments-and-spaces t)
              (setq $pbeg (point))
              (fem-safe-forward-sexp)
              (setq $pend (point))
              (make-fem-pair :fst $sexp :snd (make-fem-pair :fst $pbeg :snd $pend)))
          ;; Otherwise, call find-encompassing-assert-assume-p
          (goto-char $pos)
          (fem-find-encompassing-assert-assume-p POS BEG END))))))

(defun fem-find-encompassing-let-in (TERM_BEG TERM_END &optional BEG END)
  "Look for the 'let _ = _ in' or '_;' expression around the term.
The term is indicated by TERM_BEG and TERM_END.
Region is delimited by BEG and END.
Returns an optional fem-subexpr."
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
        (fem-skip-comments-and-spaces t)
        (setq $has-semicol (looking-at-p (regexp-quote ";")))
        (if $has-semicol
            ;; If found a semicol
            (progn
              (setq $end (+ (point) 1))
              (make-fem-subexpr :beg TERM_BEG :end $end :is-let-in nil :has-semicol t :bterm nil))
          ;; Otherwise: look for a 'let _ = _ in' construct
          ;; First look for the '=' (note that it doesn't work with sexpressions)
          (goto-char TERM_BEG)
          (fem-skip-comments-and-spaces nil)
          (backward-char)
          ;; We should look at an '=' and not be preceded by a '=' (not sure it
          ;; is necessary to check the character before)
          (if (not (and (char-equal (char-after) ?=)
                        (not (char-equal (char-before) ?=))))
              ;; Failed
              (make-fem-subexpr :beg TERM_BEG :end TERM_END :is-let-in nil :has-semicol nil :bterm nil)
            ;; Save position
            (fem-skip-comments-and-spaces nil)
            (setq $b-end (point))
            ;; Look for the closest previous let which is not in a comment
            (if (not (fem-search-backward-not-comment "let"))
                ;; Failed
                (make-fem-subexpr :beg TERM_BEG :end TERM_END :is-let-in nil :has-semicol nil :bterm nil)
              ;; Return
              (setq $beg (point))
              (forward-sexp)
              (fem-skip-comments-and-spaces t)
              (setq $b-beg (point)) ;; $b-end set previously
              ;; Look for the 'in'
              (goto-char TERM_END)
              (fem-skip-comments-and-spaces t)
              (setq $tmp (fem-sexp-at-p))
              (if (not (string-equal "in" (fem-sexp-at-p-as-string)))
                  ;; Failed
                  (make-fem-subexpr :beg TERM_BEG :end TERM_END :is-let-in nil :has-semicol nil :bterm nil)
                (forward-sexp)
                (setq $end (point))                
                (setq $bterm (make-fem-letb-term :beg $beg :end $end :bind
                                             (buffer-substring-no-properties $b-beg $b-end)
                                             :b-beg $b-beg :b-end $b-end
                                             :exp
                                             (buffer-substring-no-properties TERM_BEG TERM_END)
                                             :e-beg TERM_BEG :e-end TERM_END))
                (make-fem-subexpr :beg $beg :end $end :is-let-in t :has-semicol nil :bterm $bterm))
                )))))))                                    

;;; Extraction of information for the *Messages* buffer

(defun fem-search-data-delimiter (delimiter backward consume-delimiter no-error
                              &optional BEG END)
  "Search for DELIMITER in the buffer.
BEG and END are optional region delimiters.
BACKWARD gives the search direction, CONSUME-DELIMITER controls whether to leave
the pointer where it is or backtrack to put it just before (after) the delimiter
 (depending on the search direction).
If the delimiter could not be found, raises an error if NO-ERROR is nil, returns
nil otherwise."
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

(defun fem-extract-info-from-buffer (prefix id &optional no-error post-process LIMIT)
  "Extracts meta data from the current buffer and optionally post-processes it.
Returns a string (or nil if we we couldn't find the information)
Leaves the pointer at the end of the parsed data (just before the next data)."
  ;; Find where the data is
  (let* ((beg (point))
         (end (or LIMIT (point-max)))
         (full-id (concat prefix id ":\n"))
         (full-id-length (length full-id))
         p p1 p2 (res nil) (pp-res nil))
    ;; Find the delimiters
    (setq p (fem-search-data-delimiter full-id nil t no-error beg end))
    ;; If we found the full-id, extract the data
    (when p
      ;; Retrieve the boundaries of the information sub-buffer
      ;; - beginning:
      (setq p1 (point))
      ;; - end: we look for the next occurence of 'prefix' followed by a '\n'
      (backward-char 1)
      (setq p2 (fem-search-data-delimiter (concat "\n" prefix ":") nil nil no-error (point) end))
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
    (when fem-debug
      (let ((res-str (if res (concat "[" res "]") "nil")))
        (fem-log-dbg "extract-info-from-messages:\n- prefix: %s\n- id: %s\n- res: %s "
                 prefix id res-str)))
    res)) ;; end of function

(defun fem-meta-info-post-process ()
  "Post-process parsed data.
Replaces some identifiers (Prims.l_True -> True...)."
  ;; Greedy replacements
  (fem-replace-all-in "Prims.l_True" "True")
  (fem-replace-all-in "Prims.l_False" "False")
  nil)

(defun fem-extract-string-from-buffer (prefix id &optional no-error LIMIT)
  "Extract a string for the current buffer."
  (fem-log-dbg "extract-string-from-buffer:\n- prefix: %s\n- id: %s" prefix id)
  (fem-extract-info-from-buffer prefix id no-error nil LIMIT))

(defun fem-extract-term-from-buffer (prefix id &optional no-error LIMIT)
  "Extract a term from the current buffer.
Contrary to a string, a term is post-processed."
  (fem-log-dbg "extract-term-from-buffer:\n- prefix: %s\n- id: %s" prefix id)
  (fem-extract-info-from-buffer prefix id no-error
                            (apply-partially 'fem-meta-info-post-process)
                            LIMIT))

(defun fem-extract-assertion-from-buffer (prefix id index &optional no-error LIMIT)
  "Extract an assertion from the current buffer.
Returns a fem-meta-info structure."
  (fem-log-dbg "extract-assertion-from-buffer:\n- prefix: %s\n- id: %s\n- index: %s"
           prefix id (number-to-string index))
  (let* ((full-id (concat id (number-to-string index))))
    (fem-extract-term-from-buffer prefix full-id no-error LIMIT)))

(defun fem-extract-assertion-list-from-buffer (prefix id index num
                                           &optional no-error LIMIT)
  "Extract a given number of assertions as a list of strings."
  (fem-log-dbg "extract-assertion-list-from-buffer:\n\
- prefix: %s\n- id: %s\n- index: %s\n- num: "
           prefix id (number-to-string index) (number-to-string num))
  (if (>= index num) nil
    (let ((param nil) (params nil))
      ;; Extract (forward) the assertion given by 'index'
      (setq param
            (fem-extract-assertion-from-buffer prefix id index no-error LIMIT))
      ;; Recursive call
      (setq params
            (fem-extract-assertion-list-from-buffer prefix id (+ index 1) num
                                                no-error LIMIT))
      (cons param params))))

(defun fem-extract-assertion-num-and-list-from-buffer (prefix id
                                                   &optional no-error LIMIT)
  "Reads how many assertions to extract from the current buffer, then
extracts those assertions."
  (fem-log-dbg "extract-assertion-num-and-list-from-buffer:\n\
- prefix: %s\n- id: %s" prefix id)
  ;; Extract the number of assertions
  (let ((id-num (concat id ":num"))
        (id-prop (concat id ":prop"))
        num num-data)
    (setq num-data (fem-extract-string-from-buffer prefix id-num no-error LIMIT))
    (setq num (string-to-number num-data))
    (fem-log-dbg "> extracting %s terms" num)
    ;; Extract the proper number of parameters
    (fem-extract-assertion-list-from-buffer prefix id-prop 0 num no-error
                                        LIMIT)))

(defun fem-extract-assertions-from-buffer (prefix id
                                                   &optional no-error LIMIT)
  "Extracts an assertion structure from the current buffer"
  (fem-log-dbg "extract-assertions-from-buffer:\n\
- prefix: %s\n- id: %s" prefix id)
  ;; Extract the number of assertions
  (let ((id-pres (concat id ":pres"))
        (id-posts (concat id ":posts"))
        pres posts)
    (setq pres (fem-extract-assertion-num-and-list-from-buffer prefix id-pres no-error LIMIT))
    (setq posts (fem-extract-assertion-num-and-list-from-buffer prefix id-posts no-error LIMIT))
    (make-fem-assertions :pres pres :posts posts)))

(defun fem-copy-data-from-messages-to-buffer (beg-delimiter end-delimiter
                                          include-delimiters dest-buffer
                                          &optional no-error clear-dest-buffer)
    "When extracting information from the *Messages* buffer, we start by locating
it by finding its begin and end delimiters, then copy it to another buffer where
we can parse/modify it. The reasons are that it is easier to modify the data in
place (while the *Messages* buffer is read-only) and that more messages
may be sent to the *Messages* buffer (by the current process or other process)
which may mess up with the data treatment and prevents us from using commands
like narrow-to-region. Moreover, it makes debugging easier. The function returns
the fem-pair of point coordinates delimiting the copied data in the destination
buffer.
include-delimiters controls whether to copy the delimiters or not"
    ;; This command MUST NOT send any message to the *Messages* buffer
    (let ((prev-buffer (current-buffer))
          (backward t)
          (beg nil) (end nil) (p1 nil) (p2 nil))
      ;; Switch to the *Messages* buffer
      (switch-to-buffer fem-messages-buffer)
      ;; Find the delimiters
      (goto-char (point-max))
      (setq beg (fem-search-data-delimiter beg-delimiter t include-delimiters no-error))
      (setq end (fem-search-data-delimiter end-delimiter nil include-delimiters no-error))
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
        (make-fem-pair :fst p1 :snd p2))))

(defun fem-clean-data-from-messages (&optional BEG END)
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
        (fem-replace-all-in (concat "\n" fem-tactic-message-prefix) "\n")
        (fem-replace-all-in (concat "\n" fem-message-prefix) "\n")
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

(defun fem-extract-assertions-from-messages (prefix id &optional process-buffer no-error
                                         clear-process-buffer)
  "Extracts assertions from the *Messages* buffer. Returns an assertions structure.
process-buffer is the buffer to use to copy and process the raw data
(*fstar-data1* by default)."
  (setq-default process-buffer fem-process-buffer2)
  (fem-log-dbg "extract-assertions-from-messages:\n\
- prefix: %s\n- id: %s\n- process buffer: '%s'\n" prefix id process-buffer)
  (let ((prev-buffer (current-buffer))
        (region nil)
        (result nil)
        (beg-delimiter (concat "[F*] TAC>> " prefix id ":BEGIN"))
        (end-delimiter (concat "[F*] TAC>> " prefix id ":END")))
    ;; Copy the data
    (setq region (fem-copy-data-from-messages-to-buffer beg-delimiter end-delimiter
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
      (goto-char (fem-pair-fst region))
      ;; Restrain the region and process it
      (save-restriction
        (narrow-to-region (fem-pair-fst region) (fem-pair-snd region))
        ;; Clean
        (fem-clean-data-from-messages)
        ;; Extract the eterm-info
        (setq result (fem-extract-assertions-from-buffer prefix id no-error)))
      ;; Switch back to the original buffer
      (switch-to-buffer prev-buffer)
      ;; Return
      result)))

;;; Commands to compute meta-data and insert F* code

(defun fem-insert-with-indent (indent-str txt &optional indent-first-line)
  (when indent-first-line (insert indent-str))
  (insert (fem-replace-in-string "\n" (concat "\n" indent-str) txt)))

(defun fem-generate-assert-from-term (indent-str after-term data &optional comment)
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
    (when (> (fem-count-lines-in-string data) 1)
      (insert "\n")
      (insert indent-str)
      (insert "  "))
    (fem-insert-with-indent (concat indent-str "  ") data)
    (insert ");")
    ;; If we are before the studied term: insert a newline
    (when (not after-term) (insert "\n"))))

(defun fem-insert-assert-pre-post--continuation (indent-str p1 p2 PARSE_RESULT overlay
                                                 status response)
  "Process the information output by F* to add it to the user code.
If F* succeeded, extracts the information and adds it to the proof"
  (unless (eq status 'interrupted)
    ;; Delete the overlay
    (delete-overlay overlay)
    ;; Display the message and exit if error
    (if (eq status 'success)
        (progn
          (fem-log-dbg "F* succeeded")
          ;; The sent query "counts for nothing" so we need to pop it to reset
          ;; F* to its previous state
          (fstar-subp--pop))
      (progn
        (when (y-or-n-p "F* failed: do you want to see the F* query?")
          (switch-to-buffer fem-process-buffer1))
        (error "F* failed")))
    ;; If we reach this point it means there was no error: we can extract
    ;; the generated information and add it to the code
    ;;
    ;; Extract the data. Note that we add two spaces to the indentation, because
    ;; if we need to indent the data, it is because it will be in an assertion.
    (let ((assertions (fem-extract-assertions-from-messages "ainfo" ""
                                                  fem-process-buffer2 t t)))
      ;; Print the information
      ;; - before the focused term
      (goto-char p1)
      (dolist (a (fem-assertions-pres assertions))
        (fem-generate-assert-from-term indent-str nil a))
      ;; - after the focused term
      (forward-char (- p2 p1))
      (dolist (a (fem-assertions-posts assertions))
        (fem-generate-assert-from-term indent-str t a))
      )))

(defun fem-same-opt-num (P1 P2)
  "Return t if P1 and P2 are the same numbers or are both nil."
  (if (and P1 P2)
      (= P1 P2)
    (and (not P1) (not P2))))

(defun fem-get-pos-markers (&optional END)
  "Return the saved pos markers above the pointer and remove them from the code.
Returns a (potentially nil) fem-pair.
END is the limit of the region to check"
  (save-match-data
    (let ($original-pos $p0 $p1 $mp0 $mp1)
      (setq $original-pos (point))
      (setq $p0 (fstar-subp--untracked-beginning-position))
      (setq $p1 (or END (point)))
      ;; First marker
      (goto-char $p0)
      (if (not (search-forward (format fem-pos-marker 0) $p1 t))
          ;; No marker
          (progn (goto-char $original-pos) nil)
        ;; There is a marker: save the position and remove it
        (when (>= $original-pos (match-end 0))
          (setq $original-pos (- $original-pos (- (match-end 0) (match-beginning 0)))))
        (setq $mp0 (match-beginning 0))
        (replace-match "")
        ;; Look for the second one
        (goto-char $p0)
        (if (not (search-forward (format fem-pos-marker 1) $p1 t))
            (setq $mp1 nil)
          (setq $mp1 (match-beginning 0))
          (when (>= $original-pos (match-end 0))
            (setq $original-pos (- $original-pos (- (match-end 0) (match-beginning 0)))))
          (replace-match ""))
        ;;Return
        (goto-char $original-pos)
        (make-fem-pair :fst $mp0 :snd $mp1)))))

(defun fem-insert-pos-markers ()
  "Insert a marker in the code to indicate the pointer position.
This is a way of saving the pointer's position for a later function call,
while indicating where this position is to the user.
TODO: use overlays."
  (interactive)
  (let ($p $p1 $p2 $op1 $op2 $overlay)
    (setq $p (point))
    ;; Retract so that the current point is not in a processed region
    (fstar-subp-retract-until $p)
    ;; Check if there are other markers. If there are, remove them.
    ;; Otherwise, insert new ones.
    (if (fem-get-pos-markers)
        nil
      ;; Save the active region (if there is) or the pointer position
      (if (use-region-p)
          (setq $p1 (region-beginning) $p2 (region-end))
        ;; Pointer position: move the pointer if we are above a term
        (when (not (or (fem-space-before-p) (fem-space-after-p)))
          (fem-safe-backward-sexp))
        (setq $p1 (point) $p2 nil))
      ;; Insert the markers (starting with the second not to have to handle shifts)
      (when $p2 (goto-char $p2) (insert (format fem-pos-marker 1)))
      (goto-char $p1)
      (insert (format fem-pos-marker 0)))))

(defun fem-find-region-delimiters-or-markers ()
  "Find the region to process."
  (save-excursion
    (let ($p0 $markers $p1 $p2 $p $allow-selection $delimiters)
      ;; Check for saved markers
      (setq $markers (fem-get-pos-markers))
      (setq $p0 (point)) ;; save the original position
      ;; If we found two markers: they delimit the region
      ;; If we found one: use it as the current pointer position
      (if (and $markers
               (fem-pair-fst $markers)
               (fem-pair-snd $markers))
          (setq $p1 (fem-pair-fst $markers) $p2 (fem-pair-snd $markers))
        (setq $p (if $markers (fem-pair-fst $markers) (point)))
        (setq $allow-selection (not $markers))
        (setq $delimiters (fem-find-region-delimiters $allow-selection t nil nil $p)))
      (goto-char $p0)
      $delimiters)))

(defun fem-copy-def-for-meta-process (END INSERT_ADMIT SUBEXPR DEST_BUFFER PP_INSTR)
  "Copy code for meta-processing and update the parsed result positions.
Leaves the pointer at the end of the DEST_BUFFER where the code has been copied.
PP_INSTR is the post-processing instruction to insert just before the definition."
  (let ($beg $p0 $str1 $str2 $str3 $attr-beg $original-length $new-length $shift $res)
    (goto-char (fstar-subp--untracked-beginning-position))
    (setq $beg (point))
    ;; - copy to the destination buffer. We do the parsing to remove the current
    ;;   attributes inside the F* buffer, which is why we copy the content
    ;;   in several steps. TODO: I don't manage to confifure the parsing for the
    ;;   destination buffer correctly.
    (fem-skip-forward-comments-pragmas-spaces)
    (setq $str1 (buffer-substring $beg (point)))
    (fem-skip-forward-square-brackets) ;; (optionally) go over the attribute
    (setq $p0 (point))
    (fem-skip-forward-comments-pragmas-spaces)
    (setq $str2 (buffer-substring $p0 (point)))
    (setq $str3 (buffer-substring (point) END))
    (switch-to-buffer DEST_BUFFER)
    (erase-buffer)
    (insert $str1)
    (insert $str2)
    ;; Insert an option to deactivate the proof obligations
    (insert "#push-options \"--admit_smt_queries true\"\n")
    ;; Insert the post-processing instruction
    (insert "[@(FStar.Tactics.postprocess_with (")
    (insert PP_INSTR)
    (insert "))]\n")
    ;; Insert the function code
    (insert $str3)
    ;; Compute the shift: the shift is just the difference of length between the
    ;; content in the destination buffer and the original content, because all
    ;; the deletion/insertion so far should have happened before the points of interest
    (setq $original-length (- END $beg)
          $new-length (- (point-max) (point-min)))
    (setq $shift (- $new-length $original-length))
    (setq $shift (+ (- $shift $beg) 1))
    ;; Introduce the admit (note that the admit is at the very end of the query)
    (when INSERT_ADMIT
      (newline)
      (indent-according-to-mode) ;; buffer's mode is not F*, but don't care
      (insert "admit()"))
    ;; Shift and return the parsing information
    (setq $res (copy-fem-subexpr SUBEXPR))
    (when (fem-subexpr-bterm SUBEXPR)
      (setf (fem-subexpr-bterm $res) (copy-fem-letb-term (fem-subexpr-bterm SUBEXPR))))
    (fem-shift-subexpr-pos $shift $res)))

(defun fem-query-fstar-on-buffer-content (OVERLAY_END PAYLOAD CONTINUATION)
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
  (fem-log-dbg "sending query to F*:[\n%s\n]" PAYLOAD)
  (fstar-subp--query (fstar-subp--push-query $beg `full PAYLOAD)
                     (apply-partially CONTINUATION $overlay))))

(defun fem-generate-fstar-check-conditions ()
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

(defun fem-compute-local-indent-p (&optional POS)
  "Return a string corresponding to the indentation up to POS.
If the characters between the beginning of the line and the current position
are comments and spaces, the returned string is equal to those - the reason
is that it allows formatting of ghosted code (which uses (**)).
Otherwise, the string is made of a number of spaces equal to the column position"
  (save-restriction
    (when POS (goto-char POS))
    (let* (($ip2 (point))
           ($ip1 (progn (beginning-of-line) (point)))
           ($indent (- $ip2 $ip1)))
      (if (fem-region-is-comments-and-spaces $ip1 $ip2)
          (buffer-substring-no-properties $ip1 $ip2)
        (make-string $indent ? )))))

(defun fem-split-assert-assume-conjuncts ()
  "Split the conjunctions in an assertion/assumption."
  (interactive)
  (let ($markers $p0 $tbeg $passert $a-beg $a-end $p-beg $p-end
        $subexpr $subexpr1 $indent-str $beg $end $query-end $insert-admit
        $cbuffer $prefix $prefix-length $payload)
  (fem-log-dbg "split-assert-conjuncts")
  ;; Sanity check
  (fem-generate-fstar-check-conditions)
  ;; Look for position markers
  (setq $markers (fem-get-pos-markers))
  (setq $p0 (point))
  (when $markers (goto-char (fem-pair-fst $markers)))
  ;; Parse the assertion/assumption. Note that we may be at the beginning of a
  ;; line with an assertion/assumption, so we first try to move. More
  ;; specifically, it is safe to ignore comments and space if we are surrounded
  ;; by spaces or inside a comment.
  (setq $tbeg (fstar-subp--untracked-beginning-position))
  (when (or (fem-is-in-spaces-p) (fstar-in-comment-p)) (fem-skip-comments-and-spaces t))
  (setq $passert (fem-find-assert-assume-p (point) $tbeg))
  (when (not $passert) (error "Pointer not over an assert/assert_norm/assume"))
  ;; Parse the encompassing let (if there is)
  (setq $a-beg (fem-pair-fst (fem-pair-fst $passert))
        $a-end (fem-pair-snd (fem-pair-fst $passert))
        $p-beg (fem-pair-fst (fem-pair-snd $passert))
        $p-end (fem-pair-snd (fem-pair-snd $passert)))
  (setq $subexpr (fem-find-encompassing-let-in $a-beg $p-end))
  (when (not $subexpr) (error "Could not parse the enclosing expression"))
  ;; Compute the indentation
  (setq $indent-str (fem-compute-local-indent-p (fem-subexpr-beg $subexpr)))
  ;; Expand the region to ignore comments
  (goto-char (fem-subexpr-beg $subexpr))
  (fem-skip-comments-and-spaces nil (point-at-bol))
  (setq $beg (point))
  (goto-char (fem-subexpr-end $subexpr))
  (fem-skip-comments-and-spaces t (point-at-eol))
  (setq $end (point))
  ;; Remember which is the original buffer
  (setq $cbuffer (current-buffer))
  ;; Copy and start processing the content
  (setq $query-end (if $markers $p0 $end))
  (setq $insert-admit (and (not $markers)
                           (or (fem-subexpr-is-let-in $subexpr)
                               (fem-subexpr-has-semicol $subexpr))))
  (setq $subexpr1 (fem-copy-def-for-meta-process $query-end $insert-admit $subexpr
                                                 fem-process-buffer1
                                                 "FEM.Process.pp_split_assert_conjs false"))
  ;; We are now in the destination buffer
  ;; Insert the ``focus_on_term`` indicator at the proper place, together
  ;; with an admit after the focused term.
  ;; Note that we don't need to keep track of the positions modifications:
  ;; we will send the whole buffer to F*.
  ;; Prefix
  (goto-char (fem-subexpr-beg $subexpr1))
  (setq $prefix "let _ = FEM.Process.focus_on_term in ")
  (setq $prefix-length (length $prefix))
  (insert $prefix)
  ;; Suffix
  (goto-char (+ (fem-subexpr-end $subexpr1) $prefix-length))
  ;; Copy the buffer content
  (setq $payload (buffer-substring-no-properties (point-min) (point-max)))
  ;; We need to switch back to the original buffer to query the F* process
  (switch-to-buffer $cbuffer)
  ;; Query F*
  (fem-query-fstar-on-buffer-content $query-end $payload
                                     (apply-partially #'fem-insert-assert-pre-post--continuation
                                                      $indent-str $beg $end $subexpr))))

(defun fem-unfold-in-assert-assume ()
  "Unfold an identifier in an assertion/assumption."
  (interactive)
  (let ($markers $p0 $id $tbeg $passert $a-beg $a-end $p-beg $p-end
        $subexpr $subexpr1 $shift $indent-str $beg $end $cbuffer
        $query-end $insert-admit $payload $insert-shift $insert-and-shift)
  (fem-log-dbg "unfold-in-assert-assume")
  ;; Sanity check
  (fem-generate-fstar-check-conditions)
  ;; Look for position markers
  (setq $markers (fem-get-pos-markers))
  (setq $p0 (point))
  (when $markers (goto-char (fem-pair-fst $markers)))
  ;; Find the identifier
  (setq $id (fem-sexp-at-p))
  (when (not $id) (error "Pointer not over a term"))
  ;; Parse the assertion/assumption.
  (setq $tbeg (fstar-subp--untracked-beginning-position))
  (setq $passert (fem-find-assert-assume-p (point) $tbeg))
  (when (not $passert) (error "Pointer not over an assert/assert_norm/assume"))
  ;; Parse the encompassing let (if there is)
  (setq $a-beg (fem-pair-fst (fem-pair-fst $passert))
        $a-end (fem-pair-snd (fem-pair-fst $passert))
        $p-beg (fem-pair-fst (fem-pair-snd $passert))
        $p-end (fem-pair-snd (fem-pair-snd $passert)))
  (setq $subexpr (fem-find-encompassing-let-in $a-beg $p-end))
  (when (not $subexpr) (error "Could not parse the enclosing expression"))
  ;; Compute the indentation
  (setq $indent-str (fem-compute-local-indent-p (fem-subexpr-beg $subexpr)))
  ;; Expand the region to ignore comments
  (goto-char (fem-subexpr-beg $subexpr))
  (fem-skip-comments-and-spaces nil (point-at-bol))
  (setq $beg (point))
  (goto-char (fem-subexpr-end $subexpr))
  (fem-skip-comments-and-spaces t (point-at-eol))
  (setq $end (point))
  ;; Remember which is the original buffer
  (setq $cbuffer (current-buffer))
  ;; Copy and start processing the content
  (setq $query-end (if $markers $p0 $end))
  (setq $insert-admit (and (not $markers)
                           (or (fem-subexpr-is-let-in $subexpr)
                               (fem-subexpr-has-semicol $subexpr))))
  (setq $subexpr1 (fem-copy-def-for-meta-process $query-end $insert-admit
                                                 $subexpr fem-process-buffer1
                                                 "FEM.Process.pp_unfold_in_assert_or_assume false"))
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
  (setq $shift (- (fem-subexpr-beg $subexpr1) (fem-subexpr-beg $subexpr)))
  (goto-char (+ (fem-pair-snd $id) $shift))
  ($insert-and-shift "))")
  (goto-char (+ (fem-pair-fst $id) $shift))
  ($insert-and-shift "(let _ = FEM.Process.focus_on_term in (")
  ;; - for the assert/assume - note that the above insertion should have been made
  ;;   below the point where we now insert
  (goto-char (fem-subexpr-beg $subexpr1))
  ($insert-and-shift "let _ = FEM.Process.focus_on_term in\n")
  ;; Copy the buffer content
  (setq $payload (buffer-substring-no-properties (point-min) (point-max)))
  ;; We need to switch back to the original buffer to query the F* process
  (switch-to-buffer $cbuffer)
  ;; Query F*
  (fem-query-fstar-on-buffer-content $query-end $payload
                                 (apply-partially #'fem-insert-assert-pre-post--continuation
                                                  $indent-str $beg $end $subexpr))))

(defun fem-insert-assert-pre-post ()
  "Insert assertions with proof obligations and postconditions around a term.
TODO: take into account if/match branches"
  (interactive)
  (fem-log-dbg "insert-assert-pre-post")
  ;; Sanity check
  (fem-generate-fstar-check-conditions)
  (let ($next-point $beg $markers $p0 $allow-selection $delimiters $indent $indent-str
        $p1 $p2 $p3 $subexpr $cp1 $cp2
        $is-let-in $has-semicol $current-buffer $insert-admit
        $cbuffer $subexpr1 $payload)
    (setq $beg (fstar-subp--untracked-beginning-position))
    ;; Find markers
    (setq $markers (fem-get-pos-markers))
    (setq $p0 (point))
    (when $markers (goto-char (fem-pair-fst $markers)))
    ;; Find in which region the term to process is
    (setq $delimiters (fem-find-region-delimiters-or-markers))
    (setq $p1 (fem-pair-fst $delimiters) $p2 (fem-pair-snd $delimiters))
    ;; Ignore the region to ignore comments/spaces and try to reach line extrema
    ;; - beginning:
    (goto-char $p1)
    (fem-skip-comments-and-spaces nil (point-at-bol))
    (setq $p1 (point))
    ;; - end: same
    (goto-char $p2)
    (fem-skip-comments-and-spaces t (point-at-eol))
    (setq $p2 (point))
    ;; Parse the term
    (setq $subexpr (fem-parse-subexpr $p1 $p2))
    (setq $cp1 (fem-subexpr-beg $subexpr))
    ;; Debug information
    (cond ((fem-subexpr-is-let-in $subexpr) (fem-log-dbg "Parsed expression: 'let _ = _ in'"))
          ((fem-subexpr-has-semicol $subexpr) (fem-log-dbg "Parsed expression: '_;'"))
          (t (fem-log-dbg "Parsed expression: '_'")))
    ;; Compute the indentation
    (setq $indent-str (fem-compute-local-indent-p $cp1))
    ;; Compute where is the end of the region to send to F*
    (setq $p3 (if $markers $p0 $p2))
    (setq $insert-admit (and (not $markers)
                             (or (fem-subexpr-is-let-in $subexpr)
                                 (fem-subexpr-has-semicol $subexpr))))
    ;; Remember which is the original buffer
    (setq $cbuffer (current-buffer))
    ;; Copy and start processing the content
    (setq $subexpr1 (fem-copy-def-for-meta-process $p3 $insert-admit $subexpr fem-process-buffer1
                                                  "FEM.Process.pp_analyze_effectful_term false"))
    ;; We are now in the destination buffer
    ;; Modify the copied content and leave the pointer at the end of the region
    ;; to send to F*
    ;;
    ;; Insert the ``focus_on_term`` indicator at the proper place, together
    ;; with an admit after the focused term.
    ;; Note that we don't need to keep track of the positions modifications:
    ;; we will send the whole buffer to F*.
    (goto-char (fem-subexpr-beg $subexpr1))
    (insert "let _ = FEM.Process.focus_on_term in ")
    ;; Copy the buffer content
    (setq $payload (buffer-substring-no-properties (point-min) (point-max)))
    ;; We need to switch back to the original buffer to query the F* process
    (switch-to-buffer $cbuffer)
    ;; Query F*
    (fem-query-fstar-on-buffer-content $p3 $payload
                                   (apply-partially #'fem-insert-assert-pre-post--continuation
                                                    $indent-str $p1 $p2 $subexpr))))

;; Key bindings
(global-set-key (kbd "C-x C-a") 'fem-roll-admit)
(global-set-key (kbd "C-c C-s C-a") 'fem-switch-assert-assume-in-above-paragraph)
(global-set-key (kbd "C-S-a") 'fem-switch-assert-assume-in-current-line)

(global-set-key (kbd "C-c C-s C-i") 'fem-insert-pos-markers)
(global-set-key (kbd "C-c C-e") 'fem-insert-assert-pre-post)
(global-set-key (kbd "C-c C-s C-u") 'fem-split-assert-assume-conjuncts)
(global-set-key (kbd "C-c C-s C-f") 'fem-unfold-in-assert-assume)

(provide 'fstar-extended-mode)
;;; fstar-extended-mode.el ends here
