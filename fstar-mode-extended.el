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

(defun region-is-comments-and-spaces (BEG END &optional NO_NEWLINE)
  "Return t if the region delimited by BEG and END is only made of spaces, new line
characters (if NO_NEWLINE is not nil) and comments."
  (let (($p (point)) ($continue t))
    (goto-char BEG)
    (skip-comments-and-spaces t END)
    (if (< (point) END) nil
      ;; If we reached the end: eventually check if there are new line characters
      (goto-char BEG)
      (if NO_NEWLINE (not (search-forward "\n" END t)) t))))

(defconst messages-buffer "*Messages*")
(defconst fstar-edebug-buffer "*fstar-extended-debug*")
(defconst fstar-message-prefix "[F*] ")
(defconst fstar-info-prefix "eterm_info:")

(defun parse-sub-expression ($p1 $p2)
  (let ($delimiters $cp1 $cp2 $is-let-in $has-semicol)
    ;; Parse: 3 cases:
    ;; - let _ = _ in
    ;; - _;
    ;; - _
    (setq $is-let-in nil $has-semicol nil)
    ;; Note that there may be a comment/spaces at the beginning and/or at the end
    ;; of the processed region, which we need to skip:
    ;; - beginning
    (goto-char $p1)
    (skip-comments-and-spaces t)
    (setq $cp1 (point))
    ;; - end
    (goto-char $p2)
    (skip-comments-and-spaces nil $cp1)
    (setq $cp2 (point))
    ;; We do the regexp matching in a narrowed region
    (save-restriction
      (narrow-to-region $cp1 $cp2)
      ;; Check if the narrowed region matches: 'let _ = _ in'
      (goto-char (point-min))      
      (setq $is-let-in
            (re-search-forward "\\`let[[:ascii:][:nonascii:]]+in\\'" (point-max) t 1))
      (if $is-let-in (message "Is 'let _ = _ in'") (message "Not is 'let _ = _ in'"))
      ;; Check if the narrowed region matches: '_ ;'
      (goto-char (point-min))
      (setq $has-semicol
            ;; We could just check if the character before last is ';'
            (re-search-forward "\\`[[:ascii:][:nonascii:]]+;\\'" (point-max) t 1))
      (if $has-semicol (message "Is '_ ;'") (message "Not is '_ ;'"))
      ;; Otherwise: it is a return value (end of function)
      ) ;; end of regexp matching
    ;; Return
    (list $cp1 $cp2 $is-let-in $has-semicol)))

(defun extract-info-from-messages (info-prefix attribute-name &optional post-process)
  "Extracts meta data from the *Messages* buffer and optionally post-processes it.
   If there is a post-process function, returns a pair:
   [> (data, post-processing return value)
   Otherwise, simply returns the extracted data"
  (let* ((full-name (concat info-prefix attribute-name))
         (full-name-length (length full-name))
         p p1 p2 prev-buffer (res nil) (pp-res nil))
    ;; Find the information name
    (setq prev-buffer (current-buffer))
    (switch-to-buffer messages-buffer)
    (goto-char (point-max))
    (setq p (search-backward full-name (point-min) t))
    (when p
      (goto-char (+ p full-name-length))
      ;; If the next character is '\n' it means there is information
      (when (char-equal (char-after) ?\n)
        ;; Retrieve the boundaries of the information sub-buffer
        ;; - beginning:
        (forward-char) ;; go to next line
        (setq p1 (point))
        ;; - end: we look for the next occurence of 'info-prefix' and ignore the
        ;; line we reach
        (search-forward info-prefix (point-max) t)
        (beginning-of-line)
        (backward-char) ;; go to previous line
        (setq p2 (point))
        ;; Copy the information to the debug buffer for processing
        (kill-ring-save p1 p2)
        (switch-to-buffer fstar-edebug-buffer)
        (goto-char (point-max))
        (insert "\n") ;; makes things easier to read (for debugging)
        ;; Before yanking, narrow the region (so that we can do aggressive
        ;; modifications without caring too much)
        (save-restriction
          (narrow-to-region (point) (point))
          (yank)
          ;; Every line starts with '[F*] ' (remove those occurrences)
          (goto-char (point-min))
          (let ((continue (< (point) (point-max))))
            (while continue
              (delete-forward-char (length fstar-message-prefix))
              ;; Go to next line (if possible)
              (end-of-line)
              (if (< (point) (point-max)) (forward-char) (setq continue nil))))
          ;; Post-process the data
          (when post-process (setq pp-res (post-process)))
          ;; Save the content of the whole narrowed region
          (setq res (buffer-substring-no-properties (point-min) (point-max)))
          ) ;; end of save-restriction
        ) ;; end of second when
      ) ;; end of first when
    ;; Switch back to original buffer
    (switch-to-buffer prev-buffer)
    ;; Return
    (if (and res post-process) (list res pp-res) res))) ;; end of function

(defun insert-assert-pre-post-continuation (indent-str p1 p2 cp1 cp2 overlay status response)
  "The continuation function called once F* returns. If F* succeeded, extracts
   the information and adds it to the proof"
  (unless (eq status 'interrupted)
    ;; Delete the overlay
    (delete-overlay overlay)
    ;; Display the message and exit if error
    (if (eq status 'success)
        (progn
          (message "F* succeeded")
          ;; The sent query "counts for nothing" so we need to pop it
          (fstar-subp--pop))
      (progn
        (error "F* meta processing failed")))
    ;; If we reach this point it means there was no error: we can extract
    ;; the generated information and add it to the code
    ;;
    ;; Data post-processing function: counts the number of lines. If there is
    ;; more than one line, add indentation, otherwise leaves the data as it is.
    (defun post-process ()
      (goto-char (point-min))
      (let ((num-lines 0) continue)
        (setq continue (< (point) (point-max)))
        ;; Count the lines
        (while continue
          (end-of-line)
          (if (< (point) (point-max)) (forward-char) (setq continue nil))
          (setq num-lines (+ num-lines 1)))
        ;; If > 1 lines, indent them (note that we add two spaces to the indentation
        ;; string, because the data will be put inside an assert)
        (when (> num-lines 1)
          (let ((i 0) (indent-str1 (concat indent-str "  ")))
            (goto-char (point-min))
            (while (< i num-lines)
              ;; Indent
              (insert indent-str1)
              ;; Go to next line
              (setq i (+ i 1))
              (when (< i num-lines) (end-of-line) (forward-char)))))
        ;; Return the number of lines
        num-lines
        )) ;; end of post-process fun
    ;; Properly instantiated extraction functions
    (defun extract (attribute-name &optional pp)
      (extract-info-from-messages fstar-info-prefix attribute-name pp))
    (defun extract-pp (attribute-name)
      (extract attribute-name 'post-process))
    ;; Extract the data and add information to the proof
    (let* ((etype (extract "etype:"))
           (pre (extract-pp "pre:"))
           (post (extract-pp "post:"))
           (result (extract-pp "result:"))
           (ret (extract-pp "ret:"))
           (ret_refin (extract-pp "ret_refin:"))
           (goal (extract-pp "goal:"))
           (shift 0))
      ;; Print the information
      ;; - utilities
      (defun insert-update-shift (s)
        (insert s)
        (setq shift (+ shift (length s))))
      (defun generate-info (p data &optional comment)
        "Generates the appropriate assert at the proper position, preceded buy
         an optional comment, while updating the shift."
        (when data
          (goto-char (+ p shift))
          ;; If we are after the studied term: insert a newline
          (when (>= p cp2) (insert-update-shift "\n"))
          (when comment
            (insert-update-shift indent-str)
            (insert-update-shift comment)
            (insert-update-shift "\n"))
          (insert-update-shift indent-str)
          (insert-update-shift "assert(")
          (when (> (nth 1 data) 1) (insert-update-shift "\n"))
          (insert-update-shift (nth 0 data))
          (insert-update-shift ");")
          ;; If we are before the studied term: insert a newline
          (when (<= p cp1) (insert-update-shift "\n"))))
      ;; - print
      (generate-info p1 pre)
      (generate-info p2 post)
      (generate-info p2 goal)
)))

(defun insert-assert-pre-post--process
    ($indent-str $p1 $p2 $cp1 $cp2 $is-let-in $has-semicol)
  (let ($beg $cbuffer $shift $lbeg $lp1 $lp2 $lcp1 $lcp2)
    ;; Copy the relevant content of the buffer for modification
    (setq $beg (fstar-subp--untracked-beginning-position))
    ;; - copy and switch buffer
    (setq $cbuffer (current-buffer))
    (kill-ring-save $beg $p2)
    (switch-to-buffer fstar-edebug-buffer)
    ;; - change the reference position
    (goto-char (point-max))
    (insert "\n\n- Starting new processing:\n\n")
    (setq $lbeg (point-max) $shift (- (point-max) $beg))
    (setq $lp1 (+ $p1 $shift) $lp2 (+ $p2 $shift) $lcp1 (+ $cp1 $shift) $lcp2 (+ $cp2 $shift))
    ;; - yank
    (yank)
    ;; Modify the copied content and leave the pointer at the end of the region
    ;; to send to F*
    (cond
     ;; 'let _ = _ in'
     ($is-let-in (message "Not supported yet"))
     ;; '_;' or '_'
     (t
      (let ($prefix $prefix-length $suffix $suffix-length)
        ;; Wrap the term in a tactic to generate the debugging information
        (setq $prefix "run_tactic (fun _ -> dprint_eterm (quote (")
        (setq $suffix ")) (`()) [`()])")
        (setq $prefix-length (length $prefix) $suffix-length (length $suffix))
        (goto-char $lcp1)
        (insert $prefix)
        ;; We need to put the suffix before the ';', if there is
        (let (($semicol-size (if $has-semicol 1 0)))
          (goto-char (+ (- $lcp2 $semicol-size) $prefix-length)))
        (insert $suffix)
        ;; Insert an admit() at the end
        (goto-char (+ $lp2 (+ $prefix-length $suffix-length)))
        (progn (end-of-line)
               ;; Insert a ';' if there isn't
               (unless $has-semicol (insert ";"))
               (newline) (indent-according-to-mode) (insert "admit()"))
        )) ;; end of second case
     ) ;; end of cond
    ;; Query F*
    (let* ((overlay (make-overlay $beg $p2 $cbuffer nil nil))
           ($lend (point))
           ($payload (buffer-substring-no-properties $lbeg $lend)))
      ;; We need to swithch back to the original buffer to query the F* process
      (switch-to-buffer $cbuffer)
      ;; Overlay management
      (fstar-subp-remove-orphaned-issue-overlays (point-min) (point-max))
      (overlay-put overlay 'fstar-subp--lax nil)
      (fstar-subp-set-status overlay 'busy)
      ;; Query F*
      (fstar-subp--query (fstar-subp--push-query $beg `full $payload)
                         (apply-partially #'insert-assert-pre-post-continuation
                                          $indent-str $p1 $p2 $cp1 $cp2 overlay))
      )
    ) ;; end of outermost let
  ) ;; end of function

(defun insert-assert-pre-post ()
  (interactive)
  "Inserts assertions with the instanciated pre and post-conditions around a
function call.
TODO: replace assertions by assumes
TODO: take into account if/match branches
TODO: add assertions for the parameters' refinements"
  (let ($next-point $beg $p $delimiters $indent $indent-str
        $p1 $p2 $parse-result $cp1 $cp2
        $is-let-in $has-semicol $current-buffer)
    (setq $p (point))
    ;; F* mustn't be busy as we won't push a query to the queue but will directly
    ;; query the F* sub-process: if some processes are queued, we will mess up
    ;; with the internal proof state
    (when (fstar-subp--busy-p) (user-error "The F* process must be live and idle"))
    ;; Retract so that the current point is not in a processed region
    (fstar-subp-retract-until (point))
    ;; Check if the point is in the next block to process: if not, ask the user
    ;; if he really wants to execute the command because we will need to parse
    ;; all the definitions up to before the point, which may take time. Don't
    ;; ask if we can't compute the next block (in which case it is indeed very
    ;; likely that we are in the next block)
    (setq $next-point (fstar-subp--find-point-to-process 1))
    (when (and $next-point (< $next-point $p))
      (unless (y-or-n-p (concat "There may be unprocessed definitions above the "
                                "current position: are you sure you want to "
                                "continue? We will need to process them, which "
                                "may take time, and the result will be lost"))
        (user-error "Aborted")))
    ;; Restrict the region
    (setq $beg (fstar-subp--untracked-beginning-position))
    (setq $p (- $p $beg))
    (save-restriction
      (narrow-to-region $beg (point-max))
      ;; Find in which region the term to process is
      (setq $delimiters (find-region-delimiters t t nil nil))
      (setq $p1 (car $delimiters) $p2 (car (cdr $delimiters)))
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
      (setq $parse-result (parse-sub-expression $p1 $p2))
      (setq $cp1 (nth 0 $parse-result)
            $cp2 (nth 1 $parse-result)
            $is-let-in (nth 2 $parse-result)
            $has-semicol (nth 3 $parse-result))
      ;; Compute the indentation: if the area between the beginning of the focused
      ;; term and the beginning of the line is made of spaces and comments, we copy
      ;; it (allows to have a formatting consistent with ghosted code: "(**)",
      ;; for example), otherwise we introduce spaces equal to the length of that area
      (let (($ip1 (progn (beginning-of-line) (point))) ($ip2 $cp1))
        (setq $indent (- $ip2 $ip1))
        (if (region-is-comments-and-spaces $ip1 $ip2)
            (setq $indent-str (buffer-substring-no-properties $ip1 $ip2))
          (setq $indent-str (make-string $indent ? ))))
      ;; Process the term
      (insert-assert-pre-post--process $indent-str $p1 $p2 $cp1 $cp2 $is-let-in $has-semicol))))

(defun t1 ()
  (interactive)
  (insert-assert-pre-post))

(defun t2 ()
  (interactive)
  (message "Point: %s" (point)))

(defun fstar-subp-advance-or-retract-to-point (&optional arg)
  "Advance or retract proof state to reach point.

With prefix argument ARG, when advancing, do not split region
into blocks; process it as one large block instead."
  (interactive "P")
  (fstar-subp-start)
  (fstar--widened
    (cond
     ((fstar-subp--in-tracked-region-p)
      (fstar-subp-retract-until (point)))
     ((consp arg)
      (fstar-subp-enqueue-until (point)))
     (t
      (fstar-subp-advance-until (point))))))

(defun fstar-subp-advance-until (pos)
  "Submit or retract blocks to/from prover until POS (included)."
  (fstar-subp-start)
  (fstar--widened-excursion
    (let ((found nil))
      (fstar-subp--untracked-beginning)
      (while (and (not (eobp)) ;; Don't loop at eob
                  (fstar-subp--next-point-to-process)
                  (<= (point) pos))
        ;; ⚠ This fails when there's nothing left but blanks to process.
        ;; (which in fact makes the (not (eobp)) check above redundant.)
        (fstar-subp-enqueue-until (point))
        (setq found t))
      (fstar-subp-enqueue-until pos found))))

(defun fstar-subp-enqueue-until (end &optional no-error)
  "Mark region up to END busy, and enqueue the newly created overlay.
Report an error if the region is empty and NO-ERROR is nil."
  (fstar-subp-start)
  (let ((beg (fstar-subp--untracked-beginning-position))
        (end (save-excursion (goto-char end) (skip-chars-backward fstar--spaces) (point))))
    (if (<= end beg)
        (unless no-error
          (user-error "Region up to point is empty: nothing to process!"))
      (when (eq (char-after end) ?\n)
        (cl-incf end))
      (fstar-assert (cl-loop for overlay in (overlays-in beg end)
                        never (fstar-subp-tracking-overlay-p overlay)))
      (let ((overlay (make-overlay beg end (current-buffer) nil nil))
            (fstar-subp--lax (or fstar-subp--lax fstar-subp-sloppy)))
        (fstar-subp-remove-orphaned-issue-overlays (point-min) (point-max))
        (overlay-put overlay 'fstar-subp--lax fstar-subp--lax)
        (fstar-subp-set-status overlay 'pending)
        (fstar-subp--set-queue-timer)))))

(defun fstar-subp-process-overlay (overlay)
  "Send the contents of OVERLAY to the underlying F* process."
  (fstar-assert (not (fstar-subp--busy-p)))
  (fstar-subp-start)
  (fstar-subp-set-status overlay 'busy)
  (let ((lax (overlay-get overlay 'fstar-subp--lax)))
    (fstar-subp-push-region
     (overlay-start overlay) (overlay-end overlay) (if lax 'lax 'full)
     (apply-partially #'fstar-subp--overlay-continuation overlay))))

(defun fstar-subp-push-region (beg end kind continuation)
  "Push the region between BEG and END to the inferior F* process.
KIND indicates how to check BEG..END (one of `lax', `full').
Handle results with CONTINUATION."
  (let* ((payload (fstar-subp--clean-buffer-substring beg end)))
    (when (eq beg (point-min)) (fstar-subp--send-current-file-contents))
    (fstar-subp--query (fstar-subp--push-query beg kind payload) continuation)))

(defun fstar-subp--query (query continuation)
  "Send QUERY to F* subprocess; handle results with CONTINUATION."
  (let ((id nil))
    (when (fstar-subp-query-p query)
      (setq id (number-to-string (cl-incf fstar-subp--next-query-id)))
      (setq query (fstar-subp--serialize-query query id)))
    (fstar-log 'in "%s" query)
    (if continuation
        (fstar-subp-continuations--put id continuation)
      (remhash id fstar-subp--continuations))
    (fstar-subp-start)
    (process-send-string fstar-subp--process (concat query "\n"))))

(defun fstar-subp--push-query (pos kind code)
  "Prepare a push query for a region starting at POS.
KIND is one of `lax', `full'.  CODE is the code to push."
  (if (fstar--has-feature 'json-subp)
      (fstar-subp--push-peek-query-1 "push" pos kind code)
    (format "#push %d %d%s\n%s%s"
            (line-number-at-pos pos)
            (fstar-subp--column-number-at-pos pos)
            (pcase kind (`lax " #lax") (`full ""))
            code
            fstar-subp-legacy--footer)))

(defun fstar-subp--push-peek-query-1 (query pos kind code)
  "Helper for push/peek (QUERY) with POS KIND and CODE."
  (make-fstar-subp-query
   :query query
   :args `(("kind" . ,(symbol-name kind))
           ("code" . ,code)
           ("line" . ,(line-number-at-pos pos))
           ("column" . ,(fstar-subp--column-number-at-pos pos)))))

(defun fstar-subp--peek-query (pos kind code)
  "Prepare a peek query for a region starting at POS.
KIND is one of `syntax' or `light'.  CODE is the code to
push."
  (fstar-assert (fstar--has-feature 'json-subp))
  (fstar-subp--push-peek-query-1 "peek" pos kind code))


(defun fstar-subp--query (query continuation)
  "Send QUERY to F* subprocess; handle results with CONTINUATION."
  (let ((id nil))
    (when (fstar-subp-query-p query)
      (setq id (number-to-string (cl-incf fstar-subp--next-query-id)))
      (setq query (fstar-subp--serialize-query query id)))
    (fstar-log 'in "%s" query)
    (if continuation
        (fstar-subp-continuations--put id continuation)
      (remhash id fstar-subp--continuations))
    (fstar-subp-start)
    (process-send-string fstar-subp--process (concat query "\n"))))

(defun fstar-subp--overlay-continuation (overlay status response)
  "Handle the results (STATUS and RESPONSE) of processing OVERLAY."
  (unless (eq status 'interrupted)
    (fstar-subp-parse-and-highlight-issues status response overlay)
    (if (eq status 'success)
        (fstar-subp-set-status overlay 'processed)
      (fstar-subp-remove-unprocessed)
      ;; Legacy protocol requires a pop after failed pushes
      (unless (fstar--has-feature 'json-subp)
        (fstar-subp--pop))))
  (run-hook-with-args 'fstar-subp-overlay-processed-hook overlay status response))

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
