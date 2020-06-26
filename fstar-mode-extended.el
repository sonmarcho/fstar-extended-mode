;;
;; Custom commands and bindings for the F* mode
;;

;; TODO: many manipulations in the below functions can be simplified by using:
;; - save-current-buffer, with-current-buffer (to switch buffer), with-temp-buffer

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

(defun replace-in-string (FROM TO STR)
  (replace-regexp-in-string (regexp-quote FROM) TO STR nil 'literal))

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

(define-error 'fstar-meta-parsing "Error while parsing F*")

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
(defconst fstar-temp-buffer1 " *fstar-temp-buffer1*")
(defconst fstar-temp-buffer2 " *fstar-temp-buffer2*")
(defconst fstar-message-prefix "[F*] ")
(defconst fstar-tactic-message-prefix "[F*] TAC>> ")

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
      ;; Check if the narrowed region matches: '_ ;'
      (goto-char (point-min))
      (setq $has-semicol
            ;; We could just check if the character before last is ';'
            (re-search-forward "\\`[[:ascii:][:nonascii:]]+;\\'" (point-max) t 1))
      ;; Otherwise: it is a return value (end of function)
      ) ;; end of regexp matching
    ;; Return
    (list $cp1 $cp2 $is-let-in $has-semicol)))

;; Meta information generated by tactics and output in the *Messages* buffer:
(cl-defstruct meta-info
  "Meta information extracted from the *Messages* buffer. Contains text as well
as the result returned by the post-processing function called on the data."
  data pp-res)

;; Below, we mimic (approximate) the meta structures defined on the F* side
;; We merge the rtype_info and type_info structures
(cl-defstruct type-info ty rty-raw rty-refin)
;; For param_info: we remove the qualif field and add a types-comparison field
(cl-defstruct param-info term p-ty e-ty types-comparison)
(cl-defstruct eterm-info etype pre post ret-type head parameters goal)

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
        (end (or END (point-max))))
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

(defun meta-info-post-process ()
  "Data post-processing function: counts the number of lines. If there is
more than one line, adds indentation, otherwise leaves the data as it is.
Besides, greedily replaces some identifiers (Prims.l_True -> True...).
Returns the number of lines."
  (goto-char (point-min))
  (let ((num-lines 1))
    ;; Count the lines
    (while (search-forward "\n" (point-max) t)
      (setq num-lines (+ num-lines 1)))
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

(defun extract-type-info-from-buffer (prefix id &optional no-error LIMIT)
  "Extracts type information from the *Messages* buffer. Returns a ``type-info``
structure."
  (log-dbg "extract-type-info-from-buffer:\n- prefix: %s\n- id: %s" prefix id)
  (let ((id-ty (concat id ":ty"))
        (id-rty-raw (concat id ":rty_raw"))
        (id-rty-refin (concat id ":rty_refin"))
        extract)
    (defun extract (id)
            (extract-term-from-buffer prefix id no-error LIMIT))
    (let ((ty (extract id-ty))
          (rty-raw (extract id-rty-raw))
          (rty-refin (extract id-rty-refin)))
    (make-type-info :ty ty :rty-raw rty-raw :rty-refin rty-refin))))

(defun extract-param-info-from-buffer (prefix id index
                                       &optional no-error LIMIT)
  "Extracts parameter information from the *Messages* buffer. Returns a param-info
structure."
  (log-dbg "extract-param-info-from-buffer:\n- prefix: %s\n- id: %s\n- index: %s"
                       prefix id (number-to-string index))
  (let* ((pid (concat id ":param" (number-to-string index)))
         (id-term (concat pid ":term"))
         (id-p-ty (concat pid ":p_ty"))
         (id-e-ty (concat pid ":e_ty"))
         (id-types-comparison (concat pid ":types_comparison"))
         extract-string extract-term extract-type)
    (defun extract-string (id)
      (extract-string-from-buffer prefix id no-error LIMIT))
    (defun extract-term (id)
      (extract-term-from-buffer prefix id no-error LIMIT))
    (defun extract-type (id)
      (extract-type-info-from-buffer prefix id no-error LIMIT))
    (let ((term (extract-term id-term))
          (p-ty (extract-type id-p-ty))
          (e-ty (extract-type id-e-ty))
          (types-comparison (extract-string id-types-comparison)))
    (make-param-info :term term :p-ty p-ty :e-ty e-ty :types-comparison types-comparison))))

(defun extract-param-info-list-from-buffer (prefix id index num
                                                 &optional no-error LIMIT)
  "Extract a given number of parameters as a list of param-info."
  (log-dbg "extract-param-info-list-from-buffer:\n\
- prefix: %s\n- id: %s\n- index: %s\n- num: "
           prefix id (number-to-string index) (number-to-string num))
  (if (>= index num) nil
    (let ((param nil) (params nil))
      ;; Extract (forward) the parameter given by 'index'
      (setq param
            (extract-param-info-from-buffer prefix id index no-error LIMIT))
      ;; Recursive call
      (setq params
            (extract-param-info-list-from-buffer prefix id (+ index 1) num
                                                 no-error LIMIT))
      (cons param params))))

(defun extract-parameters-from-buffer (prefix id
                                       &optional no-error LIMIT)
  "Extracts parameters information from the *Messages* buffer. Returns a list of
param-info"
  (log-dbg "extract-parameters-from-buffer:\n\
- prefix: %s\n- id: %s" prefix id)
  ;; Extract the number of messages
  (let ((id-num (concat id ":num")))
    (setq num-data (extract-string-from-buffer prefix id-num no-error LIMIT))
    (setq num (string-to-number (meta-info-data num-data)))
    (log-dbg "> extracting %s parameters" num)
    ;; Extract the proper number of parameters
    (extract-param-info-list-from-buffer prefix id 0 num no-error
                                         LIMIT)))

(defun extract-eterm-info-from-buffer (prefix id &optional no-error LIMIT)
  "Extracts effectful term information from the current buffer and returns a
eterm-info structure."
  (log-dbg "extract-eterm-info-from-buffer:\n\
- prefix: %s\n- id: %s" prefix id)
  (let (extract-type extrac-term extract-parameters)
    (defun extract-type (id)
      (extract-type-info-from-buffer prefix id no-error LIMIT))
    (defun extract-term (id)
      (extract-term-from-buffer prefix id no-error LIMIT))
    (defun extract-parameters (id)
      (extract-parameters-from-buffer prefix id no-error LIMIT))
    (let ((etype (extract-term (concat id ":etype")))
          (pre (extract-term (concat id ":pre")))
          (post (extract-term (concat id ":post")))
          (ret-type (extract-type (concat id ":ret_type")))
          (parameters (extract-parameters (concat id ":parameters")))
          (goal (extract-term (concat id ":goal"))))
      ;; Return
      (make-eterm-info :etype etype :pre pre :post post :ret-type ret-type
                       :parameters parameters :goal goal))))

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
        (delete-forward-char 1)
        ;; Save the new region end
        (goto-char (point-max))
        (setq new-end (point))
        (goto-char (point-min)))
      ;; Return the new end of the region
      (+ (point) new-end)))

(defun extract-eterm-info-from-messages (prefix id &optional process-buffer no-error
                                         clear-process-buffer)
  "Extracts effectful term information from the *Messages* buffer. Returns an
eterm-info structure. process-buffer is the buffer to use to copy and process
the raw data (*fstar-data1* by default)."
  (setq-default process-buffer fstar-temp-buffer2)
  (log-dbg "extract-eterm-info-from-messages:\n\
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
        (setq result (extract-eterm-info-from-buffer prefix id no-error)))
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

(defun generate-param-asserts (indent-str param)
  "Generates the appropriate assertions for a parameter (type cast and type
refinement)"
  (let* ((term (param-info-term param))
         (p-ty (param-info-p-ty param))
         (e-ty (param-info-e-ty param)))
    (when (and term p-ty e-ty)
      ;; Insert an assertion for the type cast
      (when (param-info-requires-cast param)
        (let* ((rawest-e-ty (type-info-rawest-type e-ty))
               (several-lines
                (or (> (meta-info-pp-res term) 1)
                    (> (meta-info-pp-res rawest-e-ty) 1))))
          ;; Begin
          (insert indent-str)
          (insert "assert(has_type")
          ;; Insert the term
          (if several-lines
              ;; Several lines
              (progn
                (insert "\n")
                (insert indent-str)
                (insert "  (")
                (insert-with-indent (concat indent-str "   ") (meta-info-data term))
                (insert ")"))
            ;; One line
            (insert " (")
            (insert (meta-info-data term))
            (insert ") "))
          ;; Insert the type
          (if several-lines
              ;; Several lines
              (progn
                (insert "\n")
                (insert indent-str)
                (insert "  (")
                (insert-with-indent (concat indent-str "   ") (meta-info-data rawest-e-ty))
                (insert ")"))
            ;; One line
            (insert "(")
            (insert (meta-info-data rawest-e-ty))
            (insert ")"))
          ;; Finish
          (when several-lines (insert "\n") (insert indent-str))
          (insert ");\n")))
      ;; Insert an assertion for the refinement
      (when (param-info-requires-refinement param)
        (generate-assert-from-term indent-str nil (type-info-rty-refin e-ty))
        ))))

(defun insert-assert-pre-post--continuation (indent-str p1 p2 cp1 cp2 overlay
                                             status response)
  "The continuation function called once F* returns. If F* succeeded, extracts
   the information and adds it to the proof"
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
        (error "F* meta processing failed")))
    ;; If we reach this point it means there was no error: we can extract
    ;; the generated information and add it to the code
    ;;
    ;; Extract the data. Note that we add two spaces to the indentation, because
    ;; if we need to indent the data, it is because it will be in an assertion.
    (setq info (extract-eterm-info-from-messages "eterm_info" ""
                                                 fstar-temp-buffer2 t t))
    ;; Print the information
    ;; - utilities
    (let* ((indent2-str (concat indent-str "  "))
           (indent3-str (concat indent-str "   "))
           ;; TODO: check function names
           insert-update-shift generate-assert generate-param-assert)
      ;; - print
      ;; -- before the focused term
      (goto-char p1)
      (generate-assert-from-term indent-str nil (eterm-info-pre info))
      (dolist (param (eterm-info-parameters info))
        (generate-param-asserts indent-str param))
      ;; -- and insert after the focused term
      (forward-char (- p2 p1))
      (generate-assert-from-term indent-str t (eterm-info-post info))
      (generate-assert-from-term indent-str t (eterm-info-goal info))
      )))

(defun insert-assert-pre-post--process
    ($indent-str $p1 $p2 $cp1 $cp2 $is-let-in $has-semicol)
  (let ($beg $cbuffer $shift $lbeg $lp1 $lp2 $lcp1 $lcp2)
    ;; Copy the relevant content of the buffer for modification
    (setq $beg (fstar-subp--untracked-beginning-position))
    ;; - copy and switch buffer
    (setq $cbuffer (current-buffer))
    (kill-ring-save $beg $p2)
    (switch-to-buffer fstar-temp-buffer1)
    (erase-buffer)
    ;; - change the reference position
    (goto-char (point-max))
    (insert "\n\n- Starting new processing:\n\n")
    (save-restriction
      (narrow-to-region (point) (point))
      ;; TODO: cleanup the mess with the different position pointers
      (setq $lbeg (point-max) $shift (- (point-max) $beg))
      (setq $lp1 (+ $p1 $shift) $lp2 (+ $p2 $shift) $lcp1 (+ $cp1 $shift) $lcp2 (+ $cp2 $shift))
      ;; - yank
      (yank)
      ;; Modify the copied content and leave the pointer at the end of the region
      ;; to send to F*
      ;;
      ;; Insert the proper wrappers depending on the result of parsing to generate
      ;; the proper information by running F*. Note that we don't need to keep
      ;; track of the positions modifications: we will send the whole buffer to F*.
      (cond
       ;; 'let _ = _ in'
       ($is-let-in (error "Not supported yet: let _ = _ in"))
       ;; '_;' or '_'
       ($has-semicol
        (let ($prefix $prefix-length $suffix $suffix-length)
          ;; Wrap the term in a tactic to generate the debugging information
          (setq $prefix "run_tactic (fun _ -> dprint_eterm (quote (")
          (setq $suffix ")) None (`()) [`()])")
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
       (t (error "Not supported yet: _"))
       ) ;; end of cond
      ;; TODO: the following is not necessary anymore, but I keep it in comments
      ;; just in case
      ;; Do some greedy replacements: replace the assertions by assumptions
      ;;    (replace-all-in "assert_norm" "assume(*norm*)")
      ;;    (replace-all-in "assert" "assume")
      ;; Insert an option to deactivate the proof obligations
      (goto-char (point-min))
      (insert "#push-options \"--admit_smt_queries true\"\n")
      ;; Query F*
      (let* ((overlay (make-overlay $beg $p2 $cbuffer nil nil))
             ($payload (buffer-substring-no-properties (point-min) (point-max))))
        ;; We need to swithch back to the original buffer to query the F* process
        (switch-to-buffer $cbuffer)
        ;; Overlay management
        (fstar-subp-remove-orphaned-issue-overlays (point-min) (point-max))
        (overlay-put overlay 'fstar-subp--lax nil)
        (fstar-subp-set-status overlay 'busy)
        ;; Query F*
        (log-dbg "sending query to F*:[\n%s\n]" $payload)
        (fstar-subp--query (fstar-subp--push-query $beg `full $payload)
                           (apply-partially #'insert-assert-pre-post--continuation
                                            $indent-str $p1 $p2 $cp1 $cp2 overlay))
        )
      ) ;; end of restriction
    ) ;; end of outermost let
  ) ;; end of function

(defun insert-assert-pre-post ()
  (interactive)
  "Inserts assertions with the instanciated pre and post-conditions around a
function call.
TODO: take into account if/match branches
TODO: add assertions for the parameters' refinements"
  (log-dbg "insert-assert-pre-post")
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
      (setq $parse-result (parse-sub-expression $p1 $p2))
      (setq $cp1 (nth 0 $parse-result)
            $cp2 (nth 1 $parse-result)
            $is-let-in (nth 2 $parse-result)
            $has-semicol (nth 3 $parse-result))
      ;; Debug information
      (when $is-let-in (log-dbg "Parsed expression: 'let _ = _ in'"))
      (when $has-semicol (log-dbg "Parsed expression: '_;'"))
      (when (and (not $is-let-in) (not $has-semicol)) (log-dbg "Parsed expression: '_'"))
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
      (insert-assert-pre-post--process $indent-str $p1 $p2 $cp1 $cp2 $is-let-in
                                       $has-semicol))))

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

(global-set-key (kbd "C-c C-e") 'insert-assert-pre-post)

(defun t1 ()
  (interactive)
  (insert-assert-pre-post))


