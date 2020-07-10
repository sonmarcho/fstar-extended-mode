# F* extended mode
The F* extended mode contains files which extend the [F* emacs mode](https://github.com/FStarLang/fstar-mode.el). It provides simple code editing commands to help switching between assertions and assumptions in the code, to save time when progressing on a proof, or to help with techniques like the "rolling-admit". It also provides more advanced commands which reveal or help to work with proof obligations or context information at specific points in the code by inserting appropriate assertions.

# Setup
You first need to install the [F* emacs mode](https://github.com/FStarLang/fstar-mode.el). The F* extended mode is not on Melpa for now, so you need to clone the repository. Next, you need to configure the emacs mode so that it knows where to look for the .fst files used by the extended mode. The simplest way is to insert the following code in your `.emacs` file. This command tries to use any local Makefile to compute the F* dependencies whenever you start the F* mode.

```
(defun my-fstar-compute-prover-args-using-make ()
  "Construct arguments to pass to F* by calling make."
  (interactive)
  (with-demoted-errors "Error when constructing arg string: %S"
    (let* ((fname (file-name-nondirectory buffer-file-name))
           (target (concat fname "-in"))
           (argstr (condition-case nil
                       ;; Compute the dependencies by using the local Makefile
                       (concat
                        (car (process-lines "make" "--quiet" target))
                        ;; Put the path to the local copy of the F* extended mode here
                        " --include " (getenv "HOME") "/fstar-extended-mode "
                        )
                     ;; If the above failed, use a default configuration
                     (error (concat
                     	     ;; Put the relevant F* directories here
                             "--include " (getenv "HOME") "/hacl-star/lib "
                             ;; Put the path to the local copy of the F* extended mode here
                             "--include " (getenv "HOME") "/fstar-extended-mode "
                             ;; Optional
                             "--debug yes --log_queries --use_hints --cache_checked_modules"
                             )))))
      (split-string argstr))))
(setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
(setq fstar-subp-debug t)
```

# Commands and bindings
The F* extended mode introduces the following commands:
* Simple editing commands:
	* `fem-roll-admit` (C-x C-a): helper for the "rolling admit" technique: introduces an admit at the next line. Before doing so, checks if there is another admit to move, and asks the user for removal.
	* `fem-switch-assert-assume-in-above-paragraph` (C-c C-s C-a): switches between assertions (`assert`, `assert_norm`) and assumptions (`assume`) in a block of code. Performs it so that the block then only contains assertions or only contains assumptions - converts all the assertions to assumptions if it can find some assertions, otherwise converts all the assumptions to assertions. It works inside the active selection, or on the block of code above the pointer (including the current line) if there is no selection.
	* `fem-switch-assert-assume-in-current-line` (C-S-a): same as `fem-switch-assert-assume-in-above-paragraph`but operates only on the current line.
* Advanced commands relying on meta F*:
	* `fem-insert-assert-pre-post` (C-c C-e): analyzes an effectful term and inserts assertions before and after corresponding to the proof obligations which must be satisfied for the term to be well-typed (preconditions, typing conditions including refinements), and the properties which are true afterwards (postcondition, refinement on the return type). Also introduces assertions corresponding to the "global" precondition (the precondition of the function being defined) and the goal, if those are relevant. This command operates on the term on the current line, or on the term in the active region, and can be used with saved positions (see below). The parsing algorithm being fairly basic, if the term to analyze is defined over several lines, the user must indicate it by selecting it entirely.
	* `fem-split-assert-assume-conjuncts` (C-c C-s C-u): splits the conjunctions inside an assertion/assumption and introduces one `assert` per such conjunct. The pointer must be on the assertion to analyze. Also works with saved positions, see below.
	* `fem-unfold-in-assert-assume` (C-c C-s C-f): unfolds an identifier inside an assertion/assumption. The term identifier can be understood in quite a large sense: you can unfold a top-level identifier (i.e.: a definition), but the command will analyze previous pure let-bindings and equalities in postconditions to find a term by which to replace a local variable the user may wish to "unfold". In the future, it will allow to rewrite arbitrary terms.
	* `fem-insert-pos-markers` (C-c C-s C-i): it can be difficult for the above commands to generate correct queries to send to F* for analysis, because the user may be working on a function only partly written and whose holes can be difficult to fill. It especially happens when working inside `if .. then ... else ...` expressions or branches of a match.  In such cases, it can be necessary for the user to help a bit, by indicating which term he wants to analyze, then where to stop the parsing for the query to send to F*. If the user calls `fem-insert-pos-markers` then one of the above commands, those commands will use the positition saved by `fem-insert-pos-markers` to find out the term to analyze, and will parse to the current position.


