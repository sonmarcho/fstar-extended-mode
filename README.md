# F* extended mode
The F* extended mode contains files which extend the [F* emacs mode](https://github.com/FStarLang/fstar-mode.el). It provides simple code editing commands to help switching between assertions and assumptions in the code, to save time when progressing on a proof, or to help with techniques like the "rolling-admit". It also provides more advanced commands which perform term unfoldings or insert context information at specific points in the code.

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
                        ;; TODO: Put the path to the local copy of the F* extended mode here
                        " --include " (getenv "HOME") "/fstar-extended-mode "
                        "load FEM.Process" ;; Load the compiled tactics used by the extended mode
                        )
                     ;; If the above failed, use a default configuration
                     (error (concat
                     	     ;; TODO: Put the relevant F* directories here
                             "--include " (getenv "HOME") "/hacl-star/lib "
                             ;; TODO: Put the path to the local copy of the F* extended mode here
                             "--include " (getenv "HOME") "/fstar-extended-mode "
                             "load FEM.Process" ;; Load the compiled tactics used by the extended mode
                             ;; TODO: Optional
                             "--debug yes --log_queries --use_hints --cache_checked_modules"
                             )))))
      (split-string argstr))))
(setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
(setq fstar-subp-debug t)
```

The F* extended mode needs the `use-package` package. You can install it by using Melpa (`M-x list-packages`, then go to `use-package` and click on "Install").

Then, you need to load the extended mode. You can do it simply by inserting the following command in your `.emacs` file:

```
;; Replace PATH-TO-REPO by the path to the cloned extended mode repository
;; Warning: if the path to the repo is "/home/johndoe/fstar-extended-mode", you must write:
;; "/home/johndoe/fstar-extended-mode/fstar-extended-mode"
;; (this path actually indicates where to find the .el file)
(load "~/PATH-TO-REPO/fstar-extended-mode")
```

Finally, you need to build it. Just go inside the clone directory and run `make`.

**Important:** whenever you update the directory, run `make clean && make`.

# Commands and bindings
The F* extended mode introduces the following commands:
| Command       | Key binding           | Description  |
| :------------- |:-------------:| :-----|
| `fem-roll-admit` | (C-c C-e C-r) | Helper for the "**r**olling admit" technique |
| `fem-switch-assert-assume-in-above-paragraph` | (C-c C-e C-a) | Switch between **a**ssertions and **a**ssumptions in the paragraph above the pointer, or in the current selection |
| `fem-analyze-effectful-term-with-goal` | (C-c C-e C-e) | **E**xpand an effectful term to insert context information (precondition, type obligations, postcondition) |
| `fem-split-assert-assume-conjuncts` | (C-c C-e C-s) | **S**plit the conjuncts in an assertion/assumption |
| `fem-unfold-in-assert-assume` | (C-c C-e C-u) | **U**nfold/substitute a term in an assertion/assumption |
| `fem-insert-pos-markers` | (C-c C-e C-i) | **I**nsert a marker in the code for two-steps execution, in case of parsing issues |

* Simple editing commands:
	* `fem-roll-admit` (C-x C-a): helper for the "rolling admit" technique: introduces an admit at the next line. Before doing so, checks if there is another admit to move, and asks the user for removal.
	* `fem-switch-assert-assume-in-above-paragraph` (C-c C-s C-a): switches between assertions (`assert`, `assert_norm`) and assumptions (`assume`) in a block of code. Performs it so that the block then only contains assertions or only contains assumptions - converts all the assertions to assumptions if it can find some assertions, otherwise converts all the assumptions to assertions. It works inside the active selection, or on the block of code above the pointer (including the current line) if there is no selection.
	* `fem-switch-assert-assume-in-current-line` (C-S-a): same as `fem-switch-assert-assume-in-above-paragraph`but operates only on the current line.
* Advanced commands relying on meta F*:
	* `fem-insert-assert-pre-post` (C-c C-e): analyzes an effectful term and inserts assertions before and after corresponding to the proof obligations which must be satisfied for the term to be well-typed (preconditions, typing conditions including refinements), and the properties which are true afterwards (postcondition, refinement on the return type). Also introduces assertions corresponding to the "global" precondition (the precondition of the function being defined) and the goal, if those are relevant. This command operates on the term on the current line, or on the term in the active region, and can be used with saved positions (see below). The parsing algorithm being fairly basic, if the term to analyze is defined over several lines, the user must indicate it by selecting it entirely.
	* `fem-split-assert-assume-conjuncts` (C-c C-s C-u): splits the conjunctions inside an assertion/assumption and introduces one `assert` per such conjunct. The pointer must be on the assertion to analyze. Also works with saved positions, see below.
	* `fem-unfold-in-assert-assume` (C-c C-s C-f): unfolds an identifier inside an assertion/assumption. The term identifier can be understood in quite a large sense: you can unfold a top-level identifier (i.e.: a definition), but the command will analyze previous pure let-bindings and equalities in postconditions to find a term by which to replace a local variable the user may wish to "unfold". In the future, it will allow to rewrite arbitrary terms.
	* `fem-insert-pos-markers` (C-c C-s C-i): it can be difficult for the above commands to generate correct queries to send to F* for analysis, because the user may be working on a function only partly written and whose holes can be difficult to fill. It especially happens when working inside `if .. then ... else ...` expressions or branches of a match.  In such cases, it can be necessary for the user to help a bit, by indicating which term he wants to analyze, then where to stop the parsing for the query to send to F*. If the user calls `fem-insert-pos-markers` then one of the above commands, those commands will use the positition saved by `fem-insert-pos-markers` to find out the term to analyze, and will parse to the current position.

# Tutorial
You can learn how to use the package by going through the [tutorial file](./FEM.Tutorial.fst).
Note that this file also contains useful tips and tricks, for example workarounds in case the commands fail because of parsing issues.
