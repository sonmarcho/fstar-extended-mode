# F* extended mode

I'm currently working on moving the code in this repo to F\* and to the
[fstar-mode.el](https://github.com/FStarLang/fstar-mode.el) repo. The F\* meta
functions have already been moved to master, and I still need to move the elisp
code to [fstar-mode.el](https://github.com/FStarLang/fstar-mode.el).

If you currently want to use the F\* extended mode, you have to do the
following:

* clone https://github.com/FStarLang/fstar-mode.el
* checkout the branch `son_meta`
* add the following line (and modify it to use the proper path) in your `.emacs`
  to bypass the `fstar-mode.el` Melpa package:
  `(require 'fstar-mode "~/fstar-mode.el/fstar-mode.el")`
* restart emacs, and that's it!

Do not hesitate to provide feedbacks (choice of shortcuts for the commands,
improvements, new commands, etc.)!

## Tutorial

For a gentle introduction to the extended mode, open the file:
[FStar.InteractiveHelpers.Tutorial.fst](https://github.com/FStarLang/FStar/blob/master/examples/interactive/FStar.InteractiveHelpers.Tutorial.fst)
which has explanations and gives the bindings. 

## Commands and bindings
The F* extended mode introduces the following commands:
| Command       | Key binding           | Description  |
| :------------- |:-------------:| :-----|
| `fem-roll-admit` | (C-S-r) | Helper for the "**r**olling admit" technique |
| `fem-switch-assert-assume` | (C-S-s) | Switch between **a**ssertion and **a**ssumption under the pointer or in the current selection |
| `fem-analyze-effectful-term-no-pre` | (C-c C-e C-e) | Analyze an **e**ffectful term to insert context information (precondition, type obligations, postcondition...) |
| `fem-analyze-effectful-term-with-goal` | (C-c C-e C-g) | Analyze an effectful term to insert context information (precondition, type obligations, postcondition...), including the **g**lobal precondition |
| `fem-split-assert-assume-conjuncts` | (C-c C-e C-s) | **S**plit the conjuncts in an assertion/assumption |
| `fem-unfold-in-assert-assume` | (C-c C-e C-u) | **U**nfold/substitute a term in an assertion/assumption |

## Known limitations
* the .fst files containing the meta F\* functions are not automatically loaded when we start the interactive mode, forcing the user to insert instructions like `module FEM = FEM.Process` in the code before starting F\*, which is cumbersome
* the meta F\* functions which perform the analysis currently use the \*Messages\* buffer as output: this is not very safe nor convenient, and it would be good to have a dedicated output buffer in the future
* when dealing with "global" pre and postconditions (i.e.: the current function's assumptions and goal), we don't control the way F\* "unfolds" the effects, often leading to unexploitable assertions
* there are many (pretty) printing issues:
	* fully named identifiers like `FStar.Native.Some` clutter the output
	* the output printed by F\* is not always valid F\* syntax, or can't be parsed because, for instance, it uses private identifiers like `Prims.logical`
