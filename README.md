# F* extended mode
The F* extended mode contains files which extend the [F* emacs mode](https://github.com/FStarLang/fstar-mode.el). It provides simple code editing commands to help write proofs quicker, and more advanced commands to help retrieve informative feedback from F\*.

## Setup
We intend to merge the F\* extended mode with the F\* emacs mode and the F\* repositories in the future, which will make installation very easy. However, for now, there is a bit of setup to do.

### 1. Install the F\* emacs mode
If not done yet, go [here](https://github.com/FStarLang/fstar-mode.el).

### 2. Install the use-package emacs package
You can install it by using Melpa:

* `M-x list-packages`
* search the list of packages until you find `use-package`
* click on "Install"

### 3. Clone the package
```bash
sudo git clone git@github.com:Kachoc/fstar-extended-mode.git
```

### 4. Build it
```bash
make -C fstar-extended-mode
```

**Important:** whenever you update the directory, run:
```bash
make -C fstar-extended-mode clean && make -C fstar-extended-mode
```

### 5. Configure emacs to load the package at launch time
Insert this in your `.emacs` file:

```elisp
;; Replace PATH-TO-REPO by the path to the cloned F* extended mode repository
;; WARNING: if the path to the repo is "/home/johndoe/fstar-extended-mode", you must write:
;; "/home/johndoe/fstar-extended-mode/fstar-extended-mode"
;; and not:
;; "/home/johndoe/fstar-extended-mode"
;; (this path actually indicates where to find the .el file)
(load "~/PATH-TO-REPO/fstar-extended-mode")
```

### 6. Configure the F\* options
The simplest way is to insert the following code in your `.emacs` file (this code was adapted from [here](https://github.com/project-everest/mitls-fstar#configuring-emacs-mode)). Look for the **TODOs**.

```elisp
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
                        ;; TODO: Path to the F* extended mode folder
                        " --include " (getenv "HOME") "/fstar-extended-mode "
                        ;; Load the compiled tactics used by the extended mode
                        "load FEM.Process"
                        )
                     ;; If the above failed, use a default configuration
                     (error (concat
                     	     ;; TODO: Put the relevant F* directories here
                             "--include " (getenv "HOME") "/hacl-star/lib "
                       	     ;; TODO: Path to the F* extended mode folder
                             "--include " (getenv "HOME") "/fstar-extended-mode "
                             ;; Load the compiled tactics used by the extended mode
                             "load FEM.Process"
                             ;; TODO: Optional debugging options (keep or remove)
                             "--debug yes --log_queries --use_hints --cache_checked_modules"
                             )))))
      (split-string argstr))))
(setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
(setq fstar-subp-debug t)
```

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

## Tutorial
You can learn how to use the package by going through the [tutorial file](./FEM.Tutorial.fst).

## Known limitations
* the .fst files containing the meta F\* functions are not automatically loaded when we start the interactive mode, forcing the user to insert instructions like `module FEM = FEM.Process` in the code before starting F\*, which is cumbersome
* the meta F\* functions which perform the analysis currently use the \*Messages\* buffer as output: this is not very safe nor convenient, and it would be good to have a dedicated output buffer in the future
* when dealing with "global" pre and postconditions (i.e.: the current function's assumptions and goal), we don't control the way F\* "unfolds" the effects, often leading to unexploitable assertions
* there are many (pretty) printing issues:
	* fully named identifiers like `FStar.Native.Some` clutter the output
	* the output printed by F\* is not always valid F\* syntax, or can't be parsed because, for instance, it uses private identifiers like `Prims.logical`
