# General remarks and ideas for F*

## Remarks and good practices
### Rolling admits
### Switching between assert and assume (and its caveat) when writing a proof
### Checking why a precondition/goal fails (and unfolding correctly terms in a general manner)
### Arithmetic proofs
### Dealing with if/match one branch at a time to keep precision in the F* error messages
### Make tests with your functions before proving anything about them
Example of the *check_well_formed_pattern* for Noise which caused me headaches because I had made a mistake and had trouble fixing it because I was basically blind (it would have been super simple to solve this problem in HOL4 or Coq).

### Dealing with tedious functors instanciations

## Ideas
### Tactics for instanciating and showing pre/postconditions/goals or for unfolding functions
It often happens that F* can't prove a precondition and we don't know why, or we call a theorem but this doesn't allow the proof to succeed and we want to check that calling this theorem gives us what we expect/need, we don't know what the current goal is (a big problem of instanciating functors, but not limited to that) or we need to unfold some function (and potentially several terms inside) to check what it is equal to.
In those situations, my current way of doing is to copy-paste the appropriate precondition/postcondition/goal/definition and put it in an assert/assume preceded by the appropriate let-binding to instanciate the function parameters with the proper variables. This can be very tedious, especially if we need later to remove those let-bindings to see better what's going on, or if we need to unfold some subterms (in which case I basically redo the same).
It should be able to automate that with tactics, at least to generate what should be inside the assert/assume, and even to combine it with emacs commands to automatically insert in the proof what we need.
Small remark: it would be nice to be able to send an ad-hoc function for type-checking to F* and retrieve the result without the user noticing it. Even better: it would be nice to be able to lax-typecheck but still execute (some) tactics (for normalization and printing).

### Rewriting system
I sometimes miss using a rewriting system, because it is sometimes very difficult to see what is going on when a proof fails, while with a rewriting system you apply rewriting rules which is a bit similar to normalizing the terms of your proof until you get stuck, where you actually need to think about what you need to do by calling the appropriate lemmas or fixing your functions/lemma, before continuing to rewrite, etc.
I made a few tests with the F* tactics system to try to reimplement functions similar to what we can find in HOL4 (like rewriting greedily with a list of theorems, or rewriting by using all the equalities in the context -i.e.: the context of the proof, not all the equality theorems available) but I encountered the following problems:
* the general rewriting tactics don't always work (they needed a bit of debugging at that time)
* the tactics I ended up with are super slow, and I see no way of making them fast besides making some rewriting operations native. Also note that when trying to apply a rewriting theorem in F*, there may be non-trivial preconditions/type checking to perform through the SMT, and I don't really know how this works and how to mitigate its impact on performance (by aborting early).

I noticed the calc constructions are pretty solid when we need to make a stable proof step by step, but are very fastidious to write because at every step the user needs to:
1. think about what needs to be done
2. find the appropriate theorem
3. instanciate the theorem correctly
4. write what the result of applying the theorem is (which can be pretty annoying if the theorem is about a subterm of the term studied in the calc)
I think it may be possible to use tactics to (more) easily generate such calc proofs.
We can imagine functions which could take a list of theorems as parameters and apply them greedily one after another before printing the corresponding calc (theorem applications and every step of the rewriting), which would allow to solve **3** and **4**. Besides, we could define libraries of useful theorems (for arithmetic for example) which we could apply greedily in a HOL4 style, so that it would also solve **1** and **2** for *standard* problems.
Of course, such tactics would probably be super slow, but that's not really a problem because they would only be used to generate the calc once, and in the end using them would probably be faster than doing all the steps by hand.
Note that one subtelty to take into account would be the fact that we may have to mix between normalization and theorem applications. There is also the problem of the preconditions to discharge. For example, it may be needed to show that some number is > 0 before using it in a theorem  (for example, I often had to prove that the multiplication of two positive numbers is positive too - Z3 can't do that if we deactivate non-linear arithmetic).

### Ad-hoc tactic calls
In order to make the use of tactics to help *writing* proofs (by generating proof scripts which would be copy-pasted by the user) easier, it would be nice to be able to call tactics without the *assert(...) by ...* construct.

### Make a library of emacs commands to help generating proofs in emacs
I already have a *rolling-admit* command as well as a command to switch between *assert* and *assume*. Even though they are very rudimentary and could be improved, they are super useful.

### Identify the failing proof obligations more precisely
### Make the interactive proofs more deterministic
Solve the problem of: *adding lines at the end of the proof have the side effect of changing the behaviour of the prover on the preceding lines of the proof*, which basically means: *it is not because checking parts of the proof independently from each other succeeded that the full proof will succeed, and in a reasonable time (in the worst case it might even loop)*.

It would be nice to be able to:
1. make every line of a proof independant of what is below
2. have the possibility not to send the proof obligations monolitically to Z3
We could then have a *one-line at a time* evaluation behaviour in interactive mode (which we mimic today with rolling admits).