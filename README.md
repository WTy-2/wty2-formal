# wty2-formal
An attempt to formalise WTy2's type system with Agda and Idris2 (I have restarted a couple times, but current progress is mostly in [Tree2.agda](./agda-src/Tree2.agda))

If it goes well, this could feasibly turn into a WTy2 typechecker/interpreter:
- Typechecking into an indexed AST is painful (as I experienced during WACC) but also is an extremely powerful way to prevent typechecker bugs (hopefully no need to build a giant test suite)
- To typecheck WTy2 code in general, beta-reduction must be perfomed, so if we write a typechecker, we will get an interpreter for free (the other way of looking at this is that to write a typechecker, we are forced to write an interpreter - I prefer the former `;)`)

## Why Agda *and* Idris2?

- I started this project in Idris2, having been drawn to it's simplicity.
- Unfortunately, Idris2's compiler is not very robust. Error messages are especially poor (often making it difficult to tell if an error is caused by a compiler bug or is a "real" problem).
- Furthermore, after experimenting with Agda, I found it's instance arguments and automatic proof search features to be much more effective than Idris2's equivalents (auto implicit arguments and proof search).
- Lean and Coq were quickly dismissed due to their lack of support for induction-recursion/induction-induction, which my encoding of WTy2's built-ins makes liberal use of (Lean4's type theory is also not very customisable - you cannot assume `Type : Type`, or disable strict positivity checking - of course these features break soundness, but they are very convenient!)
- So, for these reasons, I have (so far) found Agda to be the most enjoyable and productive language to write dependently-typed code in. I still plan to try and backport my progress to Idris2 (and believe this should not be *too* challenging with valid Agda code as a reference) in order to actually run the final typechecker (of course, Agda does support program extraction, but it is clunky - also I find discovering the differences in what different theorem provers accept quite fun, lol).

### Addendum

The story is even more complicated now. It turns out that not only am I making use of induction-recursion and induction-induction, but I am also finding "very dependent" types (types indexed by themselves) to have substantial utility in formalising WTy2. Unfortunately, neither Agda nor Idris2 officially supports these (but both have some form of perhaps-unintentional support). Subjectively, I have found Adga to be a lot more likely to get stuck in typechecking loops, and Idris2 to be actually semi-robust, though I will have to play around more.

Of course, there is always the other option of following someone else's design from the existing literature focussed around formalising dependent types in a dependently typed metatheory, but I am slightly hesitant. My goal with this project is just to be able to write a strongly typed typechecker and interpreter for WTy2; I am less concerned with how powerful the type theory of the source language/metatheory needs to be to support such a thing. Many of the papers I have looked at go to a lot of trouble to try and reduce the gap between the power of the object theory and the metatheory, which is not a concern for me (beyond there existing some vaguely practical language I can use which implements said theory).
