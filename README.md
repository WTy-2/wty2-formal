# wty2-formal
An attempt to formalise WTy2's type system inside of Idris2 (basically everything so far is inside [Tree.idr](https://github.com/WTy-2/wty2-formal/blob/trunk/src/Checker/Tree.idr))

If it goes well, this could feasibly turn into a WTy2 typechecker/interpreter:
- Typechecking into an indexed AST is painful (as I experienced during WACC) but also is an extremely powerful way to prevent typechecker bugs (hopefully no need to build a giant test suite)
- To typecheck WTy2 code in-general beta-reduction must be perfomed, so if we write a typechecker, we will get an interpreter for free (the other way of looking at this is that to write a typechecker, we are forced to write an interpreter - I prefer the former `;)`)
