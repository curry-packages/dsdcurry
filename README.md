DSDCurry: A tool for Declarative Software Development
=====================================================

DSDCurry is a transformation tool which generate from a Curry module
containing pre/postconditions and specifications of operations
a new Curry module where assertions are added to check
these pre/postconditions and specifications.

The ideas of this tool and declarative software development
with specifications and pre/postconditions in Curry are
described in this paper:

Sergio Antoy, Michael Hanus:
[Contracts and Specifications for Functional Logic Programming](http://dx.doi.org/10.1007/978-3-642-27694-1_4),
Proc. of the 14th International Symposium on Practical Aspects of
Declarative Languages (PADL 2012),
Springer LNCS 7149, pp. 33-47, 2012

------------------------------------------------------------------------
How to use the tool:

After installing the tool with

    > cpm installapp dsdcurry

(which installs the binary `dsdcurry` in `~/.cpm/bin`),
you can use it as follows:

If `Mod.curry` contains your Curry module with pre/postconditions, execute

    > dsdcurry mod

to generate new module `ModC.curry` where assertions are added.

Load the new module into PAKCS and run it by

    > pakcs :load ModC

You can also transform and load the module into PAKCS in one step by

    > dsdcurry -r Mod

------------------------------------------------------------------------
Assumptions:

- Naming conventions: for an operation `f`,
  * its precondition must have the name `f'pre`
  * its postcondition must have the name `f'post`
  * its specification must have the name `f'spec` (or `f'specd` if the
    specification is deterministic which provides for stronger checking)

- Pre/postconditions or specifications are not required.

- If there is a postcondition `f'post` but no precondition `f'pre`,
  it is assumed that the precondition is defined as `(const True)`.

- If a function `f` is defined by

    f :: ...<some type>...
    f = unknown

  it will be considered as implemented, i.e., an implementation
  will be generated from a specification or postcondition (see below).
  Providing such an "unknown" definition might be necessary
  in larger programs where one wants to apply a function
  without having its final implementation.

- If there is a specification `f'spec` but no implementation of a function `f`,
  the specification will be used as a first implementation of `f`.

- If there is a postcondition `f'post` but neither a specification `f'spec`
  nor an implementation of function `f`, the postcondition will be used
  (by narrowing) as an initial implementation for `f`.
  One can select via option "`-pcs`" whether only one or all values
  generated from the postcondition should be take for the implementation.

- If there is a specification `f'spec` and an implementation of function `f`,
  the specification will be used as a postcondition for `f`.

- Any pre- or postcondition for a function `f` will be added to the
  implementation of `f` so that it will be checked at run-time.

- As a default, the complete computed value of a function will be
  checked in a postcondition. Alternatively, one can also check
  only some observed part of the computed result. For this purpose,
  one can define a function `f'post'observe` that maps each computed
  result into some observed part.

- Pre- and postconditions can be checked in a strict, lazy, or
  (lazy) enforecable manner (this can be specified by command-line
  arguments, see below).

------------------------------------------------------------------------
Command-line arguments:

    Usage: dsdcurry [-s|-f|-l|-e|-pcs|-r|-d] <module_name>
    
    -s : generate strict assertions (default)
    -l : generate lazy assertions
    -f : generate lazy enforceable assertions
    -e : encapsulate nondeterminism of assertions
         (see examples/ndassertion.curry)
    -pcs : take single result of funcs generated from postconditions
    -r : load the transformed program into PAKCS
    -d : show assertion results during execution (with -r)

------------------------------------------------------------------------
Examples:

See programs in the directory `examples`

------------------------------------------------------------------------
Known problems:

- Sometimes the type signatures of the generated functions
  are too general if the type signature of pre/postconditions are more
  general than the type of the generated function that is required by
  the later use of the function.

  Solution: add restrictive type signature to pre/postconditions in
            your program or add a type signature for the function
            with a body "`f = unknown`"

- Strict assertions make operations stricter, thus, changing the run-time
  behavior.

  Solution: use lazy assertions (option "`-l`"), but this has the risk
            that some assertions will never be checked

  Better solution: use enforceable assertions (option "`-f`"), i.e.,
    evaluate assertion lazily but enforce their evaluation at the
    end by evaluating the main expression "e" by "enforce e"
    (or "enforceIO e" if e is an I/O action).

------------------------------------------------------------------------
