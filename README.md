# Cutting Out Continuations

This repository contains the supplementary material for the paper
"Cutting Out Continuations" by Patrick Bahr and Graham Hutton.  The
material includes Coq formalisations of all calculations in the
paper. In addition, we also include Coq formalisations for
calculations that were mentioned but not explicitly carried out in the
paper.

## Paper vs. Coq Proofs


The Coq proofs proceed as the calculations in the paper. There are,
however, two minor technical difference due to the nature of the Coq
system.

  1. In the paper the derived abstract machines (AMs) are tail
     recursive, first-order functions. The Coq system must be able to
     prove termination of all recursive function definitions. Since
     Coq's termination checker is not powerful enough to prove
     termination for some of the AMs or the AMs are not expected to
     terminate in general (AMs for lambda calculi / for language with
     loops), we had to define the AMs as relations instead. More
     precisely, all AMs are defined as a small-step semantics. Each
     tail recursive function of an AM corresponds to a configuration
     constructor in the small-step semantics. As a consequence, the
     calculations do not prove equations, but rather instances of the
     relation `=>>`, which is the transitive, reflexive closure of the
     relation `==>` that defines the AM.

  2. The Coq files contain the final result of the calculation, and
     thus do not reflect the *process* of discovering the definition
     of the abstract machine. That is, the files already contain the
     full definitions of the abstract machine. But we used the same
     methodology as described in the paper to *develop* the Coq
     proofs. This is achieved by initially defining the `CONT` data
     type as an empty type and defining the `==>` relation as an empty
     relation (i.e. with no rules). This setup then allows us to
     calculate the definition of the `CONT` data type and the AM as
     described in the paper.

## File Structure


Below we list the relevant Coq files for the calculations in the
paper:

 - [Arith.v](Arith.v): arithmetic expressions (section 3)
 - [LambdaCBV.v](LambdaCBV.v): call-by-value lambda calculus (section 4)

In addition we also include calculations for the following languages:

 - [LambdaCBVArith.v](LambdaCBVArith.v): call-by-value lambda
   calculus + arithmetic
 - [LambdaCBName.v](LambdaCBName.v): call-by-name lambda calculus
 - [LambdaCBNameArith.v](LambdaCBNameArith.v): call-by-name lambda
   calculus + arithmetic
 - [LambdaCBNeedArith.v](LambdaCBNeedArith.v): call-by-need lambda
   calculus + arithmetic

The remaining files are used to define the Coq tactics to support
reasoning in calculation style ([Tactics.v](Tactics.v)) and to specify
auxiliary concepts ([Heap.v](Heap.v), [ListIndex.v](ListIndex.v)).

## Technical Details


### Dependencies

- To check the proofs: Coq 8.4pl5
- To step through the proofs: GNU Emacs 24.3.1, Proof General 4.2

### Proof Checking

To check and compile the complete Coq development, you can use the
`Makefile`:

```shell
> make
```

### Generate Documentation

To generate the HTML documentation for the Coq calculations use `make`
to build the `html` target as follows:

```shell
> make html
```

The generated documentation is then found in the `html` subdirectory.
