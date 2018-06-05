module Jellyfish.README where
open import Jellyfish.Everything

{-
This repository contains a try to verifying the implementation of a toy
functional language called Jellyfish in Agda. Right now this language didn't
even have a parser...

First let me introduce the language,
the language is roughly the same as our R6 without toplevel functions and
with much less primitve operations.
So there's no way for recursion (for reasons I would explain later.)
-}
open import Jellyfish.Core.Syntax.Typed

{-
Type checking and scope checking is not very interesting, much like
the haskell version of code. And there's no semantics preserving proof for
those two passes, because they are mere doing checking...
-}
open import Jellyfish.Core.Syntax.Raw
open import Jellyfish.Core.Syntax.Untyped
open import Jellyfish.ScopeCheck
open import Jellyfish.TypeCheck

{-
Since I am doing a verifed compiler, Let me introduce the notion of
compiler correctness first. In order to introduce the notion of correctness,
it seems I need to first introduce the notion of semantics.
-}

open import Jellyfish.Core.Semantics

{-
The semantics here is defined using the big-step semantics (each derivation
can be thought of as the execution steps of a evaluator/interpreter.) For each
expression there is a corresponding derivation that shows it evals to a certain
value.

As the compiler can be decompose into several
passes. The correctness proof can be thought of as composing the
each individual proof of each passes together:

  compile = f⊢ ∘ g⊢ ∘ h⊢ ∘ ...
  correct = f✓ ∘ g✓ ∘ h✓ ∘ ...

Each passes is a function from the source language to the target language

given 𝓒 is a compile pass,

𝓒 : Γ ⊢𝓢 A
  → Γ ⊢𝓣 A

each correctness proof is a function from the derivation of the source language
to the derivation of the target language

given 'ρ' is an evaluation environment and 'e' is an expression in the source
language, 'a' is an value in the source language.

𝓒✓ :   ρ ⊢𝓢   e ⇓   a
   → 𝓒 ρ ⊢𝓣 𝓒 e ⇓ 𝓒 a
-}

{-
There are 1.5 "compilers" in this repository. The first one compiles
to an abstract machine (much like "ZINC" for OCaml).
-}
open import Jellyfish.AbstractMachine.Syntax
open import Jellyfish.AbstractMachine.Semantics
open import Jellyfish.Compile
{-
In the talk "compiling functional languages" (https://xavierleroy.org/talks/compilation-agay.pdf)
given by Xavier Leroy in 2002, he describes three ways to give an
implementation for a langauge: interpretation, native compilation, and
compilation to abstract machine code. The design of abstract machine is chosen
to match closely the operations of the source language, so that to make
the implementation easier. Usually it would be some kind of stack machine.
As we all known, we can translate a infix expression into postfix expression
and thus get a stack machine for free by defining an evaluator for that. If you
start with a call-by-value langauge, the machine you would get is the CAM
machine as described in the "The ZINC experiment, an economical implementation
of the ML language" paper (http://caml.inria.fr/pub/papers/xleroy-zinc.pdf).
The implementation I defined here guarantees it is type-and-stack safe (for
example the then-branch and else-branch in the if expression is guaranteed to
push same amount of the stack.) They would be no chance to write an overflow
program in this langauge. The compilation amounts to do a infix-to-postfix
translation. And the proof is just a structural induction. As you can see
the proof and the function look much the same. For simple cases the
compiler/function can be derived from a correctness proof as described in
"Write Your Compiler by Proving It Correct" (http://liamoc.net/posts/2015-08-23-verified-compiler.html).
-}

{-
For the second compiler, which I intended to choose the LLVM IR as my backend.
LLVM IR uses the SSA form, which amounts to the flattened statements in our
compiler. So the compiler would have to do closure conversion, and flattening.
I find a toy compiler written in haskell which uses llvm as its backend which
I used as a reference (https://github.com/aherrmann/simply_llvm). The author
also have a talk for the implementation of that compiler (https://www.youtube.com/watch?v=Re3XgFfflzg).
-}

open import Jellyfish.SuperCombinator.Syntax.WithoutToplevels
open import Jellyfish.SuperCombinator.Syntax.WithToplevels

{-
I just finished the code part for closure conversion. Some of proofs seem
quite hard. My closure conversion is divided into 3 parts: strengthening,
closure conversion, and lambda lifting.

Given any lambda in the source langauge
  (lambda (x) body)

The closure conversion function would take this into a new constructor called
closure in the target language (ignore its actually representation for now).

In the target language we want:
  (closure body fvars)
where fvars is all the free variables (not including 'x') appeared in body.

Since I use debruijn indices for my variables, a simple strategy is to put
everything in the context/environment into 'fvars'.
-}

open import Jellyfish.Trivial

{-
But this is inefficient, so we need to a strongening on the body so that
that it only contains the free variables that actually occurs.

And doing strengthening turns out is to first annotation each variable with
its usage information and then according to the usage information trim the
used parts from the whole context. This is closely linked to the relevance
type system/relevance logic.
-}

open import Jellyfish.Relevance.Syntax
open import Jellyfish.Strengthening

{-
I didn't finish the correctness proof of this part. The strengthen⊢ is quite
involved with weakening function, so as it turned out, in order to prove
strengthen✓, I need to prove the correctness for every helper functions I've
defined. Given enough time, I think this part is doable, although tedious.
-}

open import Jellyfish.ClosureConversion
{-
Once I finished the proof in the strengthening part, the rest following almost
the same as in the trivial closure conversion algorithm.
-}

{-
After doing closure conversion:
  (closure body fvars)
for each closure, we need to lift the body part to the top levels so that,
each closure refers to a top level functions instead of explicitly containing
a block of code. And I call this process lambda lift.

Although this process seems easy, but I failed to give a correctness proof
for this lift⊢ function using induction (maybe it should take some extra
argument or I am too dumb.) The question is about generating fresh name,
since generating fresh name is bounded to be stateful/sequential, it actually
matters from where I spit out a fresh name so if we do a simple-minded
induction on the derivation tree, when it encounters a closure, it would
always start with the first debruijn indice.
-}

open import Jellyfish.LambdaLift

{-
After this pass, the code is much like the Intermediate language in the
reference compiler (he didn't do the lambda lift part which is the
major difference), I planned to use Haskell FFI in agda to do the
similar codegen work as in the reference compiler, but time is limited.

If more time is given, I can even take a step further try to do the flattening
part in agda and formalize that, then we would the codegen part would really
be trivial, right now, in the reference compiler, the codegen amounts to a
flattening plus some llvm stuff.

If even more time is given, I (probably not) can even formalize a small part of
the llvm IR so that I can prove the codegen part is correct.
-}

{-
For recursion.

Adding recursion to our source language (Jellyfish) is nontrivial, since it is
quite hard to give semantics for a turing-complete language in a language like
agda. But it's doable, as Conor McBride points out in his paper
"Turing-Completeness Totally Free" (https://pdfs.semanticscholar.org/e291/5b546b9039a8cf8f28e0b814f6502630239f.pdf)
languages like Agda, Coq can use coinduction to encoding non-terminating
computation. In addition in "Operation Semantics Using the Partially Monad" (http://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.pdf)
Nils Anders Danielsson acutally showed how to give an operational semantics(big
-step semantics) for untyped lambda calculus, using the same technique it is
possible to add a 'fix' point operator in Jellyfish. But it would make the
correctness proof of each transformation harder.
-}
