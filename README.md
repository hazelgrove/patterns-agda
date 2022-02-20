
# patterns-agda

This repository is a mechanization of the work described in our [paper link TODO](TODO) on pattern matching with holes. It includes almost all of the definitions and proofs from the paper.

The only results missing from this mechanization are those regarding decidability of entailment and the constraint incon judgement. These proofs involve finite sets and algorithms which are not structurally recursive, making it inordinately difficult to verify them in Agda, so we do not attempt to do so here. Decidability of the incon judgement, however, has been verified using the Z3 Theorem Prover.

# How To Check These Proofs - 	TODO

These proofs are known to check under `Agda 2.6.2`. The most direct, if not the easiest, option to check the proofs is to install that version of Agda or one compatible with it, download the code in this repo, and run `agda all.agda` at the command line.

# Where To Find Each Theorem

All of the judgements defined in the paper are given in the various *-core.agda files. The syntax is meant to mirror the on-paper notation as closely as possible, with some small variations because of the limitations of Agda syntax.

For easy reference, the proofs for the theorems in order of appearance in the paper text can be found as follows:

- TODO

The extended paper with an appendix goes into more detail for some lemmas and definitions omitted from the main paper, some of which have been mechanized as well. Those can be found as follows:

- TODO

# Description of Agda Files

The theorem statements rely on a variety of lemmas and smaller claims or observations that aren't explicitly mentioned in the paper text. What follows is a rough description of what to expect from each source file; more detail is provided in the comments inside each.

On paper, we typically take it for granted that we can silently α-rename terms to equivalent terms whenever a collision of bound names is inconvenient. In a mechanization, we do not have that luxury and instead must be explicit in our treatment of binders in one way or another. In our development here, we assume that all terms are in an α-normal form where binders (including pattern hole names) are globally not reused.

That manifests in this development where we have chosen to add premises that binders are unique within a term or disjoint between terms when needed. These premises are fairly benign, since α-equivalence tells us they can always be satisfied without changing the meaning of the term in question. Other standard approaches include using de Bruijn indices, Abstract Binding Trees, HOAS, or PHOAS to actually rewrite the terms when needed. We have chosen not to use these techniques because _almost all_ of the theory we're interested in does not need them and their overhead quickly becomes pervasive, obfuscating the actual points of interest.

Similarly, we make explicit some premises about disjointness of contexts or variables being apart from contexts in some of the premises of some rules that would typically be taken as read in an on-paper presentation. This is a slightly generalized version of Barendregt's convention (Barendregt, 1984), which we also used in our Hazel mechanizations for the same reason.

Both hole and type contexts are encoded as Agda functions from natural numbers to optional contents. In practice, these mappings are always finite. 

## Deviations from the Paper

To avoid obsfucating the core idea of our approach, a few benign technical details are supressed on paper, but must be explicitly handled in the mechanization here. We also require a few small changes to support Barendregt's convention. Explicitly, these deviations are as follows:
- Exhaustiveness and redundancy checking are given as separate judgements, rather than included as part of type assignment. While this is useful in its own right, it is in fact required to avoid positivity issues. See the comments in [statics-core.agda](statics-core.agda) for a more extensive explanation.
- Rather than simply tracking the type of each expression hole, we also include substitution environments and hole-closures à la [Hazelnut Live](https://arxiv.org/pdf/1805.00155.pdf). This does not affect the theory, but will eventually be required to support live programming, so we include it here with future development in mind.
- Each hole typing context Δ is separated into a pair Δ , Δp where Δ is used for expression holes (tracking types and hole closures) and Δp is used for pattern holes (tracking types).
- To avoid an issue related to Barendregt's convention, the ITSuccMatch transition rule does not immediately apply substitutions. Instead, it wraps the target of the match with appropriate lambdas and applications, separating these substitutions into multiple evaluation steps.
- Match expressions require a type ascription on the scrutinee.
- The match judgement e ▹ p ⊣ θ and may-match judgement e ? p require a type ascription on e, as well as on each substituted expression emitted in θ. 
- The entailment judgements require type ascriptions on the contraints.
- Cursor erasure for rules is formulated as a judgement rather than a function.

The explanation for why we modify the ITSuccMatch rule is somewhat subtle, and it is solely related to our representation of binders rather than any actual aspect of the theory. Since we only have half-annotated lambdas, this change is also what necessitates all of additional the type ascriptions enumerated above. See the comment on the `apply-substs` function in [dynamics-core.agda](dynamics-core.agda) for a more extensive explanation.

## Postulates

We postulate function extensionality in [Prelude.agda](Prelude.agda). This is known to be independent from Agda, and while not required, it simplifies reasoning about contexts as finite functions. There are no other postulates in this development.

## Meta

- [all.agda](all.agda) is morally a make file: it includes every module in
  every other file, so running `$ agda all.agda` on a clean clone of this
  repository will recheck every proof from scratch. It is known to load
  cleanly with `Agda version 2.6.2`. While we have not tested it on any other
  version, any version recent enough to include the new `in` syntax for the
  [inspection idiom](https://agda.readthedocs.io/en/v2.6.1/language/with-abstraction.html#the-inspect-idiom) will likely suffice.

## Prelude and Datatypes

These files give definitions and syntactic sugar for common elements of type theory (sum types, products, sigmas, etc.) and basic data types that are used pervasively throughout the rest of the development.

- [Bool.agda](Bool.agda)
- [List.agda](List.agda)
- [Nat.agda](Nat.agda)
- [Prelude.agda](Prelude.agda)

## Core Definitions

- [core.agda](core.agda) gives the syntax for expressions in Peanut
- [value-judgements.agda](value-judgements.agda) defines the the e val and e notintro judgements and a few quick lemmas.
- [result-judgements.agda](result-judgements.agda) defines the e indet and e final judgements and a few quick lemmas.
- [constraints-core.agda](constraint-core.agda) defines the syntax of the incomplete constraint language. As well, it defines constraint typing, ξ refutable, ξ possible, and the satisfaction judgements.
- [complete-constrants-core.agda](complete-constraints-core.agda) defines the syntax of the complete constraint language. As well, it defines complete contraint typing, satisfaction judgements, and the dual, truthify, and falsify functions.
- [patterns-core.agda](patterns-core.agda) defines the various matching judgements, pattern typing, and the p refutable judgement.
- [dynamics-core.agda](dynamics-core.agda) defines substitution, instruction transitions, and the values judgement.
- [statics-core.agda](statics-core.agda) defines type assignment, constraint entailment, exhaustiveness, and nonredundancy.

## Contexts and Binders

These files build up the definitions needed for our representation of variables and contexts as well as Barendregt's convention.

- [contexts.agda](contexts.agda) defines contexts as functions from natural numbers to possible contents.
- [freshness.agda](freshness.agda) defines judgements which state whether a variable is unbound or fresh in a term, considering either just variables in expressions or just hole names.
- [binders-disjointness.agda](binders-disjointness.agda) gives judgements stating that two terms share no binders or no hole binders a lá Barendregt.
- [binders-uniqueness.agda](binders-uniqueness.agda) gives judgements stating that a term has globally unique binders, i.e., that any two subterms of it are binders-disjoint.

## Structural Properties

These lemmas pove the expected structural properties for contexts in the various judgements:

- [exchange.agda](exhange.agda)
- [weakening.agda](weakening.agda)

## Decidability 

These files establish the decidability of various judgements. Most of these results are fairly obvious.
- [freshness-decidable.agda](freshness-decidable.agda) proves that the various freshness and unbound-in judgements are decidable.
- [htyp-decidable.agda](htyp-decidable.agda) proves that equality of types is decidable.
- [satisfy-decidable.agda](satisfy-decidable.agda) proves that the satisfy, maysatisfy, and satisfyormay functions given in the paper correctly decide whether an expression satisfies an incomplete constraint.
- [complete-satisfy-decidable.agda](complete-satisfy-decidable.agda) proves decidability of satisfaction for complete constraints.
- [notintro-decidable.agda](notintro-decidable.agda) proves that the e notintro judgement is decidable.
- [possible-decidable.agda](possible-decidable.agda) proves that the ξ possible judgement is decidable.
- [xrefutable-decidable.agda](xrefutable-decidable.agda) proves that ξ refutable judgement is decidable.

## Lemmas and Smaller Claims

These files each establish smaller claims that are either not mentioned in the paper, mentioned only in passing, or related to technical details about the mechanization.

- [binders-disjoint-symmetric.agda](binders-disjoint-symmetric.agda) argues that the binders-disjoint judgements are symmetric in their two arguments. 
- [hole-binders-disjoint-symmetric.agda](hole-binders-disjoint-symmetric) argues that the hole-binders-disjoint judgements are symmetric in their two arguments.
- [lemmas-contexts.agda](lemmas-contexts.agda) provides various lemmas for reasoning about contexts.
- [lemmas-freshness.agda](lemmas-freshness.agda) establishes various lemmas regarding freshness and binders. For example, we show that the type Γp of a pattern only records binders occuring in the pattern. As well, it proves that any unbound variable disjoint from a typing context is fresh in the typed term.
- [lemmas-or-append.agda](lemmas-or-append.agda) defines a function ξ1 ∨+ ξ2 which is similar to ξ1 ∨ ξ2, but appending ξ2 at the inner most level if ξ1 itself is a series of constraints combined with ∨. This is supressed on paper, but needed when we compute the constraint emitted by the cursor erasure of a list of rules. See the comments in the file for more information.
- [lemmas-patterns.agda](lemmas-patterns.agda) gives miscellaneous easy lemmas about patterns, rules, and their typing judgements.
- [lemmas-values.agda](lemmas-values.agda) argues that the values judgement behaves as expected, showing that every indet expression has a value, and that if an expression does not satisfy or may satisfy a constraint then neither do its values.
- [lemmas-satisfy.agda](lemmas-satisfy.agda) establishes various results about satisfaction judgements, as well as their relation to the refutable and possible judgements.

There is also a collection of files which shows that all of our judgements are well-behaved with respect to substituting an expression for a variable. These are only needed by preservation.
- [lemmas-subst-disjointness.agda](lemmas-subst-disjointness.agda)
- [lemmas-subst-value.agda](lemmas-subst-value.agda)
- [lemmas-subst-result.agda](lemmas-subst-result.agda)
- [lemmas-subst-matching.agda](lemmas-subst-matching.agda)
- [lemmas-subst-satisfy.agda](lemmas-subst-satisfy.agda)
- [lemmas-subst-list.agda](lemmas-subst-list.agda)
- [lemmas-subst-type.agda](lemmas-subst-type.agda)
- [lemmas-subst-exhaustive.agda](lemmas-subst-exhaustive.agda)
- [lemmas-subst-nonredundant.agda](lemmas-subst-nonredundant.agda)

## Theorems
The following files prove the main theorem from the paper.
- [satisfy-exclusive.agda](satisfy-exclusive.agda) argues that for an expression e and an incomplete constraint ξ of the same type, exactly one of the following holds: e satisfies ξ, e may satify ξ, or e does not satisfy or may satisfy ξ. 
- [complete-satisfy-exclusive.agda](complete-satisfy-exclusive.agda) argues that for an expression e and a constraint ξ of the same type, either e satisfies ξ or e satisfies the dual of ξ, but not both.
- [matching-determinism.agda](matching-determinism.agda) argues that for an expression e and a pattern p of the same type, exactly one of the following holds: e matches p, e may match p, or e does not match p.
- [matching-coherence.agda](matching-coherence.agda) shows that patterns and their constraints behave as expected, e.g., an expression matches the pattern if and only if it satisfies the emitted constraint.
- [complete-relationship.agda](complete-relationship.agda) establishes the relationship between the incomplete and complete constraint languages via the falsify and truthify functions
- [material-entailment.agda](material-entailment.agda) proves that ξ1 entailing ξ2 is equivalent to ⊤ entailing (dual ξ1) ∨  ξ2
- [preservation.agda](preservation.agda) proves that evaluating an expression one step does not change its type.
- [finality.agda](finality.agda) proves that any final expression is actually final, i.e., it cannot be evaluated further.
- [determinism.agda](determinism.agda) proves that every well-typed expression is either val, indet, or steps to a unique expression.