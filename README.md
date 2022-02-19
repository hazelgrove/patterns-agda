
# patterns-agda

This repository is a mechanization of the work described in our [paper link TODO](TODO) on pattern matching with holes. It includes almost all of the definitions and proofs from the paper.

The only results missing from this mechanization are those regarding decidability of entailment and the constraint incon judgement. These proofs involve finite sets and algorithms which are not structurally recursive, making it inordinately difficult to verify them in Agda, so we do not attempt to do so here. Decidability of the incon judgement, however, has been verified using the Z3 Theorem Prover.

# How To Check These Proofs - 	TODO

These proofs are known to check under `Agda 2.6.2`. The most direct, if not the easiest, option to check the proofs is to install that version of Agda or one compatible with it, download the code in this repo, and run `agda all.agda` at the command line.

Alternatively, we have provided a [Docker file TODO](Dockerfile) to make it easier to build that environment and check the proofs. To use it, first install [Docker](https://www.docker.com/products/docker-desktop), make sure the Docker daemon is running, and clone this repository to your local machine. Then, at a command line inside that clone, run

```
docker build -t peanut .
```

This may take a fair amount of time. When it finishes, run

```
docker run peanut
```

This should take less than a minute, produce a lot of output as Agda checks each module and function, and end with either the line `Finished all.` or `Loading all (/all.agdai).` to indicate success, depending on Docker-level caching.

Most text editors that support Agda can be configured to use the version instead a Docker container instead of your host machine, so you can experiment with or evolve this code without making too much of a mess. For some example instructions, see the [docker-agda repo](https://github.com/banacorn/docker-agda).

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

Similarly, we make explicit some premises about disjointness of contexts or variables being apart from contexts in some of the premises of some rules that would typically be taken as read in an on-paper presentation. This is a slightly generalized version of Barendregt's convention (Barendregt,
1984), which we also used in our [Hazel mechanizations](https://github.com/hazelgrove/agda-popl17) for the same reason.

Both hole and type contexts are encoded as Agda functions from natural numbers to optional contents. In practice, these mappings are always finite. 

## Deviations from the Paper

To avoid obsfucating the core idea of our approach, a few benign technical details are supressed on paper, but must be explicitly handled in the mechanization here. We also require a few small changes to support Barendregt's convention. Explicitly, these deviations are as follows:
- Exhaustiveness and redundancy checking are given as separate judgements, rather than included as part of type assignment. While this is useful in its own right, it is in fact required to avoid positivity issues. See the comments in [statics-core.agda](statics-core.agda) for a more extensive explanation.
- Rather than simply tracking the type of each expression hole, we also include hole-closures à la [Hazelnut Live](https://arxiv.org/pdf/1805.00155.pdf). This does not affect the theory, but will eventually be required to support live programming, so we include it here with future development in mind.
- Each hole typing context Δ is separated into a pair Δ , Δp, with Δ tracking expression holes and their closures and Δp tracking pattern holes and their types. 
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

These files give definitions and syntactic sugar for common elements of
type theory (sum types, products, sigmas, etc.) and basic data types that
are used pervasively throughout the rest of the development.

- [Bool.agda](Bool.agda)
- [List.agda](List.agda)
- [Nat.agda](Nat.agda)
- [Prelude.agda](Prelude.agda)

## Core Definitions

- TODO

## Structural Properties

- TODO

## Theorems

- TODO

### Type Safety
 
- TODO

## Lemmas and Smaller Claims


These files each establish smaller claims that are either not mentioned in
the paper or mentioned only in passing. In terms of complexity and
importance, they're somewhere between a lemma and a theorem.

- TODO

These files contain technical lemmas for the corresponding judgement or
theorem. They are generally not surprising once stated, although it's
perhaps not immediate why they're needed, and they tend to obfuscate the
actual proof text. They are corralled into their own modules in an effort
to aid readability.

- TODO