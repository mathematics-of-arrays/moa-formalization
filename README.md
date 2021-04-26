# Formalizing the Mathematics of Arrays using Proof Assistants

⚠️ The code in this directory is highly experimental and a work in progress
towards computer-checking MoA.

For now, the proofs can be found in the [coq/drafts](coq/drafts) directory.

## State of the work

The exercise of proving theorems about multidimensional arrays in Coq has
proven to be rather painful. This is at least partially because we used
"proper" dependent types in our most advanced attempt, which are just not
convenient to work with in Coq.

Based on these insights, we are currently exploring two alternative solutions:

- a Coq formalization that relies on Sigma types (see
  [coq/drafts/coresigma.v](coq/drafts/coresigma.v));
- a formalization in Agda (*not pushed to the repo yet*).

There is less uncertainty about how the second option will turn out, thanks to
the previous efforts of the authors of [agda-array](https://github.com/ashinkarov/agda-array).
