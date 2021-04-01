# Drafts for a formalization of MoA in Coq

⚠️ the code in this directory is highly experimental and a work in progress
towards computer-checking MoA.

This directory contains several attempts at formalizing MoA in Coq. There are
three files:

* `core.v`, which contains a Coq specification of the core MoA operations using
  proper dependent types;
* `coreexpanded.v` which expands upon the core outlined in `core.v` and builds
  towards the operations required to work with padding, both in general and more
  specifically in the context of stencil computations;
* `coresigma.v` which reformulates most of the content of `core.v` using sigma
  types instead, to allow for stating theorems more easily.

`coreexpanded.v` is the most advanced of the three – and it contains a
surprising amount of lemmas only necessary to state the theorems we care about.
Going forward, `coresigma.v` is more likely to be the base on which we build –
assuming we stick with Coq. The rest is included to give a better overview of
the state of the effort.
