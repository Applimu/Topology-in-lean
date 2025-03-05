This repository contains a few folders I created that contain theorems about topology using the Lean 4 theoremprover. The only important folder is `topology.lean`. Nothing here depends on any external lean libraries (including mathlib), only the lean prelude that comes when you download lean.

I currently have:
- A definition of a topology on on a set, represented as a type `X` with a "predicate of predicates" `Topology.is_open (τ: Topology X): (X → Prop) → Prop` that return whether a given predicate is corresponds to an open set.
- Definitions of discrete, indiscrete, and empty set topologies
- A basis of a topology
- The interior of a set
- Hausdorff topologies
- Frechet topologies
- continuous functions
- closure of sets
- A few proofs of problems in a recent topology exam in topology


`Cofinite_failure.lean` contains some attempts that I made in defining cofinite predicates. 

`rationals.lean` contains a definition of rational numbers, which I am thinking about defining the topology for in the future after I make it nicer to work with.
