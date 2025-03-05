This is a few folders that contain theorems about topology using the Lean 4 theoremprover. The folder containing all of the important information is `topology.lean`.

It includes:
- A definition of a topology on on a set, represented as a type `X` with a "predicate of predicates" `Topology.is_open (τ: Topology X): (X → Prop) → Prop` that return whether the set is open.
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
