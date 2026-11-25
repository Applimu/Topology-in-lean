
## About
This repository contains loads of lean code which I created mainly in the spring of 2024 and 2025. It is centered around point-set topology, but also has theorems about set theory, bornology, finite sets, and cardinality. I started it when I took point-set topology at university, and decided to make a lean library to model it. It has since grown, and has a variety of theorems that are not necessarily related to topology directly.

Here is a general breakdown of the files in this repo:
- `Sets.lean` - Basic set theory and set operations
- `Functions.lean` - Useful properties of functions such as injectivity and constructions such as the image of a function.
- `Basic.lean` - Basic topology, mainly the definition of a `Topology` on a type.
- `Closures.lean` - Definition of the closure of a set. Also contains some proofs for problems that I had on an exam in the point-set topology course.
- `Separation.lean` - Contains predicates that say a topology `isHausdorff` or `isFrechet`
- `Product.lean` - Contains the definition of the product topology
- `Compact.lean` - Definition of a compact set using a tube lemma qualification.
- `Connected.lean` - Defines the notion of a connected topological space.
- `Bornology.lean` - Definition of a "Bornology" which qualifies an idea of boundedness
- `Finite.lean` - Contains multiple attempts of defining the idea of a finite type in lean. 
- `Cardinal.lean` - Defines a cardinal as a quotient on the type `Type u` by the equivalence relation where `A ~ B` iff there exists a bijection between them.
- `FunctionsMisc.lean` - Contains miscelaneous ideas that I wanted to play around with related to functions, such as cantor's paradox, constant functions, idempotent functions, and the "kernel" of a set-function.




