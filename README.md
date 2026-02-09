
## About
This repository contains loads of lean code of what I have been working on and off on for almost a year or so, which is mostly centered around Topology and Finite sets. I started it when I took point-set topology at university, and decided to make a lean library to model it. Over the summer of 2025, it got a bit stale because I had refused to create any kind of model for a set inside of the library to the point that it was becoming hard to work with.

In around September 2025, I decided that I should probably create a form of set theory, which led to the creation of `Sets.lean` which currently contains all of this library's set theory and then `Functions.lean` which contains theorems related to injectivity and surjectivity. 

Part of the reason I came back was because I really wanted to define a notion of a finite set/type. I tried in the past in this library to create a "cofinite" type and failed to do so so this time I came back much better prepared to do something like this. In `Finite.lean` I define a type to be finite iff the strict subset relation is well-founded. i.e. there is no infinite descending chain of subsets `... ⊂ S₃ ⊂ S₂ ⊂ S₁`. I specifically define it in a way that works well with constructive mathematics, so it is defined basically the same way that `Acc` is defined in the prelude.

My main goal right now is to prove all of the facts that I consider to be basic about finite sets. I'm currently struggling alot with proving that, to the point that I am considering changing the definition.

I am mainly updating the repo because the code has changed alot since August 2025 when I last posted this on github.

