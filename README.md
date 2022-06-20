# mini Agda TySy
The purpose of this project is to formalize a basic functional language with its type system and to prove the well known safety theorem.

The project is divided in multiple files:
- `basic.agda` contains common basic definitions.
- `list.agda` contains all about lists, both functions that deals with lists and proofs of useful propositions.
- `nat.agda` contains all about natural numbers.
- `type-system.agda` is the main file. It contains the language formalization and all the steps that brings to the proof of the safety theorem.
- `examples.agda` contains examples of type judgments or evaluation judgments.

I suggest to start the reading from `type-system.agda` and then to switch to other files as needed.
