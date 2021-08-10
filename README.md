# math-from-nothing
This is a project that I work on in my spare time where I am developing mathematics in Coq.  There are several things that set this project apart from others:
- The project hardly uses the Coq standard library.  The point of this project is for me to prove everything myself, so I use the standard library as little as possible.  I use it for just the very basic logical definitions and for the Setoid library (although I don't even use any custom Setoids).
- The project includes three axioms: functional extensionality, propositional extensionality, and indefinite description.  These axioms imply predicate extensionality, proof irrelevance, and the strong law of the excluded middle.  This provides a non-constructive and classical way of doing math.
- Other than these three axioms, nothing is ever assumed.  While there are a few incomplete proofs currently in the repository that have admitted parts, this is an artifact of the fact that I haven't finished writing those proofs (if they are even possible at all).  These proofs are never used and I am hoping to replace those at some point.

While you are free to do whatever you wish with the code (as long as it is permitted by the license, of course), I wrote this code for my own use only.  I am not going to be approving any pull requests that people submit, because the point of this project is that I did this all myself.  I am only putting this code online for academic purposes.  If you try to use the code, don't blame me if you get confused at some of the decisions I made.

Some of the interesting things developed in this project are:
- Construction of various number systems, including the natural numbers, integers, rationals, real numbers, cardinals, and ordinals.
- An extensive system of typeclasses for basic algebraic manipulations
- Set theory is developed as a part of a nonconstructive type theory.  This enables the definition of cardinals and ordinals as equivalence classes on types rather than their traditional definition in ZFC.  While I have suspicions that this isn't quite as powerful as ZFC (I haven't found a way to define aleph-omega, for example), it is more than sufficient for the rest of the mathematics in the project.
- Several basic theorems about topology.
- Several basic theorems about analysis.

There are still things that are incomplete.  Some of the larger ones are:
- Ordinal exponentiation.  Given my foundation, ordinal exponention is much harder to use than it normally is.  I did manage to define it, but I didn't go much further.  I could pull this off if I wanted to, but I got tired after everything else that I had done.
- Many of the things in the Linear Algebra or Geometric Algebra folders.  I've had several different ideas floating around for the best way to define geometric algebra in here, and I haven't finished any of them yet, so there are several different half-finished constructions.  This will hopefully get cleaned up at some point.
- I am still wanting to add more to the analysis and topology folders.
- Some of the code is messy and there are a few things that are proven several times because I was too lazy to isolate a theorem and prove it.
