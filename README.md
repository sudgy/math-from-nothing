# math-from-nothing
This is a project that I work on in my spare time where I am developing mathematics in Coq.  There are several things that set this project apart from others:
- The point of the project is for me to prove everything myself from the ground up.  Thus, the project hardly uses any automation or the Coq standard library.  The standard library is used just for the very basic logical definitions and for the Setoid library (although I don't even use any custom Setoids).
- The project includes three axioms: functional extensionality, propositional extensionality, and indefinite description.  These axioms imply predicate extensionality, proof irrelevance, and the strong law of the excluded middle.  This provides a classical and non-constructive way of doing math.
- Other than these three axioms, nothing is ever assumed or admitted.

While you are free to do whatever you wish with the code (as long as it is permitted by the license, of course), I wrote this code for my own use only.  I am not going to be approving any pull requests that people submit, because the point of this project is that I did this all myself.  I am only putting this code online for academic purposes.  If you try to use the code, don't blame me if you get confused at some of the decisions I made.

Some of the interesting things developed in this project are:
- Construction of various number systems, including the natural numbers, integers, rationals, real numbers, cardinals, and ordinals.
- An extensive system of typeclasses for basic algebraic manipulations
- Set theory is developed as a part of a nonconstructive type theory.  This enables the definition of cardinals and ordinals as equivalence classes on types rather than their traditional definition in ZFC.
- Several basic theorems about topology
- Several basic theorems about analysis
- A construction of the geometric algebra of a module over a commutive ring

There are still things that are incomplete.  Some of the larger ones are:
- Linear Algebra has only been used for developing other parts of the project, so it is currently just a collection of several unrelated pieces.  Some of what it was developed for led to a dead end, so there are several unused things in this folder as well.
- I am still wanting to add more to the analysis and topology folders.
- Some of the code is messy and there are a few things that are proven several times because I was too lazy to isolate a theorem and prove it.

One note about coqdoc: While the code is written with coqdoc in mind (you will see several "begin show/hide"s in there), the point of the documentation is for me to be able to find the names of theorems easily.  As such, sections and local context are usually hidden, and all proofs are hidden as well.  This might make it a bit hard to interpret exactly what the theorems are saying to someone who isn't familiar with the codebase.  As this is first and foremost a personal project, I'm going to use coqdoc in the way that helps me the most and not in the way that might help others.
