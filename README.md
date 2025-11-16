Hilbert System Proof Generator

This project is a Python script that automatically searches for and generates formal proofs in a specific Hilbert-style axiomatic system for propositional logic.

It demonstrates an approach to solving a problem in computational logic that involves navigating a massive combinatorial search space, implementing a Breadth-First Search (BFS), and applying optimizations to find valid and simple proofs.

The Axiomatic System

The script operates on a logical system defined by three axioms and one rule of inference. The logic uses only two operators: ¬ (NOT) and → (implication).

Axioms:

A1: (A → (B → A))

A2: ((A → (B → C)) → ((A → B) → (A → C)))

A3: ((¬B → ¬A) → (A → B))

Rule of Inference:

Modus Ponens (MP): From P and (P → Q), infer Q.

How It Works

The core of the project is a Breadth-First Search (BFS) algorithm that builds proofs step-by-step.

WFF Basis: The search space for all possible proofs is infinite. To make the search possible, we define a finite set of "building block" formulas (Well-Formed Formulas) called WFF_BASIS. These formulas (e.g., a, b, (¬a), (a → a)) are used to create initial instances of the axioms.

Combinatorial Explosion: The primary challenge is the "combinatorial explosion." The number of possible proofs grows exponentially with the length of the proof and the size of the WFF_BASIS. A basis of 9 formulas searching for 5-step proofs must navigate a search space on the order of trillions of potential paths.

BFS Algorithm:

Length 1: The script first generates all possible "length 1" proofs by substituting formulas from the WFF_BASIS into the axiom templates (A1, A2, A3).

Length N: To find proofs of length N, it takes every proof of length N-1 and tries to add a new line by either:
a) Adding another axiom instance.
b) Applying Modus Ponens to any two previous lines in the proof.

Optimization: The script keeps track of every unique sequence of formulas it has already generated at each length, preventing redundant exploration of identical proof paths.

Final Filtering: The search generates thousands of valid proofs. The script applies a final filtering pass to present only the most useful results:

It filters out any proof that doesn't use Modus Ponens (i.e., just a list of axioms).

It filters out proofs shorter than 3 lines.

Crucially, it calculates a "simplicity score" for every proof and presents only the single simplest proof for each unique theorem found. This is how it finds the elegant 5-step proof for a → a among thousands of other, more complex proofs.

How to Run

No external libraries are required.

Ensure you have Python 3.x installed.

Run the script from your terminal:

python formal_proof_printer.py


The script will print its progress to the console and may take several minutes to run, as the search is computationally intensive.

All output, including progress and the final list of proofs, is written to proof_output.txt.

Project Journey

This project was built iteratively to solve several challenges, which mimics a real-world development process:

Initial Concept: We began by defining the axioms and a simple way to verify a given proof for a → a.

Search Implementation: The goal changed to finding proofs, not just verifying them. This required building the BFS algorithm and defining the WFF_BASIS concept.

Filtering: The initial output was noisy. We added filters to show only proofs of a minimum length (3+) and, most importantly, only proofs that actually used Modus Ponens.

Bug Fixing (The a → a Proof): The famous a → a proof was initially missing! We discovered an optimization was too aggressive (it was pruning duplicate theorems instead of duplicate proof paths), which led to a key bug fix.

Basis Expansion: To find more interesting proofs (like those using A3), we had to carefully expand the WFF_BASIS, balancing the need for variety against the computational cost.

Final Optimization (Simplicity): The output still contained many redundant proofs for the same theorem. The final step was to add a "complexity score" to filter the entire set down to only the single best and simplest proof for each theorem.
