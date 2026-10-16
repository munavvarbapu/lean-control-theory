# Reviewing and explaining the project

Start by opening the project folder in VS Code with the Lean 4 extension.
Move the cursor through a proof to see its hypotheses and current goal.
The following questions are useful checks before presenting the work.

1. **What is actually defined as controllability?**
   `Controllable A B` means `reachable A B = ⊤`. It is the algebraic
   condition. Do not claim that an arbitrary PDE endpoint operator is
   already part of this definition.

2. **Why use a supremum of submodules?**
   The supremum is the smallest subspace containing all the block images.
   A plain union of images need not be closed under addition. The key
   proof rule is `iSup_le`: to bound the supremum, bound every block.

3. **Where is Cayley--Hamilton used?**
   In `reachable_eq_finiteReachable`, the identity
   `A.pow_eq_aeval_mod_charpoly j` replaces a power by a polynomial
   remainder. `Polynomial.aeval_eq_sum_range'` expands that remainder.
   The remaining terms belong to the first `dim V` blocks.

4. **Why does feedback preserve controllability?**
   Explain the two subspace inclusions. Both `A x` and `B (K x)` stay in
   the original reachable space. Then apply the same argument with `-K`.
   This is stronger than proving a matrix-rank equality for one example.

5. **What does the star in the duality argument mean?**
   It means composition on the algebraic dual. In particular,
   `(A.dualMap ℓ) x = ℓ (A x)`. Over the complex numbers it is not the
   conjugate transpose induced by a Hilbert-space inner product.

6. **Why does the PBH theorem need an algebraically closed field?**
   Its converse chooses an eigenvector of the restriction of `A` to a
   nonzero unobservable subspace. A real rotation can have no real
   eigenvectors. The field assumption is mathematical, not a tactic
   convenience.

7. **What is assumed in the Lyapunov theorem?**
   Two real functions have the displayed derivatives at every real time.
   The result bounds any such trajectory. It does not construct the
   solution or prove a general stabilization theorem.

8. **What do the axiom reports establish?**
   `Verification.lean` asks Lean which axioms the principal theorem
   constants depend on. The checker allows the usual `propext`,
   `Classical.choice`, and `Quot.sound`. A successful build and an axiom
   check establish the exact formal statements and their proof dependencies.

For a useful first modification, derive a different feedback pair in the
double-integrator example and find a positive quadratic energy for it.
For a larger extension, connect the algebraic condition to a
continuous-time endpoint map with explicitly stated hypotheses.
