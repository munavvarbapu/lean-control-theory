# Lean Control Theory

A Lean 4 formalization of reachability, the finite Kalman criterion, the
Popov--Belevitch--Hautus eigenvector test, and an explicit Lyapunov decay
estimate for a controlled double integrator.

The starting point is a pair of linear maps

$$A : V \to V, \qquad B : U \to V.$$

The project builds the reachable subspace from the input directions
$A^j B u$, proves its structural properties, and connects several familiar
tests through reusable theorems. A separate real-analysis example proves
exponential decay along closed-loop trajectories.

## Main results

| Result | Lean theorem | Assumptions beyond vector spaces |
| --- | --- | --- |
| Reachable space is the smallest invariant subspace containing the inputs | `reachable_minimal` | None |
| Static feedback preserves the reachable space | `reachable_closedLoop` | None |
| Reachability is preserved by a change of coordinates | `reachable_transport` | Linear equivalence of state spaces |
| Reachability and observability are dual | `controllable_iff_dual_observable` | None |
| The first `dim V` input blocks suffice | `reachable_eq_finiteReachable` | Finite-dimensional state space |
| The finite Kalman map is onto exactly when the pair is controllable | `controllable_iff_surjective_kalmanMap` | Finite-dimensional state space |
| PBH left-eigenvector criterion | `controllable_iff_hautus` | Finite-dimensional state space; algebraically closed field |
| Exponential Lyapunov decay for a double integrator | `Examples.energy_decay` | Real differentiable trajectories satisfying the closed-loop equations |

Names in the table are in the `ControlTheory` namespace.

## The example

For

$$x' = y, \qquad y' = u,$$

choose $u=-2x-3y$. Define

$$E(x,y)=5x^2+2xy+y^2.$$

The formal proofs establish

$$\frac12(x^2+y^2)\le E(x,y)\le6(x^2+y^2),$$

$$\frac{d}{dt}E(x(t),y(t))=-4(x(t)^2+y(t)^2),$$

and, for $s\le t$,

$$E(x(t),y(t))\le E(x(s),y(s))e^{-\frac23(t-s)}.$$

Consequently,

$$x(t)^2+y(t)^2\le12\bigl(x(s)^2+y(s)^2\bigr)e^{-\frac23(t-s)}.$$

There is also an exact two-step discrete control, an algebraically
uncontrollable example, and a two-state feedback calculation with
prescribed eigenvalues.

## Build and check

The project pins Lean **4.24.0** and mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` for reproducible builds.

Install Lean through the [official installation instructions](https://lean-lang.org/install/).
Then run these commands from the project directory:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
python3 scripts/check.py
```

The first command downloads compiled mathlib dependencies. `scripts/check.py`
builds the project, prints the axioms of the main results, and rejects proof
placeholders, project-defined axioms, and unexpected axioms in the checked
results. It requires Python 3. On Windows, use `python` if that is your
Python command.

The GitHub Actions workflow runs the same checks on pushes and pull requests.
See the [local verification report](BUILD_REPORT.md) for the recorded build
and principal theorem axiom checks.

## Source map

| File | Purpose |
| --- | --- |
| `ControlTheory/Reachability.lean` | Definitions, invariance, and minimality |
| `ControlTheory/Feedback.lean` | Static-feedback invariance |
| `ControlTheory/Coordinates.lean` | Intertwining maps and coordinate changes |
| `ControlTheory/Observability.lean` | Invisible states and algebraic duality |
| `ControlTheory/Kalman.lean` | Cayley--Hamilton and the finite criterion |
| `ControlTheory/Synthesis.lean` | Finite input synthesis and discrete trajectories |
| `ControlTheory/Hautus.lean` | The PBH eigenvector criterion |
| `ControlTheory/Examples/DoubleIntegrator.lean` | Controllability, exact control, and feedback eigenvectors |
| `ControlTheory/Examples/HiddenMode.lean` | An inaccessible state direction |
| `ControlTheory/Examples/Lyapunov.lean` | Derivatives and explicit exponential estimates |
| `Verification.lean` | Axiom inspection for the principal results |

Read [the mathematical notes](docs/mathematical-notes.md) for the argument
behind each module and [the review guide](docs/review-guide.md) to check your
understanding of the formalization. The archive also includes a
[publishing guide](docs/publish-on-github.md).

## Scope

`Controllable` is defined algebraically. The project does not silently
identify that definition with a continuous-time endpoint operator.
`dualMap` is the algebraic transpose, not the Hermitian adjoint. The PBH
equivalence is stated over an algebraically closed field, so it includes
complex eigenvalues when the field is complex. Real-to-complex extension
is not formalized here.

The Lyapunov theorem assumes a differentiable solution of the displayed
closed-loop equations. It proves the decay estimate; it does not prove
existence of solutions. PDE controllability, general stabilizability,
and a general pole-assignment theorem are outside the current scope.

See [acknowledgments](ACKNOWLEDGMENTS.md) for dependencies and development
assistance. The source is available under the [MIT license](LICENSE).
