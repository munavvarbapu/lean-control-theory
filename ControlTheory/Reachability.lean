import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic

/-!
# The algebraic reachable subspace

For a linear system with state map `A` and input map `B`, the reachable
subspace is the span of the vectors `A^j (B u)`. This definition is algebraic:
no time domain, regularity of a control, or differential equation is hidden
in it. Later modules relate it to finite tests and discrete trajectories.
-/

namespace ControlTheory

open Module

variable {𝕜 V U : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]

/-- The `j`th input block of the Kalman family. -/
def krylovBlock (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (j : ℕ) : U →ₗ[𝕜] V :=
  (A ^ j).comp B

/-- The smallest subspace containing all input directions and their iterates. -/
def reachable (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) : Submodule 𝕜 V :=
  ⨆ j : ℕ, LinearMap.range (krylovBlock A B j)

/-- Algebraic controllability. Analytic control problems need a separate bridge. -/
def Controllable (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) : Prop :=
  reachable A B = ⊤

/-- An explicit form of invariance, convenient for proof by induction. -/
def IsInvariant (A : Module.End 𝕜 V) (S : Submodule 𝕜 V) : Prop :=
  ∀ x ∈ S, A x ∈ S

@[simp]
theorem krylovBlock_apply (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (j : ℕ) (u : U) :
    krylovBlock A B j u = (A ^ j) (B u) := rfl

theorem krylov_mem_reachable (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (j : ℕ) (u : U) :
    (A ^ j) (B u) ∈ reachable A B :=
  Submodule.mem_iSup_of_mem j ⟨u, rfl⟩

theorem input_mem_reachable (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (u : U) :
    B u ∈ reachable A B := by
  simpa using krylov_mem_reachable A B 0 u

theorem reachable_le_iff (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (S : Submodule 𝕜 V) :
    reachable A B ≤ S ↔ ∀ j u, (A ^ j) (B u) ∈ S := by
  constructor
  · intro h j u
    exact h (krylov_mem_reachable A B j u)
  · intro h
    refine iSup_le fun j => ?_
    rintro x ⟨u, rfl⟩
    exact h j u

/-- The reachable subspace is invariant under the state map. -/
theorem reachable_invariant (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    IsInvariant A (reachable A B) := by
  have h : reachable A B ≤ (reachable A B).comap A := by
    apply (reachable_le_iff A B _).2
    intro j u
    change A ((A ^ j) (B u)) ∈ reachable A B
    simpa [pow_succ', Module.End.mul_apply] using krylov_mem_reachable A B (j + 1) u
  exact fun x hx => h hx

/-- Every invariant subspace containing the inputs contains all reachable states. -/
theorem reachable_minimal (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (S : Submodule 𝕜 V) (hB : LinearMap.range B ≤ S) (hA : IsInvariant A S) :
    reachable A B ≤ S := by
  apply (reachable_le_iff A B S).2
  intro j u
  induction j with
  | zero => simpa using hB (show B u ∈ LinearMap.range B from ⟨u, rfl⟩)
  | succ j ih =>
    simpa [pow_succ', Module.End.mul_apply] using hA _ ih

theorem reachable_le_iff_input_and_invariant
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (S : Submodule 𝕜 V)
    (hA : IsInvariant A S) :
    reachable A B ≤ S ↔ LinearMap.range B ≤ S := by
  constructor
  · intro h x hx
    rcases hx with ⟨u, rfl⟩
    exact h (input_mem_reachable A B u)
  · intro hB
    exact reachable_minimal A B S hB hA

/-- No actuation gives the zero reachable subspace. -/
@[simp]
theorem reachable_zero_input (A : Module.End 𝕜 V) :
    reachable A (0 : U →ₗ[𝕜] V) = ⊥ := by
  apply le_antisymm _ bot_le
  apply (reachable_le_iff _ _ _).2
  intro j u
  simp

/-- Surjective actuation already supplies every state direction. -/
theorem controllable_of_surjective_input (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (hB : Function.Surjective B) : Controllable A B := by
  apply top_unique
  intro x _
  obtain ⟨u, rfl⟩ := hB x
  exact input_mem_reachable A B u

/-- A covector annihilates the reachable space exactly when it kills every block. -/
theorem mem_annihilator_reachable_iff
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (ℓ : Module.Dual 𝕜 V) :
    ℓ ∈ (reachable A B).dualAnnihilator ↔ ∀ j u, ℓ ((A ^ j) (B u)) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  change (reachable A B ≤ LinearMap.ker ℓ) ↔ _
  exact reachable_le_iff A B (LinearMap.ker ℓ)

end ControlTheory
