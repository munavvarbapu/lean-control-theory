import ControlTheory.Reachability

/-!
# Static state feedback

The closed-loop state map is `A + B K`, corresponding to the convention
`u = K x + v`. The extra input `v` still acts through `B`.

Feedback preserves the whole reachable subspace. The proof uses its minimal
invariant-subspace property, so it does not require a choice of coordinates
or a finite-dimensional state space.
-/

namespace ControlTheory

variable {𝕜 V U : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]

/-- The convention here is `u = K x + v`. -/
def closedLoop (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (K : V →ₗ[𝕜] U) :
    Module.End 𝕜 V := A + B.comp K

@[simp]
theorem closedLoop_apply (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (K : V →ₗ[𝕜] U) (x : V) : closedLoop A B K x = A x + B (K x) := rfl

theorem reachable_closedLoop_le (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (K : V →ₗ[𝕜] U) : reachable (closedLoop A B K) B ≤ reachable A B := by
  apply reachable_minimal
  · rintro x ⟨u, rfl⟩
    exact input_mem_reachable A B u
  · intro x hx
    exact (reachable A B).add_mem (reachable_invariant A B x hx)
      (input_mem_reachable A B (K x))

/-- Applying the opposite feedback restores the original state map. -/
@[simp]
theorem closedLoop_neg_feedback (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (K : V →ₗ[𝕜] U) : closedLoop (closedLoop A B K) B (-K) = A := by
  ext x
  simp [closedLoop, add_assoc]

/-- Feedback invariance of the algebraic reachable subspace. -/
theorem reachable_closedLoop (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (K : V →ₗ[𝕜] U) : reachable (closedLoop A B K) B = reachable A B := by
  apply le_antisymm (reachable_closedLoop_le A B K)
  simpa using reachable_closedLoop_le (closedLoop A B K) B (-K)

theorem controllable_closedLoop_iff (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (K : V →ₗ[𝕜] U) : Controllable (closedLoop A B K) B ↔ Controllable A B := by
  simp only [Controllable, reachable_closedLoop]

end ControlTheory
