import ControlTheory.Reachability

/-!
# Changes of state coordinates

We first prove a statement for an intertwining linear map. Coordinate
invariance follows by applying it to a linear equivalence and its inverse.
-/

namespace ControlTheory

variable {𝕜 V U W : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup W] [Module 𝕜 W]

/-- An intertwining map sends reachable states to reachable states. -/
theorem map_reachable_le (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (A' : Module.End 𝕜 W) (B' : U →ₗ[𝕜] W) (F : V →ₗ[𝕜] W)
    (hA : F.comp A = A'.comp F) (hB : F.comp B = B') :
    (reachable A B).map F ≤ reachable A' B' := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply reachable_minimal
  · rintro x ⟨u, rfl⟩
    change F (B u) ∈ reachable A' B'
    have h := congrArg (fun G : U →ₗ[𝕜] W => G u) hB
    change F (B u) = B' u at h
    rw [h]
    exact input_mem_reachable A' B' u
  · intro x hx
    change F (A x) ∈ reachable A' B'
    have h := congrArg (fun G : V →ₗ[𝕜] W => G x) hA
    change F (A x) = A' (F x) at h
    rw [h]
    exact reachable_invariant A' B' (F x) hx

/-- State dynamics in the coordinates `z = e x`. -/
def transportDynamics (e : V ≃ₗ[𝕜] W) (A : Module.End 𝕜 V) : Module.End 𝕜 W :=
  e.toLinearMap.comp (A.comp e.symm.toLinearMap)

/-- The corresponding input map in the new coordinates. -/
def transportInput (e : V ≃ₗ[𝕜] W) (B : U →ₗ[𝕜] V) : U →ₗ[𝕜] W :=
  e.toLinearMap.comp B

@[simp]
theorem transportDynamics_apply (e : V ≃ₗ[𝕜] W) (A : Module.End 𝕜 V) (x : W) :
    transportDynamics e A x = e (A (e.symm x)) := rfl

@[simp]
theorem transportInput_apply (e : V ≃ₗ[𝕜] W) (B : U →ₗ[𝕜] V) (u : U) :
    transportInput e B u = e (B u) := rfl

/-- The reachable subspace transforms by the same coordinate map as the state. -/
theorem reachable_transport (e : V ≃ₗ[𝕜] W) (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    reachable (transportDynamics e A) (transportInput e B) =
      (reachable A B).map e.toLinearMap := by
  have forward : (reachable A B).map e.toLinearMap ≤
      reachable (transportDynamics e A) (transportInput e B) := by
    apply map_reachable_le
    · ext x
      simp
    · rfl
  have backward :
      (reachable (transportDynamics e A) (transportInput e B)).map e.symm.toLinearMap ≤
        reachable A B := by
    apply map_reachable_le
    · ext x
      simp
    · ext u
      simp
  apply le_antisymm _ forward
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  exact backward ⟨y, hy, rfl⟩

theorem controllable_transport_iff (e : V ≃ₗ[𝕜] W)
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    Controllable (transportDynamics e A) (transportInput e B) ↔ Controllable A B := by
  rw [Controllable, reachable_transport, Controllable]
  constructor
  · intro h
    apply top_unique
    intro x _
    have hx : e x ∈ (reachable A B).map e.toLinearMap := by rw [h]; trivial
    rcases hx with ⟨y, hy, he⟩
    have : y = x := e.injective he
    simpa [this] using hy
  · intro h
    rw [h]
    apply top_unique
    intro y _
    exact ⟨e.symm y, Submodule.mem_top, e.apply_symm_apply y⟩

end ControlTheory
