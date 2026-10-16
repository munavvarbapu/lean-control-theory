import ControlTheory.Reachability

/-!
# A mode that the input cannot reach

The first coordinate evolves independently. In continuous-time notation
it would satisfy `x₁' = x₁`, while the input acts only on the second
coordinate. We compute the reachable space exactly and show that this
pair is not algebraically controllable.
-/

namespace ControlTheory.Examples

variable {𝕜 : Type*} [Field 𝕜]

def hiddenMode : Module.End 𝕜 (𝕜 × 𝕜) where
  toFun x := (x.1, -x.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' c x := by ext <;> simp

def secondCoordinateInput : 𝕜 →ₗ[𝕜] (𝕜 × 𝕜) where
  toFun u := (0, u)
  map_add' u v := by ext <;> simp
  map_smul' c u := by ext <;> simp

theorem reachable_hiddenMode :
    reachable (hiddenMode : Module.End 𝕜 (𝕜 × 𝕜)) secondCoordinateInput =
      LinearMap.ker (LinearMap.fst 𝕜 𝕜 𝕜) := by
  apply le_antisymm
  · apply reachable_minimal
    · rintro x ⟨u, rfl⟩
      rfl
    · intro x hx
      exact hx
  · rintro ⟨x, y⟩ hxy
    change x = 0 at hxy
    subst x
    exact input_mem_reachable (hiddenMode : Module.End 𝕜 (𝕜 × 𝕜)) secondCoordinateInput y

theorem hiddenMode_not_controllable :
    ¬Controllable (hiddenMode : Module.End 𝕜 (𝕜 × 𝕜)) secondCoordinateInput := by
  intro h
  have heq := reachable_hiddenMode (𝕜 := 𝕜)
  rw [h] at heq
  have hx : (1, 0) ∈ LinearMap.ker (LinearMap.fst 𝕜 𝕜 𝕜) := by
    rw [← heq]
    trivial
  exact one_ne_zero (show (1 : 𝕜) = 0 from hx)

end ControlTheory.Examples
