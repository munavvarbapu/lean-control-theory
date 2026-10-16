import ControlTheory.Feedback
import ControlTheory.Synthesis

/-!
# A controlled double integrator

The state is `(position, velocity)`, the input acts on velocity, and the
drift is `(velocity, 0)`. We verify controllability directly, give an exact
two-step discrete control, and exhibit the closed-loop eigenvectors.
-/

namespace ControlTheory.Examples

variable {𝕜 : Type*} [Field 𝕜]

def doubleIntegrator : Module.End 𝕜 (𝕜 × 𝕜) where
  toFun x := (x.2, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

def velocityInput : 𝕜 →ₗ[𝕜] (𝕜 × 𝕜) where
  toFun u := (0, u)
  map_add' u v := by ext <;> simp
  map_smul' c u := by ext <;> simp

def positionVelocityFeedback (p q : 𝕜) : (𝕜 × 𝕜) →ₗ[𝕜] 𝕜 :=
  (-p) • LinearMap.fst 𝕜 𝕜 𝕜 + (-q) • LinearMap.snd 𝕜 𝕜 𝕜

@[simp]
theorem doubleIntegrator_apply (x : 𝕜 × 𝕜) :
    doubleIntegrator x = (x.2, 0) := rfl

@[simp]
theorem velocityInput_apply (u : 𝕜) : velocityInput u = (0, u) := rfl

@[simp]
theorem positionVelocityFeedback_apply (p q : 𝕜) (x : 𝕜 × 𝕜) :
    positionVelocityFeedback p q x = -p * x.1 - q * x.2 := by
  simp [positionVelocityFeedback, sub_eq_add_neg]

theorem doubleIntegrator_controllable :
    Controllable (doubleIntegrator : Module.End 𝕜 (𝕜 × 𝕜)) velocityInput := by
  let A : Module.End 𝕜 (𝕜 × 𝕜) := doubleIntegrator
  let B : 𝕜 →ₗ[𝕜] (𝕜 × 𝕜) := velocityInput
  change reachable A B = ⊤
  apply top_unique
  rintro ⟨x, y⟩ _
  have hx := krylov_mem_reachable A B 1 x
  have hy := input_mem_reachable A B y
  simpa [A, B] using (reachable A B).add_mem hx hy

theorem closedLoop_doubleIntegrator (p q : 𝕜) (x : 𝕜 × 𝕜) :
    closedLoop doubleIntegrator velocityInput (positionVelocityFeedback p q) x =
      (x.2, -p * x.1 - q * x.2) := by
  ext <;> simp [closedLoop]

/-- A concrete chronological control supported at steps zero and one. -/
def twoStepControl (position velocity : 𝕜) (j : ℕ) : 𝕜 :=
  if j = 0 then position else if j = 1 then velocity else 0

theorem twoStepControl_reaches (position velocity : 𝕜) :
    discreteState doubleIntegrator velocityInput (twoStepControl position velocity) 2 =
      (position, velocity) := by
  simp [discreteState, twoStepControl]

/-- Feedback `p = a*b`, `q = a+b` places an eigenvalue at `-a`. -/
theorem assigned_eigenvector_left (a b : 𝕜) :
    closedLoop doubleIntegrator velocityInput (positionVelocityFeedback (a * b) (a + b))
      (1, -a) = (-a) • (1, -a) := by
  rw [closedLoop_doubleIntegrator]
  apply Prod.ext
  · change -a = (-a) * 1
    ring
  · change -(a * b) * 1 - (a + b) * (-a) = (-a) * (-a)
    ring

/-- The same feedback also places an eigenvalue at `-b`. -/
theorem assigned_eigenvector_right (a b : 𝕜) :
    closedLoop doubleIntegrator velocityInput (positionVelocityFeedback (a * b) (a + b))
      (1, -b) = (-b) • (1, -b) := by
  rw [closedLoop_doubleIntegrator]
  apply Prod.ext
  · change -b = (-b) * 1
    ring
  · change -(a * b) * 1 - (a + b) * (-b) = (-b) * (-b)
    ring

theorem closedLoop_doubleIntegrator_controllable (p q : 𝕜) :
    Controllable (closedLoop doubleIntegrator velocityInput (positionVelocityFeedback p q))
      velocityInput := by
  exact (controllable_closedLoop_iff _ _ _).2 doubleIntegrator_controllable

end ControlTheory.Examples
