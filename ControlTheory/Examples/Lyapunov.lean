import ControlTheory.Examples.DoubleIntegrator
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# An explicit exponential stabilization estimate

Use the feedback `u = -2 x - 3 y` for the continuous-time double integrator.
The closed-loop equations are `x' = y`, `y' = -2 x - 3 y`.

The energy `5 x² + 2 x y + y²` has derivative `-4 (x² + y²)`.
We prove an exponential energy bound and then a bound for the squared
Euclidean state length. These statements apply to any differentiable
trajectory satisfying the displayed equations; existence of that trajectory
is not part of this module's assumptions or conclusions.
-/

namespace ControlTheory.Examples

noncomputable def energy (x y : ℝ) : ℝ := 5 * x ^ 2 + 2 * (x * y) + y ^ 2

theorem energy_lower (x y : ℝ) : (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) ≤ energy x y := by
  dsimp [energy]
  nlinarith [sq_nonneg (y + 2 * x), sq_nonneg x]

theorem energy_upper (x y : ℝ) : energy x y ≤ 6 * (x ^ 2 + y ^ 2) := by
  dsimp [energy]
  nlinarith [sq_nonneg (x - y), sq_nonneg y]

theorem energy_nonneg (x y : ℝ) : 0 ≤ energy x y := by
  have h := energy_lower x y
  nlinarith [sq_nonneg x, sq_nonneg y]

theorem energy_eq_zero_iff (x y : ℝ) : energy x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hl := energy_lower x y
    have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨(sq_eq_zero_iff).mp hx, (sq_eq_zero_iff).mp hy⟩
  · rintro ⟨rfl, rfl⟩
    simp [energy]

/-- The exact quadratic-form identity underlying the Lyapunov argument. -/
theorem energy_dissipation_identity (x y : ℝ) :
    (10 * x + 2 * y) * y + (2 * x + 2 * y) * (-2 * x - 3 * y) =
      -4 * (x ^ 2 + y ^ 2) := by ring

theorem energy_hasDerivAt {x y : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (y t) t) (hy : HasDerivAt y (-2 * x t - 3 * y t) t) :
    HasDerivAt (fun s => energy (x s) (y s)) (-4 * (x t ^ 2 + y t ^ 2)) t := by
  convert (((hx.pow 2).const_mul 5).add ((hx.mul hy).const_mul 2)).add (hy.pow 2) using 1
  dsimp [energy]
  ring

noncomputable def weightedEnergy (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  energy (x t) (y t) * Real.exp ((2 / 3 : ℝ) * t)

theorem weightedEnergy_hasDerivAt {x y : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (y t) t) (hy : HasDerivAt y (-2 * x t - 3 * y t) t) :
    HasDerivAt (weightedEnergy x y)
      (Real.exp ((2 / 3 : ℝ) * t) *
        (-4 * (x t ^ 2 + y t ^ 2) + (2 / 3 : ℝ) * energy (x t) (y t))) t := by
  convert (energy_hasDerivAt hx hy).mul
    (((hasDerivAt_id t).const_mul (2 / 3 : ℝ)).exp) using 1
  dsimp [weightedEnergy]
  ring

theorem weightedEnergy_derivative_nonpos (x y t : ℝ) :
    Real.exp ((2 / 3 : ℝ) * t) *
      (-4 * (x ^ 2 + y ^ 2) + (2 / 3 : ℝ) * energy x y) ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
  have h := energy_upper x y
  linarith

/-- A kernel-checked exponential Lyapunov estimate for every closed-loop trajectory. -/
theorem energy_decay {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (y t) t)
    (hy : ∀ t, HasDerivAt y (-2 * x t - 3 * y t) t)
    {s t : ℝ} (hst : s ≤ t) :
    energy (x t) (y t) ≤
      energy (x s) (y s) * Real.exp (-(2 / 3 : ℝ) * (t - s)) := by
  have hmono : Antitone (weightedEnergy x y) :=
    antitone_of_hasDerivAt_nonpos
      (fun r => weightedEnergy_hasDerivAt (hx r) (hy r))
      (fun r => weightedEnergy_derivative_nonpos (x r) (y r) r)
  have h := mul_le_mul_of_nonneg_right (hmono hst)
    (le_of_lt (Real.exp_pos (-(2 / 3 : ℝ) * t)))
  have hcancel : Real.exp ((2 / 3 : ℝ) * t) * Real.exp (-(2 / 3 : ℝ) * t) = 1 := by
    rw [← Real.exp_add]
    have hz : (2 / 3 : ℝ) * t + -(2 / 3 : ℝ) * t = 0 := by ring
    rw [hz, Real.exp_zero]
  have hcombine : Real.exp ((2 / 3 : ℝ) * s) * Real.exp (-(2 / 3 : ℝ) * t) =
      Real.exp (-(2 / 3 : ℝ) * (t - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [weightedEnergy, mul_assoc, hcancel, mul_one, hcombine] using h

/-- Squared Euclidean decay with explicit constants, without a numerical solver. -/
theorem state_square_decay {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (y t) t)
    (hy : ∀ t, HasDerivAt y (-2 * x t - 3 * y t) t)
    {s t : ℝ} (hst : s ≤ t) :
    x t ^ 2 + y t ^ 2 ≤
      12 * (x s ^ 2 + y s ^ 2) * Real.exp (-(2 / 3 : ℝ) * (t - s)) := by
  have hlow := energy_lower (x t) (y t)
  have hdecay := energy_decay hx hy hst
  have hu := mul_le_mul_of_nonneg_right (energy_upper (x s) (y s))
    (le_of_lt (Real.exp_pos (-(2 / 3 : ℝ) * (t - s))))
  nlinarith

end ControlTheory.Examples
