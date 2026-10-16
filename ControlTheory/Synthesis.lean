import ControlTheory.Kalman

/-!
# Finite input synthesis

The Kalman map sends a finite list of input vectors to the sum of the
corresponding input blocks. Its range is exactly the finite reachable
subspace, which turns the finite Kalman criterion into a surjectivity test.

For a discrete-time system, the chronological endpoint uses these same
blocks in reversed order. We separately verify that every recursively
defined discrete trajectory stays in the algebraic reachable subspace.
-/

namespace ControlTheory

variable {𝕜 V U : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]

/-- Synthesis in block order: `B u₀ + A B u₁ + ...`. -/
def kalmanMap (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (n : ℕ) :
    (Fin n → U) →ₗ[𝕜] V where
  toFun u := ∑ j : Fin n, (A ^ j.val) (B (u j))
  map_add' u v := by simp [map_add, Finset.sum_add_distrib]
  map_smul' c u := by simp [map_smul, Finset.smul_sum]

@[simp]
theorem kalmanMap_apply (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (n : ℕ) (u : Fin n → U) :
    kalmanMap A B n u = ∑ j : Fin n, (A ^ j.val) (B (u j)) := rfl

/-- Finite block synthesis has exactly the finite reachable subspace as its range. -/
theorem range_kalmanMap (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (n : ℕ) :
    LinearMap.range (kalmanMap A B n) = finiteReachable A B n := by
  classical
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    rw [kalmanMap_apply]
    apply Submodule.sum_mem
    intro j _
    exact krylov_mem_finiteReachable A B j.isLt (u j)
  · refine iSup_le fun j => ?_
    rintro x ⟨u, rfl⟩
    refine ⟨Pi.single j u, ?_⟩
    simp [kalmanMap, Pi.single_apply, apply_ite]

/-- A finite-dimensional system is controllable exactly when its Kalman map is onto. -/
theorem controllable_iff_surjective_kalmanMap [FiniteDimensional 𝕜 V]
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    Controllable A B ↔ Function.Surjective (kalmanMap A B (Module.finrank 𝕜 V)) := by
  rw [controllable_iff_kalman, ← range_kalmanMap, LinearMap.range_eq_top]

/-- Discrete-time trajectory from the zero state with a chronological input sequence. -/
def discreteState (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (u : ℕ → U) : ℕ → V
  | 0 => 0
  | j + 1 => A (discreteState A B u j) + B (u j)

@[simp]
theorem discreteState_zero (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (u : ℕ → U) :
    discreteState A B u 0 = 0 := rfl

@[simp]
theorem discreteState_succ (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (u : ℕ → U) (j : ℕ) :
    discreteState A B u (j + 1) = A (discreteState A B u j) + B (u j) := rfl

theorem discreteState_mem_reachable (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (u : ℕ → U) (j : ℕ) : discreteState A B u j ∈ reachable A B := by
  induction j with
  | zero => exact (reachable A B).zero_mem
  | succ j ih =>
    exact (reachable A B).add_mem (reachable_invariant A B _ ih)
      (input_mem_reachable A B (u j))

end ControlTheory
