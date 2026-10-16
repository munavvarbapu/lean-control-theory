import ControlTheory.Reachability

/-!
# A finite Kalman criterion

Cayley--Hamilton reduces the infinite family of input blocks to the first
`dim V` blocks. The proof expands the remainder of `X^j` modulo the
characteristic polynomial. No rank condition is assumed as a hypothesis.
-/

namespace ControlTheory

open Polynomial Module

variable {𝕜 V U : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]

/-- The span of the first `n` input blocks, including none when `n = 0`. -/
def finiteReachable (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (n : ℕ) : Submodule 𝕜 V :=
  ⨆ j : Fin n, LinearMap.range (krylovBlock A B j.val)

theorem finiteReachable_le (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) (n : ℕ) :
    finiteReachable A B n ≤ reachable A B := by
  refine iSup_le fun j => ?_
  rintro x ⟨u, rfl⟩
  exact krylov_mem_reachable A B j.val u

theorem krylov_mem_finiteReachable (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    {j n : ℕ} (hj : j < n) (u : U) :
    (A ^ j) (B u) ∈ finiteReachable A B n :=
  Submodule.mem_iSup_of_mem ⟨j, hj⟩ ⟨u, rfl⟩

theorem finiteReachable_mono (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    {m n : ℕ} (hmn : m ≤ n) : finiteReachable A B m ≤ finiteReachable A B n := by
  refine iSup_le fun j => ?_
  rintro x ⟨u, rfl⟩
  exact krylov_mem_finiteReachable A B (lt_of_lt_of_le j.isLt hmn) u

/-- Cayley--Hamilton gives the finite Kalman span, also in dimension zero. -/
theorem reachable_eq_finiteReachable [FiniteDimensional 𝕜 V]
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    reachable A B = finiteReachable A B (finrank 𝕜 V) := by
  classical
  apply le_antisymm _ (finiteReachable_le A B _)
  cases subsingleton_or_nontrivial V with
  | inl hV =>
    letI := hV
    intro x _
    have : x = 0 := Subsingleton.elim _ _
    rw [this]
    exact (finiteReachable A B (finrank 𝕜 V)).zero_mem
  | inr hV =>
    letI := hV
    apply (reachable_le_iff A B _).2
    intro j u
    have hchar : A.charpoly ≠ 1 := by
      intro h
      have hd := congrArg Polynomial.natDegree h
      rw [A.charpoly_natDegree, Polynomial.natDegree_one] at hd
      exact (ne_of_gt (Module.finrank_pos (R := 𝕜) (M := V))) hd
    have hdegree : (X ^ j %ₘ A.charpoly).natDegree < finrank 𝕜 V := by
      simpa only [A.charpoly_natDegree] using
        Polynomial.natDegree_modByMonic_lt (X ^ j) A.charpoly_monic hchar
    rw [A.pow_eq_aeval_mod_charpoly j, Polynomial.aeval_eq_sum_range' hdegree]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    apply Submodule.sum_mem
    intro i hi
    exact (finiteReachable A B (finrank 𝕜 V)).smul_mem _
      (krylov_mem_finiteReachable A B (Finset.mem_range.mp hi) u)

/-- A finite criterion for algebraic controllability. -/
theorem controllable_iff_kalman [FiniteDimensional 𝕜 V]
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    Controllable A B ↔ finiteReachable A B (finrank 𝕜 V) = ⊤ := by
  rw [Controllable, reachable_eq_finiteReachable]

/-- Once `dim V` blocks have been included, adding blocks changes nothing. -/
theorem finiteReachable_eq_of_finrank_le [FiniteDimensional 𝕜 V]
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) {n : ℕ} (hn : finrank 𝕜 V ≤ n) :
    finiteReachable A B n = reachable A B := by
  apply le_antisymm (finiteReachable_le A B n)
  rw [reachable_eq_finiteReachable]
  exact finiteReachable_mono A B hn

end ControlTheory
