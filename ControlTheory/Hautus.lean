import ControlTheory.Observability
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# The Popov--Belevitch--Hautus eigenvector test

Over an algebraically closed field, an invariant nonzero subspace contains
an eigenvector. Applying this to the unobservable subspace gives the PBH
test for observability, and duality gives the left-eigenvector test for
controllability.

This is a controllability theorem. A stabilizability test would restrict
the spectral region and requires additional definitions and analysis.
-/

namespace ControlTheory

variable {𝕜 V U Y : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup Y] [Module 𝕜 Y]

theorem pow_apply_of_eigen (A : Module.End 𝕜 V) {c : 𝕜} {x : V}
    (hx : A x = c • x) (j : ℕ) : (A ^ j) x = c ^ j • x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

/-- An eigenvector invisible at time zero remains invisible under all iterates. -/
theorem eigen_mem_unobservable (A : Module.End 𝕜 V) (C : V →ₗ[𝕜] Y)
    {c : 𝕜} {x : V} (hA : A x = c • x) (hC : C x = 0) : x ∈ unobservable A C := by
  apply (mem_unobservable_iff A C x).2
  intro j
  rw [pow_apply_of_eigen A hA j, map_smul, hC, smul_zero]

/-- The PBH eigenvector criterion for observability. -/
theorem observable_iff_eigenvector_test [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 V]
    (A : Module.End 𝕜 V) (C : V →ₗ[𝕜] Y) :
    Observable A C ↔ ∀ (c : 𝕜) (x : V), A x = c • x → C x = 0 → x = 0 := by
  constructor
  · intro h c x hA hC
    have hx := eigen_mem_unobservable A C hA hC
    rw [h] at hx
    simpa using hx
  · intro h
    change unobservable A C = ⊥
    by_contra hN
    let N := unobservable A C
    letI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
    let R : Module.End 𝕜 N := A.restrict (unobservable_invariant A C)
    obtain ⟨c, hc⟩ := R.exists_eigenvalue
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hA : A (v : V) = c • (v : V) := congrArg Subtype.val hv.apply_eq_smul
    have hC : C (v : V) = 0 := unobservable_le_ker A C v.property
    have hz : (v : V) = 0 := h c v hA hC
    exact hv.2 (Subtype.ext hz)

/-- The left-eigenvector PBH criterion, with all eigenvalues in the base field. -/
theorem controllable_iff_hautus [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 V]
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    Controllable A B ↔ ∀ (c : 𝕜) (ℓ : Module.Dual 𝕜 V),
      ℓ.comp A = c • ℓ → ℓ.comp B = 0 → ℓ = 0 := by
  rw [controllable_iff_dual_observable, observable_iff_eigenvector_test]
  rfl

end ControlTheory
