import ControlTheory.Reachability

/-!
# Observability and algebraic duality

An unobservable state is killed by `C A^j` for every `j`. The annihilator
of the reachable subspace of `(A, B)` is exactly the unobservable subspace
of the dual pair `(A*, B*)`. Here `*` means algebraic transpose; it is not
a complex inner-product adjoint.
-/

namespace ControlTheory

variable {𝕜 V U Y : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup Y] [Module 𝕜 Y]

/-- States whose outputs vanish under every state-map iterate. -/
def unobservable (A : Module.End 𝕜 V) (C : V →ₗ[𝕜] Y) : Submodule 𝕜 V :=
  ⨅ j : ℕ, LinearMap.ker (C.comp (A ^ j))

def Observable (A : Module.End 𝕜 V) (C : V →ₗ[𝕜] Y) : Prop :=
  unobservable A C = ⊥

theorem mem_unobservable_iff (A : Module.End 𝕜 V) (C : V →ₗ[𝕜] Y) (x : V) :
    x ∈ unobservable A C ↔ ∀ j : ℕ, C ((A ^ j) x) = 0 := by
  simp only [unobservable, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]

theorem unobservable_le_ker (A : Module.End 𝕜 V) (C : V →ₗ[𝕜] Y) :
    unobservable A C ≤ LinearMap.ker C := by
  intro x hx
  simpa using (mem_unobservable_iff A C x).1 hx 0

theorem unobservable_invariant (A : Module.End 𝕜 V) (C : V →ₗ[𝕜] Y) :
    IsInvariant A (unobservable A C) := by
  intro x hx
  apply (mem_unobservable_iff A C (A x)).2
  intro j
  simpa [pow_succ, Module.End.mul_apply] using (mem_unobservable_iff A C x).1 hx (j + 1)

/-- The unobservable subspace is the largest invariant subspace inside `ker C`. -/
theorem unobservable_maximal (A : Module.End 𝕜 V) (C : V →ₗ[𝕜] Y)
    (S : Submodule 𝕜 V) (hC : S ≤ LinearMap.ker C) (hA : IsInvariant A S) :
    S ≤ unobservable A C := by
  intro x hx
  apply (mem_unobservable_iff A C x).2
  intro j
  apply hC
  induction j with
  | zero => simpa using hx
  | succ j ih => simpa [pow_succ', Module.End.mul_apply] using hA _ ih

/-- Transposition commutes with taking powers of one endomorphism. -/
theorem dual_pow_apply (A : Module.End 𝕜 V) (j : ℕ) (ℓ : Module.Dual 𝕜 V) (x : V) :
    ((A.dualMap ^ j) ℓ) x = ℓ ((A ^ j) x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.dualMap_apply, ih]
    rw [pow_succ, Module.End.mul_apply]

/-- Reachability/observability duality, stated at the subspace level. -/
theorem annihilator_reachable_eq_unobservable
    (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    (reachable A B).dualAnnihilator = unobservable A.dualMap B.dualMap := by
  ext ℓ
  rw [mem_annihilator_reachable_iff, mem_unobservable_iff]
  constructor
  · intro h j
    ext u
    simpa only [LinearMap.dualMap_apply, dual_pow_apply, LinearMap.zero_apply] using h j u
  · intro h j u
    have hu := congrArg (fun f : Module.Dual 𝕜 U => f u) (h j)
    simpa only [LinearMap.dualMap_apply, dual_pow_apply, LinearMap.zero_apply] using hu

/-- Algebraic controllability is equivalent to observability of the dual pair. -/
theorem controllable_iff_dual_observable (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V) :
    Controllable A B ↔ Observable A.dualMap B.dualMap := by
  rw [Controllable, Observable, ← annihilator_reachable_eq_unobservable]
  constructor
  · intro h
    rw [h, Submodule.dualAnnihilator_top]
  · intro h
    apply Subspace.dualAnnihilator_inj.mp
    exact h.trans Submodule.dualAnnihilator_top.symm

end ControlTheory
