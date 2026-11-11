/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReconstruction
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants

/-!
# One actual constant-field map for all reconstructed local factors

Over finite constants, a function belongs to the actual full constant field
exactly when it is zero or a root of unity. A multiplicative field equivalence
therefore restricts to one multiplicative equivalence of the actual full
constant fields. This argument does not assume additivity of the recovered map.

For the reconstruction through the original Artin kernels, this single
constant map agrees with the reconstructed local maps at every place, by the
proved identity on original principal ideles. Independent local constant maps
and their coherence are not extra inputs.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve LocalClassFieldTheory

namespace FunctionField.RayClass

section FullConstants

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K]

/-- The actual full constants are zero and the finite-order nonzero functions. -/
theorem mem_fullConstants_iff_zero_or_pow (x : K) :
    x ∈ algebraicClosure k K ↔ x = 0 ∨ ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  constructor
  · intro hx
    by_cases hxzero : x = 0
    · exact Or.inl hxzero
    · right
      have : Finite (algebraicClosure k K) :=
        FieldTheory.finite_algebraicClosure_of_finite_base k K
      let c : algebraicClosure k K := ⟨x, hx⟩
      have hc : c ≠ 0 := fun h => hxzero (congrArg Subtype.val h)
      let u : (algebraicClosure k K)ˣ := Units.mk0 c hc
      have hu : u ^ Nat.card (algebraicClosure k K)ˣ = 1 := pow_card_eq_one'
      have hpow : (u : algebraicClosure k K) ^ Nat.card (algebraicClosure k K)ˣ = 1 :=
        congrArg Units.val hu
      have hK := congrArg (algebraMap (algebraicClosure k K) K) hpow
      rw [map_pow, map_one] at hK
      exact ⟨Nat.card (algebraicClosure k K)ˣ, Nat.card_pos, hK⟩
  · rintro (rfl | ⟨n, hn, hx⟩)
    · exact mem_algebraicClosure_iff.mpr (isIntegral_zero (R := k)).isAlgebraic
    · apply mem_algebraicClosure_iff.mpr
      apply IsIntegral.isAlgebraic
      apply IsIntegral.of_pow hn
      rw [hx]
      exact isIntegral_one

end FullConstants

section ConstantEquivalence

variable {k₁ K₁ k₂ K₂ : Type*}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁] [Algebra.EssFiniteType k₁ K₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂] [Algebra.EssFiniteType k₂ K₂]

/-- Any actual multiplicative field equivalence preserves the full constants. -/
theorem mulEquiv_mem_fullConstants_iff (ψ : K₁ ≃* K₂) (x : K₁) :
    ψ x ∈ algebraicClosure k₂ K₂ ↔ x ∈ algebraicClosure k₁ K₁ := by
  rw [mem_fullConstants_iff_zero_or_pow, mem_fullConstants_iff_zero_or_pow]
  constructor
  · rintro (hzero | ⟨n, hn, hpow⟩)
    · exact Or.inl (ψ.injective (hzero.trans (map_zero ψ).symm))
    · refine Or.inr ⟨n, hn, ψ.injective ?_⟩
      rw [map_pow, hpow, map_one]
  · rintro (rfl | ⟨n, hn, hpow⟩)
    · exact Or.inl (map_zero ψ)
    · refine Or.inr ⟨n, hn, ?_⟩
      rw [← map_pow, hpow, map_one]

/-- Restriction to the actual full constant fields, without assuming addition. -/
def fullConstantMulEquiv (ψ : K₁ ≃* K₂) :
    algebraicClosure k₁ K₁ ≃* algebraicClosure k₂ K₂ where
  toFun x := ⟨ψ (x : K₁),
    (mulEquiv_mem_fullConstants_iff (k₁ := k₁) (k₂ := k₂) ψ (x : K₁)).mpr x.property⟩
  invFun y := ⟨ψ.symm (y : K₂), by
    apply (mulEquiv_mem_fullConstants_iff (k₁ := k₁) (k₂ := k₂)
      ψ (ψ.symm (y : K₂))).mp
    rw [ψ.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (ψ.symm_apply_apply (x : K₁))
  right_inv y := Subtype.ext (ψ.apply_symm_apply (y : K₂))
  map_mul' x y := Subtype.ext (map_mul ψ (x : K₁) (y : K₁))

/-- The constant map is the original map on the original included function. -/
theorem fullConstantMulEquiv_coe (ψ : K₁ ≃* K₂) (c : algebraicClosure k₁ K₁) :
    (fullConstantMulEquiv (k₁ := k₁) (k₂ := k₂) ψ c : K₂) = ψ (c : K₁) := rfl

/-- The full constant field sizes agree as a consequence of multiplicative reconstruction. -/
theorem fullConstants_card_eq_of_mulEquiv (ψ : K₁ ≃* K₂) :
    Nat.card (algebraicClosure k₁ K₁) = Nat.card (algebraicClosure k₂ K₂) :=
  Nat.card_congr (fullConstantMulEquiv (k₁ := k₁) (k₂ := k₂) ψ).toEquiv

end ConstantEquivalence

section OriginalLocalConstants

variable {k₁ K₁ k₂ K₂ : Type*}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]

local instance originalConstantSourceFiniteType : Algebra.EssFiniteType k₁ K₁ :=
  FunctionField.essFiniteType k₁ K₁

local instance originalConstantTargetFiniteType : Algebra.EssFiniteType k₂ K₂ :=
  FunctionField.essFiniteType k₂ K₂

variable (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
    (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (γ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
      (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
    (hclosure : ∀ v g,
      g ∈ (localRayAbsoluteArtin m₁ v).range.topologicalClosure ↔
        γ g ∈ (localRayAbsoluteArtin m₂ (e v)).range.topologicalClosure)
    (hdegree : ∀ g, rayAbelianDegree m₂ (γ g) = rayAbelianDegree m₁ g)
    (hboundary₁ : ∀ v : Place k₁ K₁, ∃ w : Place k₁ K₁, w ≠ v ∧ m₁ w ≠ 0)
    (hboundary₂ : ∀ v : Place k₂ K₂, ∃ w : Place k₂ K₂, w ≠ v ∧ m₂ w ≠ 0)
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)

local notation "ψ" => reconstructedRayFunction m₁ m₂ e γ hclosure hdegree
  hboundary₁ hboundary₂ hm₁ hm₂

/-- The reconstructed global units restrict to the one full constant map. -/
theorem reconstructedRayFunctionUnits_constants (c : (algebraicClosure k₁ K₁)ˣ) :
    reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree hboundary₁ hboundary₂ hm₁ hm₂
        (Units.map (algebraMap (algebraicClosure k₁ K₁) K₁).toMonoidHom c) =
      Units.map (algebraMap (algebraicClosure k₂ K₂) K₂).toMonoidHom
        (Units.map (fullConstantMulEquiv (k₁ := k₁) (k₂ := k₂) ψ).toMonoidHom c) := by
  apply Units.ext
  change (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
    hboundary₁ hboundary₂ hm₁ hm₂
      (Units.map (algebraMap (algebraicClosure k₁ K₁) K₁).toMonoidHom c) : K₂) =
    (fullConstantMulEquiv (k₁ := k₁) (k₂ := k₂) ψ (c : algebraicClosure k₁ K₁) : K₂)
  rw [fullConstantMulEquiv_coe]
  exact (reconstructedRayFunction_apply_units m₁ m₂ e γ hclosure hdegree
    hboundary₁ hboundary₂ hm₁ hm₂
      (Units.map (algebraMap (algebraicClosure k₁ K₁) K₁).toMonoidHom c)).symm

/-- Every reconstructed local factor uses the same actual full constant map. -/
theorem localRayEquivOfClosure_constants
    (c : (algebraicClosure k₁ K₁)ˣ) (v : Place k₁ K₁) :
    localRayEquivOfClosure m₁ v m₂ (e v) γ (hclosure v) hdegree
        (hboundary₁ v) (hboundary₂ (e v))
        (QuotientGroup.mk' (localHigherUnitGroup v (m₁ v))
          (Units.map (algebraMap K₁ v.adicCompletion).toMonoidHom
            (Units.map (algebraMap (algebraicClosure k₁ K₁) K₁).toMonoidHom c))) =
      QuotientGroup.mk' (localHigherUnitGroup (e v) (m₂ (e v)))
        (Units.map (algebraMap K₂ (e v).adicCompletion).toMonoidHom
          (Units.map (algebraMap (algebraicClosure k₂ K₂) K₂).toMonoidHom
            (Units.map (fullConstantMulEquiv (k₁ := k₁) (k₂ := k₂) ψ).toMonoidHom c))) := by
  have hlocal := reconstructedRayFunctionUnits_local m₁ m₂ e γ hclosure hdegree
    hboundary₁ hboundary₂ hm₁ hm₂
      (Units.map (algebraMap (algebraicClosure k₁ K₁) K₁).toMonoidHom c) v
  exact hlocal.symm.trans (congrArg
    (fun y : K₂ˣ => QuotientGroup.mk' (localHigherUnitGroup (e v) (m₂ (e v)))
      (Units.map (algebraMap K₂ (e v).adicCompletion).toMonoidHom y))
    (reconstructedRayFunctionUnits_constants m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂ hm₁ hm₂ c))

end OriginalLocalConstants

end FunctionField.RayClass
