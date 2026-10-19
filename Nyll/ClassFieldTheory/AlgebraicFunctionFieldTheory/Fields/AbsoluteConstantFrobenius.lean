/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower

/-!
# Degree one and actual arithmetic constant Frobenius

An automorphism has profinite degree one exactly when it raises every algebraic
constant to the cardinality of the full constant field. Its restriction to
every finite constant stage is therefore the already constructed Frobenius.
-/

noncomputable section

open ClassFormation

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    [IsSepClosed Ω]

/-- A natural-number arithmetic degree is characterized by the corresponding
Frobenius power on all actual algebraic constants. -/
theorem absoluteConstantDegree_eq_nat_iff (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    absoluteConstantDegree k K Ω σ = Multiplicative.ofAdd (n : ZHat) ↔
      ∀ c : separableClosure k Ω, σ (c : Ω) = (c : Ω) ^ (Nat.card k ^ n) := by
  let : Fintype k := Fintype.ofFinite k
  have : IsSepClosed (separableClosure k Ω) := IsSepClosure.sep_closed k
  have : PerfectField (separableClosure k Ω) := Algebra.IsAlgebraic.perfectField k
  let e := LocalClassFieldTheory.residueAbsoluteFrobeniusEquivIn k (separableClosure k Ω)
  let f := FiniteField.frobeniusAlgEquivOfAlgebraic k (separableClosure k Ω)
  let r := absoluteConstantRestriction k K Ω
  have hn : Multiplicative.ofAdd (n : ZHat) = Multiplicative.ofAdd (1 : ZHat) ^ n := by
    apply Multiplicative.ext
    change (n : ZHat) = n • (1 : ZHat)
    rw [nsmul_eq_mul, mul_one]
  have hf : e (Multiplicative.ofAdd (n : ZHat)) = f ^ n := by
    have hf1 : e (Multiplicative.ofAdd (1 : ZHat)) = f :=
      LocalClassFieldTheory.residueAbsoluteFrobenius_one k (separableClosure k Ω)
    rw [hn, map_pow, hf1]
  have hp (c : separableClosure k Ω) :
      ((f ^ n) c : Ω) = (c : Ω) ^ (Nat.card k ^ n) := by
    change ((FiniteField.frobeniusAlgEquivOfAlgebraic k (separableClosure k Ω) ^ n)
      c : Ω) = _
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    change (c : Ω) ^ (Fintype.card k ^ n) = (c : Ω) ^ (Nat.card k ^ n)
    rw [Nat.card_eq_fintype_card]
  have hcoord : absoluteConstantDegree k K Ω σ = Multiplicative.ofAdd (n : ZHat) ↔
      r σ = f ^ n := by
    change e.symm (r σ) = Multiplicative.ofAdd (n : ZHat) ↔ _
    constructor
    · intro h
      exact (e.apply_symm_apply (r σ)).symm.trans ((congrArg e h).trans hf)
    · intro h
      rw [h, ← hf, e.symm_apply_apply]
  refine hcoord.trans ?_
  constructor
  · intro h c
    have hr := AlgEquiv.restrictNormal_commutes (σ.restrictScalars k)
      (separableClosure k Ω) c
    have hc := congrArg (fun τ : separableClosure k Ω ≃ₐ[k] separableClosure k Ω =>
      (τ c : Ω)) h
    exact hr.symm.trans (hc.trans (hp c))
  · intro h
    apply AlgEquiv.ext
    intro c
    apply Subtype.ext
    have hr := AlgEquiv.restrictNormal_commutes (σ.restrictScalars k)
      (separableClosure k Ω) c
    change (r σ c : Ω) = σ (c : Ω) at hr
    exact hr.trans ((h c).trans (hp c).symm)

/-- Arithmetic degree one is characterized by its action on all actual constants. -/
theorem absoluteConstantDegree_eq_frobenius_iff (σ : Ω ≃ₐ[K] Ω) :
    absoluteConstantDegree k K Ω σ = Multiplicative.ofAdd (1 : ZHat) ↔
      ∀ c : separableClosure k Ω, σ (c : Ω) = (c : Ω) ^ Nat.card k := by
  simpa only [Nat.cast_one, pow_one] using
    absoluteConstantDegree_eq_nat_iff k K Ω σ 1

omit [IsSepClosed Ω] in
/-- The action on embedded constants determines restriction to their actual compositum. -/
theorem restrict_constantExtensionFrobenius [Fintype k]
    (C : IntermediateField k Ω) [FiniteDimensional k C]
    (hsc : ∀ y : K, IsSeparable k y → y ∈ (algebraMap k K).range)
    (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ c : C, σ (c : Ω) = (c : Ω) ^ Fintype.card k) :
    AlgEquiv.restrictNormalHom (constantExtensionStage (K := K) C) σ =
      constantExtensionFrobenius (K := K) C hsc := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro c hc
  change (AlgEquiv.restrictNormalHom (constantExtensionStage (K := K) C) σ)
      (constantEmbedding (K := K) C ⟨c, hc⟩) =
    constantExtensionFrobenius (K := K) C hsc (constantEmbedding (K := K) C ⟨c, hc⟩)
  rw [constantExtensionFrobenius_constant]
  apply Subtype.ext
  exact (AlgEquiv.restrictNormal_commutes σ (constantExtensionStage (K := K) C)
    (constantEmbedding (K := K) C ⟨c, hc⟩)).trans (hσ ⟨c, hc⟩)

end FunctionField

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]

/-- A degree-one absolute automorphism restricts to arithmetic Frobenius on every
actual finite extension of the full constants. -/
theorem fullConstantDegreeData_one_restrict (σ : Ω ≃ₐ[K] Ω)
    (hσ : (fullConstantDegreeData k K Ω).degree σ = Multiplicative.ofAdd (1 : ZHat))
    (n : ℕ) [NeZero n] :
    AlgEquiv.restrictNormalHom (fullConstantDegreeStage k K Ω n) σ =
      fullConstantDegreeFrobenius k K Ω n := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  let : Fintype (algebraicClosure k K) := Fintype.ofFinite _
  have hpow := (absoluteConstantDegree_eq_frobenius_iff (algebraicClosure k K) K Ω σ).mp hσ
  let C := (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField
  apply restrict_constantExtensionFrobenius (algebraicClosure k K) K Ω C
    (separableConstants_fullConstants k K) σ
  intro c
  have hsep : (c : Ω) ∈ separableClosure (algebraicClosure k K) Ω :=
    mem_separableClosure_iff.mpr
      ((Algebra.IsSeparable.isSeparable (algebraicClosure k K) c).map
        C.val C.val.injective)
  simpa only [Nat.card_eq_fintype_card] using hpow ⟨c, hsep⟩

/-- A single actual absolute automorphism realizes arithmetic Frobenius at every
finite constant stage simultaneously. -/
theorem exists_fullConstantFrobenius_lift :
    ∃ σ : Ω ≃ₐ[K] Ω,
      (fullConstantDegreeData k K Ω).degree σ = Multiplicative.ofAdd (1 : ZHat) ∧
      ∀ (n : ℕ) [NeZero n],
        AlgEquiv.restrictNormalHom (fullConstantDegreeStage k K Ω n) σ =
          fullConstantDegreeFrobenius k K Ω n := by
  obtain ⟨σ, hσ⟩ := (fullConstantDegreeData k K Ω).degree_surjective
    (Multiplicative.ofAdd (1 : ZHat))
  exact ⟨σ, hσ, fun n _ => fullConstantDegreeData_one_restrict k K Ω σ hσ n⟩

end FunctionField
