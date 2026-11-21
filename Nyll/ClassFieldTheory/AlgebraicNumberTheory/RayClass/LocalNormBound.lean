/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalField
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalFieldExtension
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparablePrincipalUnitNorm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups

/-!
# The arithmetic bound for local ray-unit norms

The finite ray-unit groups are the actual principal-unit groups of the
canonical completed local fields. The separable norm theorem therefore gives
the bound in terms of the ramification index of the original prime ideal.
-/

@[expose] public section

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace RayClass

universe u v

/-- Finite ray-unit groups are the standard principal-unit groups for the
distinguished valuation relation on the same completion. -/
theorem localHigherUnitGroup_eq_fieldPrincipalUnits
    (K : Type u) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    let : ValuativeRel (v.adicCompletion K) :=
      ClassFieldTheory.finitePlaceCompletionValuativeRel K v
    ClassFieldTheory.rayLocalHigherUnitGroup v n =
      LocalFieldTheory.fieldPrincipalUnits (v.adicCompletion K) n := by
  intro relation
  let ν : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  have hS : (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring =
      v.adicCompletionIntegers K := by
    ext x
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
      ν).le_one_iff_le_one
  let F := v.adicCompletion K
  let reductionKernel (S : ValuationSubring F) : Subgroup Fˣ :=
    Subgroup.map S.units.subtype
      (((Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S ^ n)).toMonoidHom).comp
        S.toSubmonoid.unitsEquivUnitsType.toMonoidHom).ker)
  have hReduction : ClassFieldTheory.rayLocalHigherUnitGroup v n =
      reductionKernel (v.adicCompletionIntegers K) := rfl
  refine hReduction.trans ((congrArg reductionKernel hS.symm).trans ?_)
  ext x
  let e := (ValuativeRel.valuation (v.adicCompletion K)).integer.toSubmonoid.unitsEquivUnitsType
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e y, ?_, rfl⟩
    change Units.map
      (Ideal.Quotient.mk ((𝓂[v.adicCompletion K] : Ideal 𝒪[v.adicCompletion K]) ^ n)).toMonoidHom
        (e y) = 1 at hy
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := (𝓂[v.adicCompletion K] : Ideal 𝒪[v.adicCompletion K]) ^ n) _ _).mp
      (congrArg Units.val hy)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨e.symm z, ?_, rfl⟩
    change Units.map
      (Ideal.Quotient.mk ((𝓂[v.adicCompletion K] : Ideal 𝒪[v.adicCompletion K]) ^ n)).toMonoidHom
        (e (e.symm z)) = 1
    rw [e.apply_symm_apply]
    apply Units.ext
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := (𝓂[v.adicCompletion K] : Ideal 𝒪[v.adicCompletion K]) ^ n) _ _).mpr hz

/-- A local ray-unit depth strictly greater than `e * (m - 1)` is sufficient
for the norm to land at depth `m`; the extension need not be Galois or tame. -/
theorem localHigherUnitGroup_le_norm_preimage_of_depth
    (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v})
    {n m : ℕ}
    (hn : W.1.asIdeal.ramificationIdx (𝓞 K) * (m - 1) < n) :
    let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    ClassFieldTheory.rayLocalHigherUnitGroup W.1 n ≤
      (ClassFieldTheory.rayLocalHigherUnitGroup v m).comap
      (LocalFieldTheory.normUnits (v.adicCompletion K) (W.1.adicCompletion L)) := by
  intro completionAlgebra
  have hn' : ClassFieldTheory.finitePlaceCompletionRamificationIndex K L v W * (m - 1) < n := by
    rw [ClassFieldTheory.finitePlaceCompletionRamificationIndex_eq]
    exact hn
  let : ValuativeRel (v.adicCompletion K) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel K v
  let : ValuativeRel (W.1.adicCompletion L) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel L W.1
  let : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField K v
  let : IsNonarchimedeanLocalField (W.1.adicCompletion L) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField L W.1
  let : (ValuativeRel.valuation (v.adicCompletion K)).HasExtension
      (ValuativeRel.valuation (W.1.adicCompletion L)) :=
    ClassFieldTheory.finitePlaceCompletion_hasExtension K L v W
  let : FiniteDimensional (v.adicCompletion K) (W.1.adicCompletion L) :=
    finitePlaceAdicCompletionMap_moduleFinite K L v W
  let : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  let : Algebra.IsIntegral (v.adicCompletion K) (W.1.adicCompletion L) :=
    Algebra.IsIntegral.of_finite _ _
  let : Algebra.IsSeparable (v.adicCompletion K) (W.1.adicCompletion L) :=
    Algebra.IsSeparable.of_integral _ _
  rw [localHigherUnitGroup_eq_fieldPrincipalUnits, localHigherUnitGroup_eq_fieldPrincipalUnits]
  exact LocalFieldTheory.fieldPrincipalUnits_le_norm_preimage_of_isSeparable
    (v.adicCompletion K) (W.1.adicCompletion L) hn'

end RayClass
