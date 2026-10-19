/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.KummerSplit
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitKummerUnramified
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SupportedLocalNorms
import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
import Nyll.AlgebraicCurves.Places.Ramification.NcardAlgHomCompEqPreimageEqRamificationIndex

/-!
# Detecting S-unit powers at a finite set of places

When S-ideles represent all idele classes, an S-unit which is a power in every
completion at S is a power in the field. The actual simple Kummer extension
is split at S and unramified elsewhere. Actual local norm preimages give
surjectivity of its idele-class norm, and the proved first norm inequality
forces its degree to be one.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.SUnits

open KummerTheory
open AlgebraicCurves.Places.Proofs
open Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.AlgebraicCurve

variable {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- Local power detection for S-units, using the actual S-idele presentation
and the actual cyclic norm inequality. -/
theorem mem_nthPowers_of_local_powers (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (S : Finset (Place k K))
    (hS : Function.Surjective (IdeleGroup.sIdeleClass S))
    (b : units k K S)
    (hlocal : ∀ v : Place k K, v ∈ S → ∃ x : v.adicCompletionˣ,
      (x : v.adicCompletion) ^ (n : ℕ) = algebraMap K v.adicCompletion (b.val : K)) :
    b.val ∈ unitNthPowersSubgroup K n := by
  classical
  let Ω := SeparableClosure K
  let akΩ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  have hkKΩ : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let M := chosenSimpleKummerExtension K n hn b.val
  have hMfinite : FiniteDimensional K M :=
    chosenSimpleKummerExtension_finiteDimensional K n hn b.val
  have hMabelian : IsAbelianGalois K M :=
    chosenSimpleKummerExtension_isAbelianGalois K n hn hmu b.val
  have hMcyclic : IsCyclic Gal(M/K) := chosenSimpleKummerExtension_isCyclic K n hn hmu b.val
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K M
  let aRM : Algebra (RatFunc k) M := presentation.val
  have hkRM : IsScalarTower k (RatFunc k) M := presentation.property.1
  have hMfunction : FunctionField k M := presentation.property.2
  have hMcurve : IsCurveOver k M := isCurveOver k M
  let β : Mˣ := chosenSimpleKummerRootUnit K n hn b.val
  have hβ : (β : M) ^ (n : ℕ) = algebraMap K M (b.val : K) :=
    congrArg Units.val (chosenSimpleKummerRootUnit_pow K n hn b.val)
  have hgen : Algebra.adjoin K {(β : M)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := K) (β : M)),
      chosenSimpleKummerExtension_adjoin_root_eq_top]
    rfl
  have hAway (w : Place k M) (hw : w.restrict K ∉ S) : w.ramificationIndex K = 1 := by
    let E := kummerExtension (Ω := Ω) n S
    have hEfinite : FiniteDimensional K E := kummerExtension_finiteDimensional n hn hmu S
    have hEgalois : IsGalois K E := kummerRadicalExtension_isGalois n (units k K S)
    have hME : M ≤ E := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro z hz
      have hzβ : z = chosenSimpleKummerRoot K n hn b.val := Set.mem_singleton_iff.mp hz
      subst z
      exact IntermediateField.subset_adjoin K
        (kummerRootSet (K := K) (Omega := Ω) n (units k K S))
        ⟨b, chosenSimpleKummerRoot_pow K n hn b.val⟩
    let aME : Algebra M E := (IntermediateField.inclusion hME).toRingHom.toAlgebra
    have hKME : IsScalarTower K M E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hkME : IsScalarTower k M E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hMEfinite : FiniteDimensional M E := FiniteDimensional.right K M E
    have hMEsep : Algebra.IsSeparable M E := Algebra.isSeparable_tower_top_of_isSeparable K M E
    obtain ⟨W, hW⟩ := Place.exists_restrict_eq (M := E) w
    have hnot : W.restrict K ∉ S := by
      rw [← SpecialisationCount.restrict_restrict (F := K) (F' := M), hW]
      exact hw
    have he : W.ramificationIndex K = 1 :=
      kummerExtension_ramificationIndex_eq_one n hn hmu S W hnot
    have hmul := SpecialisationCount.ramificationIndex_tower (F := K) (F' := M) W
    rw [he, hW] at hmul
    exact Nat.eq_one_of_dvd_one ⟨W.ramificationIndex M,
      hmul.trans (Nat.mul_comm _ _)⟩
  have hSplit (v : Place k K) (hv : v ∈ S) (w : Place k M) (hw : w.restrict K = v) :
      Function.Surjective (IdeleGroup.localNormOver v w hw) := by
    subst v
    obtain ⟨x, hx⟩ := hlocal (w.restrict K) hv
    exact IdeleGroup.localNorm_surjective_of_kummer_root w n hmu b.val β hβ hgen x hx
  have hdegree : Module.finrank K M = 1 :=
    finrank_eq_one_of_supported_local_norms (k := k) (K := K) (M := M) S hS hAway hSplit
  obtain ⟨x, hx⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdegree).2 (β : M)
  have hxne : x ≠ 0 := by
    intro hzero
    apply β.ne_zero
    rw [← hx, hzero, map_zero]
  refine ⟨Units.mk0 x hxne, ?_⟩
  apply Units.ext
  apply (algebraMap K M).injective
  change algebraMap K M (x ^ (n : ℕ)) = algebraMap K M (b.val : K)
  rw [map_pow, hx, hβ]

end FunctionField.SUnits
