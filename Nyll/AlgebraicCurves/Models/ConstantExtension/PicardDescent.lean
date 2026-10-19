/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.DivisorDescent
import Nyll.AlgebraicCurves.Models.ConstantExtension.FixedDivisor
import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardAction
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.PrincipalPrincipalPullbackConstants
import Nyll.GaloisCohomology.Cyclic.PeriodicNorm

/-!
# The arithmetic Picard group as actual Frobenius invariants

Pullback along the actual model embedding is injective by descent of principal
divisors. Its image consists exactly of the classes fixed by geometric Frobenius,
using a fixed representative and actual divisor descent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurves.FunctionFields.Proofs
open LinearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic
open AlgebraicCurves.Divisors.Proofs
open Divisor_existsUnique_pullbackConstants_eq_of_forall_smul_eq.P2mSchmidtDescent2

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k Ω F₀ F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)

local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- Picard pullback along the actual original-field embedding of the two models. -/
def constantPicardBaseChange : Pic k F₀ →+ Pic Ω F :=
  let _ : Algebra F₀ F := M₀.constantModelAlgebra M e
  let _ : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
  let _ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
  let _ : Algebra.IsIntegral F₀ F := (M₀.constantModel_isIntegral_and_adjoin M e he).1
  Pic.baseChange k Ω F₀ F

omit [Fintype k] [IsAlgClosed Ω] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] in
/-- Actual Picard pullback loses no divisor class. -/
theorem constantPicardBaseChange_injective [PerfectField k] (hC : ConstantsAreBase k F₀) :
    Function.Injective (M₀.constantPicardBaseChange M e he) := by
  let baseAlg : Algebra F₀ F := M₀.constantModelAlgebra M e
  let constAlg : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
  have towerΩ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have tower₀ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
  obtain ⟨hInt, hgen⟩ := M₀.constantModel_isIntegral_and_adjoin M e he
  change Function.Injective (Pic.baseChange k Ω F₀ F)
  apply (injective_iff_map_eq_zero (Pic.baseChange k Ω F₀ F)).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  apply (QuotientAddGroup.eq_zero_iff D).mpr
  apply Divisor.isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension hgen hC
  exact (QuotientAddGroup.eq_zero_iff (Divisor.pullbackConstants Ω F D)).mp hx

omit [IsAlgClosed Ω] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] in
private theorem constantPicardBaseChange_fixed (hC : ConstantsAreBase k F₀) (x : Pic k F₀) :
    φ • M₀.constantPicardBaseChange M e he x = M₀.constantPicardBaseChange M e he x := by
  let baseAlg : Algebra F₀ F := M₀.constantModelAlgebra M e
  let constAlg : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
  have towerΩ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have tower₀ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
  obtain ⟨hInt, hgen⟩ := M₀.constantModel_isIntegral_and_adjoin M e he
  have hconst : ∀ a : F₀, IsAlgebraic k a → a ∈ (algebraMap k F₀).range :=
    fun a ha => LdCab.mem_range_of_isAlgebraic hC a ha
  have hram (w : Place Ω F) : (w.forgetConstants (K := k)).ramificationIndex F₀ = 1 :=
    Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgen hconst w
  have hfix (a : F₀) : φ • algebraMap F₀ F a = algebraMap F₀ F a :=
    M.constantSemilinearAction_baseEmbedding M₀.toBase e he
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (M₀.ffEquiv a)
  have hplace (w : Place Ω F) :
      Place.restrictConstants F₀ (K := k) (φ⁻¹ • w) = Place.restrictConstants F₀ (K := k) w := by
    apply Place.ext
    exact over_smul (v := Place.restrictConstants F₀ (K := k) w) (W := w) rfl φ⁻¹
      (fun a => by rw [inv_smul_eq_iff, hfix])
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  change H1Gm.mk (φ • Divisor.pullbackConstants Ω F D) = H1Gm.mk (Divisor.pullbackConstants Ω F D)
  apply congrArg H1Gm.mk
  ext w
  rw [SemilinearAut.divisor_smul_apply, Divisor.pullbackConstants_apply,
    Divisor.pullbackConstants_apply, hram, hram, hplace]

/-- Arithmetic divisor classes are exactly the actual geometric Frobenius-fixed classes. -/
theorem exists_constantPicardBaseChange_preimage_iff (hC : ConstantsAreBase k F₀)
    (x : Pic Ω F) :
    (∃ y : Pic k F₀, M₀.constantPicardBaseChange M e he y = x) ↔ φ • x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact M₀.constantPicardBaseChange_fixed M e he hC y
  · intro hx
    obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
    have hD : (φ • D - D).IsPrincipal := by
      have hzero : H1Gm.mk (φ • D - D) = 0 := sub_eq_zero.mpr hx
      exact (QuotientAddGroup.eq_zero_iff (φ • D - D)).mp hzero
    obtain ⟨E, hDE, -, hE⟩ := M.exists_constantFrobenius_fixed_divisor M₀.toBase e he D hD
    let baseAlg : Algebra F₀ F := M₀.constantModelAlgebra M e
    let constAlg : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
    have towerΩ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have tower₀ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
    have hInt : Algebra.IsIntegral F₀ F := (M₀.constantModel_isIntegral_and_adjoin M e he).1
    obtain ⟨E₀, hE₀, -⟩ := M₀.existsUnique_constantFrobenius_divisor_descent M e he hC E hE
    refine ⟨H1Gm.mk E₀, ?_⟩
    change H1Gm.mk (Divisor.pullbackConstants Ω F E₀) = H1Gm.mk D
    rw [hE₀]
    have hzero : H1Gm.mk (D - E) = 0 := (QuotientAddGroup.eq_zero_iff (D - E)).mpr hDE
    exact (sub_eq_zero.mp hzero).symm

/-- The actual arithmetic Picard group is isomorphic to geometric Frobenius invariants. -/
def constantPicardFixedEquiv (hC : ConstantsAreBase k F₀) :
    Pic k F₀ ≃+ CyclicAction.periodicSubgroup (A := Pic Ω F) φ 1 := by
  let f : Pic k F₀ →+ CyclicAction.periodicSubgroup (A := Pic Ω F) φ 1 :=
    (M₀.constantPicardBaseChange M e he).codRestrict _ (fun x => by
      change φ ^ 1 • M₀.constantPicardBaseChange M e he x = _
      rw [pow_one]
      exact M₀.constantPicardBaseChange_fixed M e he hC x)
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    exact M₀.constantPicardBaseChange_injective M e he hC (congrArg Subtype.val hxy)
  · intro x
    have hxpow : φ ^ 1 • (x : Pic Ω F) = x := x.property
    have hx : φ • (x : Pic Ω F) = x := by simpa only [pow_one] using hxpow
    obtain ⟨y, hy⟩ := (M₀.exists_constantPicardBaseChange_preimage_iff M e he hC x).mpr hx
    exact ⟨y, Subtype.ext hy⟩

omit [Fintype k] [IsAlgClosed Ω] in
/-- The Picard comparison preserves the actual divisor degree. -/
theorem degree_constantPicardBaseChange [PerfectField k]
    (hC : ConstantsAreBase k F₀) (x : Pic k F₀) :
    H1Gm.degree Ω F (M₀.constantPicardBaseChange M e he x) = H1Gm.degree k F₀ x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  exact M₀.degree_pullback_constantModel M e he hC D

end AlgebraicCurve.CurveModel
