/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReciprocity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayLocalArtin
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteConstantDegree

/-!
# Integer valuations from the arithmetic degree of actual local Artin symbols

The one-place absolute Artin symbol has arithmetic degree equal to the
normalized integer order times the residue degree over the full constants.
The integer order is uniquely determined by this value. At every finite
constant stage the same original symbol is the corresponding power of the
actual constant Frobenius. Thus a local uniformizer has arithmetic degree
the place degree, with the sign already fixed by local reciprocity.

The final comparison applies to any representative of a coordinate of the
actual principal reciprocity kernel, and recovers its original place order.
-/

@[expose] public section

universe u v

noncomputable section

open AlgebraicCurve ClassFormation LocalClassFieldTheory

namespace FunctionField

private theorem zHat_intCast_injective : Function.Injective (Int.cast : ℤ → ZHat) := by
  intro a b hab
  apply sub_eq_zero.mp
  have hz : ((a - b : ℤ) : ZHat) = 0 := by rw [Int.cast_sub, hab, sub_self]
  let n := (a - b).natAbs + 1
  have hn : 0 < n := Nat.succ_pos _
  have hr : ((a - b : ℤ) : ZMod n) = 0 := by
    have h := congrArg (zHatReduction n hn) hz
    simpa only [zHatReduction_intCast, map_zero] using h
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    ((ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) n).mp hr)
  simpa only [Int.natAbs_natCast] using Nat.lt_succ_self (a - b).natAbs

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

omit [HasPrincipalDivisors k K] in
private theorem fullConstant_placeDegree_ne_zero (v : Place k K) :
    (v.extendConstants (algebraicClosure k K)).deg ≠ 0 := by
  have : IsCurveOver (algebraicClosure k K) K := isCurveOver_fullConstants k K
  have : Module.Finite (algebraicClosure k K)
      (v.extendConstants (algebraicClosure k K)).ResidueField :=
    IsCurveOver.finiteResidue _
  exact Module.finrank_pos.ne'

/-- The original absolute symbol records the normalized local order, with
the actual residue-degree factor over the full constant field. -/
theorem absoluteAbelianDegree_placeIdele (v : Place k K) (x : v.adicCompletionˣ) :
    absoluteAbelianDegree k K
        (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))) =
      Multiplicative.ofAdd
        (((IdeleGroup.localOrder v x).toAdd *
          (v.extendConstants (algebraicClosure k K)).deg : ℤ) : ZHat) := by
  rw [absoluteAbelianDegree_artin, IdeleClassGroup.normalizedDegree_placeIdele]

/-- The arithmetic degree determines the local integer valuation uniquely;
there is no choice of a profinite unit multiplying that valuation. -/
theorem absoluteAbelianDegree_placeIdele_eq_iff
    (v : Place k K) (x : v.adicCompletionˣ) (n : ℤ) :
    absoluteAbelianDegree k K
        (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))) =
        Multiplicative.ofAdd
          ((n * (v.extendConstants (algebraicClosure k K)).deg : ℤ) : ZHat) ↔
      (IdeleGroup.localOrder v x).toAdd = n := by
  rw [absoluteAbelianDegree_placeIdele]
  constructor
  · intro h
    exact mul_right_cancel₀
      (Int.natCast_ne_zero.mpr (fullConstant_placeDegree_ne_zero v))
      (zHat_intCast_injective (congrArg Multiplicative.toAdd h))
  · intro h
    rw [h]

/-- In particular a uniformizer has the arithmetic degree of its residue
field, corresponding to `Fr_κ(v) = Fr_constants ^ deg(v)`. -/
theorem absoluteAbelianDegree_placeIdele_uniformizer
    (v : Place k K) (x : v.adicCompletionˣ)
    (hx : (IdeleGroup.localOrder v x).toAdd = 1) :
    absoluteAbelianDegree k K
        (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))) =
      Multiplicative.ofAdd ((v.extendConstants (algebraicClosure k K)).deg : ZHat) := by
  rw [absoluteAbelianDegree_placeIdele, hx, one_mul, Int.cast_natCast]

/-- The arithmetic kernel on the original local field is exactly its
ordinary unit subgroup. -/
theorem absoluteAbelianDegree_placeIdele_eq_one_iff
    (v : Place k K) (x : v.adicCompletionˣ) :
    absoluteAbelianDegree k K
        (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))) = 1 ↔
      x ∈ RayClass.localHigherUnitGroup v 0 := by
  have h := absoluteAbelianDegree_placeIdele_eq_iff v x 0
  simpa only [zero_mul, Int.cast_zero, ofAdd_zero,
    RayClass.localHigherUnitGroup_zero, IdeleGroup.localOrder_eq_zero_iff] using h

/-- If the stated base is the full constant field, the factor is the
original residue degree over that base. -/
theorem absoluteAbelianDegree_placeIdele_of_fullConstants
    (hconstants : algebraicClosure k K = ⊥)
    (v : Place k K) (x : v.adicCompletionˣ) :
    absoluteAbelianDegree k K
        (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))) =
      Multiplicative.ofAdd (((IdeleGroup.localOrder v x).toAdd * v.deg : ℤ) : ZHat) := by
  have hdegree : v.deg = (v.extendConstants (algebraicClosure k K)).deg := by
    have hc : Module.finrank k (algebraicClosure k K) = 1 := by
      rw [hconstants, IntermediateField.finrank_bot]
    have h : v.deg = Module.finrank k (algebraicClosure k K) *
        (v.extendConstants (algebraicClosure k K)).deg :=
      Place.deg_forgetConstants (K := k)
      (v.extendConstants (algebraicClosure k K))
    simpa only [hc, one_mul] using h
  rw [absoluteAbelianDegree_placeIdele, hdegree]

/-- Every finite restriction of the original one-place absolute symbol is
the actual local reciprocity value in the original decomposition subgroup. -/
theorem absoluteArtin_placeIdele_restriction_decomposition
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    ∀ (w : Place k E) (x : (w.restrict K).adicCompletionˣ),
      absoluteAbelianRestriction K E
          (absoluteArtin k K
            (IdeleClassGroup.mk (IdeleGroup.placeIdele (w.restrict K) x))) =
        (localDecompositionArtin (K := K) w x).val := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ w x
  rw [absoluteArtin_restriction]
  exact (localArtin_eq_abelianFiniteArtin_placeIdele k K E w x).symm

/-- Restriction of the same original absolute symbol to each actual finite
constant field is its arithmetic Frobenius to the normalized local degree. -/
theorem absoluteArtin_constantRestriction_placeIdele (n : ℕ) [NeZero n]
    (v : Place k K) (x : v.adicCompletionˣ) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    let _ : IsCyclic Gal((fullConstantDegreeStage k K (SeparableClosure K) n)/K) :=
      isCyclic_fullConstantDegreeStage k K (SeparableClosure K) n
    let _ : IsAbelianGalois K (fullConstantDegreeStage k K (SeparableClosure K) n) :=
      IsAbelianGalois.of_isCyclic K (fullConstantDegreeStage k K (SeparableClosure K) n)
    absoluteAbelianRestriction K
        (fullConstantDegreeStage k K (SeparableClosure K) n).toIntermediateField
        (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))) =
      fullConstantDegreeFrobenius k K (SeparableClosure K) n ^
        ((IdeleGroup.localOrder v x).toAdd *
          (v.extendConstants (algebraicClosure k K)).deg) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ hcyc hab
  rw [absoluteArtin_restriction]
  exact (DFunLike.congr_fun (abelianFiniteArtin_fullConstant k K n)
    (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))).trans
      (IdeleClassGroup.constantFrobeniusCharacter_placeIdele k K (SeparableClosure K) n v x)

namespace RayClass

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
/-- Equal local ray coordinates have exactly the same original integer
order, even when the boundary quotient retains residue units. -/
theorem localOrder_eq_of_rayLocalFactor_eq (m : Modulus k K) (v : Place k K)
    (x y : v.adicCompletionˣ)
    (h : QuotientGroup.mk' (localHigherUnitGroup v (m v)) x =
      QuotientGroup.mk' (localHigherUnitGroup v (m v)) y) :
    (IdeleGroup.localOrder v x).toAdd = (IdeleGroup.localOrder v y).toAdd := by
  have hu : x / y ∈ localHigherUnitGroup v (m v) := QuotientGroup.eq_iff_div_mem.mp h
  have hz := (IdeleGroup.localOrder_eq_zero_iff v (x / y)).mpr
    (localHigherUnitGroup_le_localUnits v (m v) hu)
  rw [map_div, toAdd_div] at hz
  exact sub_eq_zero.mp hz

/-- Reading a coordinate of the actual principal reciprocity kernel by its
original local Artin symbol recovers the valuation of the original function.
The local representative may be chosen arbitrarily in its ray class. -/
theorem principalKernel_localArtin_degree_eq_iff
    (m : Modulus k K) (hm : m ≠ 0)
    (u : (restrictedProductAbsoluteArtin m).ker) (v : Place k K)
    (x : v.adicCompletionˣ)
    (hx : QuotientGroup.mk' (localHigherUnitGroup v (m v)) x =
      (u : RayRestrictedProduct m) v) (n : ℤ) :
    absoluteAbelianDegree k K
        (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))) =
        Multiplicative.ofAdd
          ((n * (v.extendConstants (algebraicClosure k K)).deg : ℤ) : ZHat) ↔
      v.ord ((principalRestrictedArtinKernelEquiv m hm).symm u : K) = n := by
  let f := (principalRestrictedArtinKernelEquiv m hm).symm u
  have hf : QuotientGroup.mk' (localHigherUnitGroup v (m v))
      (Units.map (algebraMap K v.adicCompletion) f) = (u : RayRestrictedProduct m) v := by
    have h := congrArg (fun a : (restrictedProductAbsoluteArtin m).ker =>
      (a : RayRestrictedProduct m) v)
      ((principalRestrictedArtinKernelEquiv m hm).apply_symm_apply u)
    exact (principalRestrictedArtinKernelEquiv_apply m hm f v).symm.trans h
  have ho := localOrder_eq_of_rayLocalFactor_eq m v x
    (Units.map (algebraMap K v.adicCompletion) f) (hx.trans hf.symm)
  rw [IdeleGroup.localOrder_algebraMap] at ho
  exact (absoluteAbelianDegree_placeIdele_eq_iff v x n).trans
    ⟨fun h => ho.symm.trans h, fun h => ho.trans h⟩

end RayClass

end FunctionField
