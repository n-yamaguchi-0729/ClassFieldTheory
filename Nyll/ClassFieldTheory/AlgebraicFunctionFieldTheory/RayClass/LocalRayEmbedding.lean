/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReciprocity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiniteQuotients

/-!
# Local ray factors inside the original global reciprocity target

A single local ray factor embeds in the ray class group whenever the modulus
has a positive component at another place. If a one-place family were
principal, the product formula would force its remaining order to vanish.
The congruence at the other boundary then forces the function itself to be one.

Consequently the same local factor embeds through the original absolute
Artin map. Both the embedding and its representatives retain the existing
completion and reciprocity maps.
-/

@[expose] public section

universe u v

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

open scoped Classical in
/-- Insert one original local ray factor into the actual restricted product. -/
def localRayToRestrictedProduct (m : Modulus k K) (v : Place k K) :
    RayLocalFactor m v →* RayRestrictedProduct m :=
  RestrictedProduct.mulSingleMonoidHom
    (fun w : Place k K => (⊥ : Subgroup (RayLocalFactor m w))) v

/-- The supporting coordinate recovers the original local class. -/
theorem localRayToRestrictedProduct_same (m : Modulus k K) (v : Place k K)
    (x : RayLocalFactor m v) : localRayToRestrictedProduct m v x v = x := by
  classical
  exact RestrictedProduct.mulSingle_eq_same
    (fun w : Place k K => (⊥ : Subgroup (RayLocalFactor m w))) v x

/-- Every other coordinate is the identity class. -/
theorem localRayToRestrictedProduct_of_ne (m : Modulus k K) (v w : Place k K)
    (x : RayLocalFactor m v) (hw : w ≠ v) :
    localRayToRestrictedProduct m v x w = 1 := by
  classical
  exact RestrictedProduct.mulSingle_eq_of_ne
    (fun z : Place k K => (⊥ : Subgroup (RayLocalFactor m z))) x hw

/-- A representative is sent to its original one-place idele class. -/
theorem localRayToRestrictedProduct_mk (m : Modulus k K) (v : Place k K)
    (x : v.adicCompletionˣ) :
    localRayToRestrictedProduct m v
        (QuotientGroup.mk' (localHigherUnitGroup v (m v)) x) =
      ideleToRayRestrictedProduct m (IdeleGroup.placeIdele v x) := by
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst w
    calc
      localRayToRestrictedProduct m v
          (QuotientGroup.mk' (localHigherUnitGroup v (m v)) x) v =
        QuotientGroup.mk' (localHigherUnitGroup v (m v)) x :=
          localRayToRestrictedProduct_same m v _
      _ = ideleToRayRestrictedProduct m (IdeleGroup.placeIdele v x) v := by
        change QuotientGroup.mk' (localHigherUnitGroup v (m v)) x =
          QuotientGroup.mk' (localHigherUnitGroup v (m v))
            (IdeleGroup.component v (IdeleGroup.placeIdele v x))
        rw [IdeleGroup.component_placeIdele_same]
  · calc
      localRayToRestrictedProduct m v
          (QuotientGroup.mk' (localHigherUnitGroup v (m v)) x) w = 1 :=
        localRayToRestrictedProduct_of_ne m v w _ hw
      _ = ideleToRayRestrictedProduct m (IdeleGroup.placeIdele v x) w := by
        change 1 = QuotientGroup.mk' (localHigherUnitGroup w (m w))
          (IdeleGroup.component w (IdeleGroup.placeIdele v x))
        rw [IdeleGroup.component_placeIdele_of_ne v w x hw, map_one]

variable [HasPrincipalDivisors k K]

/-- The original ray-class map restricted to one actual local factor. -/
def localRayToRayClass (m : Modulus k K) (v : Place k K) :
    RayLocalFactor m v →* RayClassGroup m :=
  (restrictedProductToRayClass m).comp (localRayToRestrictedProduct m v)

variable [∀ v : Place k K, v.FiniteResidue]

private theorem principal_eq_one_of_away_congruence
    (m : Modulus k K) (v : Place k K)
    (hm : ∃ w : Place k K, w ≠ v ∧ m w ≠ 0)
    (x : Kˣ)
    (hx : ∀ w : Place k K, w ≠ v →
      Units.map (algebraMap K w.adicCompletion) x ∈ localHigherUnitGroup w (m w)) :
    x = 1 := by
  classical
  have horder (w : Place k K) (hw : w ≠ v) : w.ord (x : K) = 0 := by
    have hlocal := localHigherUnitGroup_le_localUnits w (m w) (hx w hw)
    exact (IdeleGroup.localOrder_algebraMap w x).symm.trans
      ((IdeleGroup.localOrder_eq_zero_iff w _).mpr hlocal)
  obtain ⟨D, hD, hdegree⟩ := HasPrincipalDivisors.exists_divisor
    (K := k) (F := K) (x : K) x.ne_zero
  have hsingle : D = Finsupp.single v (v.ord (x : K)) := by
    apply Finsupp.ext
    intro w
    rw [hD w]
    by_cases hw : w = v
    · subst w
      rw [Finsupp.single_eq_same]
    · rw [horder w hw, Finsupp.single_eq_of_ne hw]
  have hvorder : v.ord (x : K) = 0 := by
    have : Module.Finite k v.ResidueField := Place.FiniteResidue.finite
    have hvdegree : v.deg ≠ 0 := Module.finrank_pos.ne'
    rw [hsingle, Divisor.degree_single] at hdegree
    exact (mul_eq_zero.mp hdegree).resolve_right (Int.natCast_ne_zero.mpr hvdegree)
  have hmerase : m.erase v ≠ 0 := by
    obtain ⟨w, hw, hwm⟩ := hm
    intro hzero
    apply hwm
    have h := congrArg (fun n : Modulus k K => n w) hzero
    simpa only [Finsupp.erase_ne hw, Finsupp.zero_apply] using h
  apply principalIdele_eq_one_of_mem_congruence (m.erase v) hmerase x
  intro w
  by_cases hw : w = v
  · subst w
    rw [Finsupp.erase_same, localHigherUnitGroup_zero]
    exact (IdeleGroup.localOrder_eq_zero_iff v _).mp
      ((IdeleGroup.localOrder_algebraMap v x).trans hvorder)
  · rw [Finsupp.erase_ne hw]
    exact hx w hw

/-- A positive modulus component away from the chosen place prevents any
nontrivial local ray class from becoming globally principal. -/
theorem localRayToRayClass_injective
    (m : Modulus k K) (v : Place k K)
    (hm : ∃ w : Place k K, w ≠ v ∧ m w ≠ 0) :
    Function.Injective (localRayToRayClass m v) := by
  apply (injective_iff_map_eq_one (localRayToRayClass m v)).mpr
  intro a ha
  have hker : localRayToRestrictedProduct m v a ∈
      (restrictedProductToRayClass m).ker := ha
  rw [restrictedProductToRayClass_ker] at hker
  obtain ⟨x, hx⟩ := hker
  have hxone : x = 1 := principal_eq_one_of_away_congruence m v hm x (by
    intro w hw
    have h := congrArg (fun q : RayRestrictedProduct m => q w) hx
    rw [localRayToRestrictedProduct_of_ne m v w a hw] at h
    change QuotientGroup.mk' (localHigherUnitGroup w (m w))
      (Units.map (algebraMap K w.adicCompletion) x) = 1 at h
    exact (QuotientGroup.eq_one_iff _).mp h)
  have h := congrArg (fun q : RayRestrictedProduct m => q v) hx
  rw [localRayToRestrictedProduct_same, hxone, map_one] at h
  exact h.symm

end FunctionField.RayClass

namespace FunctionField.RayClass

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- The original absolute reciprocity map on a single local ray factor. -/
def localRayAbsoluteArtin (m : Modulus k K) (v : Place k K) :
    RayLocalFactor m v →*
      LocalClassFieldTheory.localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m :=
  (restrictedProductAbsoluteArtin m).comp (localRayToRestrictedProduct m v)

/-- The local embedding evaluates a representative by its original absolute
Artin symbol, with the original arithmetic reciprocity convention. -/
theorem localRayAbsoluteArtin_mk (m : Modulus k K) (v : Place k K)
    (x : v.adicCompletionˣ) :
    localRayAbsoluteArtin m v (QuotientGroup.mk' (localHigherUnitGroup v (m v)) x) =
      QuotientGroup.mk' (artinRaySubgroup m)
        (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))) := by
  change restrictedProductAbsoluteArtin m
    (localRayToRestrictedProduct m v
      (QuotientGroup.mk' (localHigherUnitGroup v (m v)) x)) = _
  rw [localRayToRestrictedProduct_mk, restrictedProductAbsoluteArtin_idele]

/-- At a place with another positive boundary component, actual local ray
classes embed in the original global absolute-Artin quotient. -/
theorem localRayAbsoluteArtin_injective
    (m : Modulus k K) (v : Place k K)
    (hm : ∃ w : Place k K, w ≠ v ∧ m w ≠ 0) :
    Function.Injective (localRayAbsoluteArtin m v) := by
  have hcurve : IsCurveOver k K := FunctionField.isCurveOver k K
  have hres : ∀ w : Place k K, w.FiniteResidue :=
    fun w => ⟨IsCurveOver.finiteResidue w⟩
  exact (rayClassAbsoluteArtin_injective m).comp
    (localRayToRayClass_injective m v hm)

end FunctionField.RayClass
