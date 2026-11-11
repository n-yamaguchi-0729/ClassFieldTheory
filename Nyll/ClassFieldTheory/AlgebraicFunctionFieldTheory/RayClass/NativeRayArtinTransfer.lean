/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChange
public import Nyll.ProCGroups.Topologies.QuotientMaps
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Original transfer on actual reduced ray quotients

Actual finite extension of ideles preserves the reduced congruence
subgroups. The proved absolute Artin inclusion square therefore shows
that original group transfer carries the actual ray Artin subgroup
into the pulled-back ray Artin subgroup. Quotienting this original
transfer gives a continuous map of the actual Galois ray quotients.

The resulting restricted-product square is proved on genuine idele
representatives, using the original absolute Artin map and actual
idele inclusion throughout.
-/

@[expose] public section

universe u v

noncomputable section

namespace FunctionField.RayClass

open AlgebraicCurve ClassFormation LocalClassFieldTheory

-- These comparisons use the proved Artin formulas rather than unfolding their construction.
attribute [local irreducible] abelianFiniteArtin finiteArtin

section RaySubgroups

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Actual idele-class inclusion preserves the pulled-back reduced ray
congruence subgroup. -/
theorem baseChange_mem_reducedRayClassSubgroup
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (c : IdeleClassGroup k K) (hc : c ∈ rayClassSubgroup m) :
    IdeleClassGroup.baseChange (k := k) (K := K) (L := L) c ∈
      rayClassSubgroup (rayModulusBaseChange L m) := by
  obtain ⟨a, ha, rfl⟩ := hc
  refine ⟨IdeleGroup.baseChange (K := K) (L := L) a,
    baseChange_mem_reducedCongruence m hm a ha, ?_⟩
  exact (IdeleClassGroup.baseChange_mk a).symm

end RaySubgroups

/-- The type of a continuous transfer between the two specified quotient groups. -/
abbrev RayQuotientTransfer (G : ProfiniteGrp.{u}) (P : ProfiniteGrp.{v})
    (N : Subgroup G) (M : Subgroup P) [N.Normal] [M.Normal] : Type (max u v) :=
  G ⧸ N →ₜ* P ⧸ M

/-- A continuous transfer preserving the specified ray subgroups descends to their quotients. -/
def rayQuotientTransferOfSubgroupMap
    (G : ProfiniteGrp.{u}) (P : ProfiniteGrp.{v})
    (N : Subgroup G) (M : Subgroup P) [N.Normal] [M.Normal]
    (f : G →ₜ* P) (hf : ∀ g : G, g ∈ N → f g ∈ M) :
    RayQuotientTransfer G P N M :=
  ProCGroups.QuotientGroup.mapₜ N M f (by
    intro g hg
    exact (Subgroup.mem_comap (K := M) (f := f.toMonoidHom) (x := g)).2 (hf g hg))

/-- The descended transfer applies the original transfer to representatives. -/
theorem rayQuotientTransferOfSubgroupMap_mk
    (G : ProfiniteGrp.{u}) (P : ProfiniteGrp.{v})
    (N : Subgroup G) (M : Subgroup P) [N.Normal] [M.Normal]
    (f : G →ₜ* P) (hf : ∀ g : G, g ∈ N → f g ∈ M) (g : G) :
    rayQuotientTransferOfSubgroupMap G P N M f hf (QuotientGroup.mk' N g) =
      QuotientGroup.mk' M (f g) :=
  rfl

section NativeTransfer

variable (k : Type u) (K : Type v) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal]

local notation "F" => abstractFixedField K (SeparableClosure K) H.field

/-- The canonical separable-closure algebra of the actual fixed field. -/
local instance nativeRayFixedFieldSeparableClosureAlgebra : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).toSubalgebra.algebra

/-- The fixed field acts on its closure through that same canonical algebra. -/
local instance nativeRayFixedFieldSeparableClosureSMul : SMul F (SeparableClosure F) :=
  (nativeRayFixedFieldSeparableClosureAlgebra (K := K) (H := H)).toSMul

variable (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
    ≃ₐ[(abstractFixedField K (SeparableClosure K) H.field)] SeparableClosure K)

/-- The original absolute group transfer preserves the actual reduced
ray Artin subgroups, by the native absolute reciprocity inclusion square. -/
theorem nativeAbsoluteTransfer_mem_artinRaySubgroup
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : FunctionField k (abstractFixedField K (SeparableClosure K) H.field) :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k) (K := K) (Ω := SeparableClosure K)
        (abstractFixedField K (SeparableClosure K) H.field)
    have _ : HasPrincipalDivisors k (abstractFixedField K (SeparableClosure K) H.field) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K
        (abstractFixedField K (SeparableClosure K) H.field)).toHasPrincipalDivisors
    ∀ g : localAbsoluteAbelianProfinite K, g ∈ artinRaySubgroup m →
      nativeAbsoluteTransferOfFixedField K H e g ∈
        artinRaySubgroup
          (rayModulusBaseChange (abstractFixedField K (SeparableClosure K) H.field) m) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ hKF hFfield hFprincipal g hg
  obtain ⟨c, hc, rfl⟩ := hg
  refine ⟨IdeleClassGroup.baseChange (k := k) (K := K)
      (L := abstractFixedField K (SeparableClosure K) H.field) c,
    baseChange_mem_reducedRayClassSubgroup m hm c hc, ?_⟩
  exact absoluteArtin_baseChange_nativeTransfer k K H e c

-- Quotienting uses the proved ray-subgroup containment, not its Artin-image construction.
attribute [local irreducible] artinRaySubgroup

/-- Actual original transfer descended to the genuine reduced ray Galois
quotients. It is defined from group transfer, before any comparison with
restricted-product reciprocity. -/
def nativeRayTransferOfFixedField (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    let E₀ : IntermediateField K (SeparableClosure K) :=
      abstractFixedField K (SeparableClosure K) H.field
    have _ : FiniteDimensional K E₀ :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : FunctionField k E₀ :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k) (K := K) (Ω := SeparableClosure K) E₀
    have _ : HasPrincipalDivisors k E₀ :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E₀).toHasPrincipalDivisors
    let G₀ := localAbsoluteAbelianProfinite K
    let P₀ := localAbsoluteAbelianProfinite E₀
    let mF : Modulus k E₀ := rayModulusBaseChange E₀ m
    let N : Subgroup G₀ := artinRaySubgroup m
    let M : Subgroup P₀ := artinRaySubgroup mF
    have _ : N.Normal := artinRaySubgroup_normal m
    have _ : M.Normal := artinRaySubgroup_normal mF
    RayQuotientTransfer G₀ P₀ N M := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ E₀ hKF hFfield hFprincipal G₀ P₀ mF N M hN hM
  exact rayQuotientTransferOfSubgroupMap G₀ P₀ N M
    (nativeAbsoluteTransferOfFixedField K H e)
    (nativeAbsoluteTransfer_mem_artinRaySubgroup k K H e m hm)

/-- The descended map retains the literal original transfer value on every
absolute Galois representative. -/
theorem nativeRayTransferOfFixedField_mk (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : FunctionField k (abstractFixedField K (SeparableClosure K) H.field) :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k) (K := K) (Ω := SeparableClosure K)
        (abstractFixedField K (SeparableClosure K) H.field)
    have _ : HasPrincipalDivisors k (abstractFixedField K (SeparableClosure K) H.field) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K
        (abstractFixedField K (SeparableClosure K) H.field)).toHasPrincipalDivisors
    ∀ g : localAbsoluteAbelianProfinite K,
      nativeRayTransferOfFixedField k K H e m hm (QuotientGroup.mk' (artinRaySubgroup m) g) =
        QuotientGroup.mk'
          (artinRaySubgroup
            (rayModulusBaseChange (abstractFixedField K (SeparableClosure K) H.field) m))
          (nativeAbsoluteTransferOfFixedField K H e g) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ hKF hFfield hFprincipal g
  let mF : Modulus k F := rayModulusBaseChange F m
  let N : Subgroup (localAbsoluteAbelianProfinite K) := artinRaySubgroup m
  let M : Subgroup (localAbsoluteAbelianProfinite F) := artinRaySubgroup mF
  let transfer : localAbsoluteAbelianProfinite K →ₜ* localAbsoluteAbelianProfinite F :=
    nativeAbsoluteTransferOfFixedField K H e
  let : N.Normal := artinRaySubgroup_normal m
  let : M.Normal := artinRaySubgroup_normal mF
  have hmaps := nativeAbsoluteTransfer_mem_artinRaySubgroup k K H e m hm
  have hmk := rayQuotientTransferOfSubgroupMap_mk
    (localAbsoluteAbelianProfinite K) (localAbsoluteAbelianProfinite F) N M transfer hmaps g
  exact hmk

-- The descended transfer is used through its proved quotient-representative formula.
attribute [local irreducible] nativeRayTransferOfFixedField

/-- Actual restricted-product inclusion commutes with original Galois
transfer on the genuine reduced ray quotients. The equality is derived
from native absolute reciprocity and actual idele representatives. -/
theorem restrictedProductAbsoluteArtin_baseChange_nativeTransfer
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : FunctionField k (abstractFixedField K (SeparableClosure K) H.field) :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k) (K := K) (Ω := SeparableClosure K)
        (abstractFixedField K (SeparableClosure K) H.field)
    have _ : HasPrincipalDivisors k (abstractFixedField K (SeparableClosure K) H.field) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K
        (abstractFixedField K (SeparableClosure K) H.field)).toHasPrincipalDivisors
    ∀ a : RayRestrictedProduct m,
      restrictedProductAbsoluteArtin
          (rayModulusBaseChange (abstractFixedField K (SeparableClosure K) H.field) m)
          (restrictedRayBaseChange
            (L := abstractFixedField K (SeparableClosure K) H.field) m hm a) =
        nativeRayTransferOfFixedField k K H e m hm (restrictedProductAbsoluteArtin m a) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ hKF hFfield hFprincipal a
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  let mF : Modulus k F := rayModulusBaseChange F m
  let bF : IdeleGroup k F := IdeleGroup.baseChange (k := k) (K := K) (L := F) b
  let quotient : localAbsoluteAbelianProfinite F →
      (localAbsoluteAbelianProfinite F ⧸ artinRaySubgroup mF) :=
    QuotientGroup.mk' (artinRaySubgroup mF)
  have hbase : restrictedRayBaseChange (L := F) m hm (ideleToRayRestrictedProduct m b) =
      ideleToRayRestrictedProduct mF bF :=
    restrictedRayBaseChange_idele (L := F) m hm b
  have hsource : restrictedProductAbsoluteArtin m (ideleToRayRestrictedProduct m b) =
      QuotientGroup.mk' (artinRaySubgroup m) (absoluteArtin k K (IdeleClassGroup.mk b)) :=
    restrictedProductAbsoluteArtin_idele m b
  have htarget : restrictedProductAbsoluteArtin mF (ideleToRayRestrictedProduct mF bF) =
      quotient (absoluteArtin k F (IdeleClassGroup.mk bF)) :=
    restrictedProductAbsoluteArtin_idele mF bF
  have hclasses : IdeleClassGroup.baseChange (k := k) (K := K) (L := F)
      (IdeleClassGroup.mk b) = IdeleClassGroup.mk bF :=
    IdeleClassGroup.baseChange_mk (k := k) (K := K) (L := F) b
  have habsolute : absoluteArtin k F (IdeleClassGroup.mk bF) =
      nativeAbsoluteTransferOfFixedField K H e (absoluteArtin k K (IdeleClassGroup.mk b)) :=
    (congrArg (absoluteArtin k F) hclasses.symm).trans
      (absoluteArtin_baseChange_nativeTransfer k K H e (IdeleClassGroup.mk b))
  have htransfer : nativeRayTransferOfFixedField k K H e m hm
      (QuotientGroup.mk' (artinRaySubgroup m) (absoluteArtin k K (IdeleClassGroup.mk b))) =
      quotient (nativeAbsoluteTransferOfFixedField K H e
        (absoluteArtin k K (IdeleClassGroup.mk b))) :=
    nativeRayTransferOfFixedField_mk k K H e m hm
      (absoluteArtin k K (IdeleClassGroup.mk b))
  have hleft : restrictedProductAbsoluteArtin mF
      (restrictedRayBaseChange (L := F) m hm (ideleToRayRestrictedProduct m b)) =
      quotient (absoluteArtin k F (IdeleClassGroup.mk bF)) :=
    (congrArg (restrictedProductAbsoluteArtin mF) hbase).trans htarget
  have hright : nativeRayTransferOfFixedField k K H e m hm
      (restrictedProductAbsoluteArtin m (ideleToRayRestrictedProduct m b)) =
      quotient (nativeAbsoluteTransferOfFixedField K H e
        (absoluteArtin k K (IdeleClassGroup.mk b))) :=
    (congrArg (nativeRayTransferOfFixedField k K H e m hm) hsource).trans htransfer
  exact hleft.trans ((congrArg quotient habsolute).trans hright.symm)

end NativeTransfer

end FunctionField.RayClass
