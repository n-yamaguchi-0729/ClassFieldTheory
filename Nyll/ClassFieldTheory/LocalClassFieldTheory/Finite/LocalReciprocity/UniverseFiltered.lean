/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Valuation.Integers
public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkOpenSubgroups
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkResidueTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.Ramification.Filtration
public import Nyll.ValuedFieldTheory.Ramification.LocalField.BaseChange
public import Nyll.ValuedFieldTheory.Ramification.LocalField.Core

/-!
# Actual filtered local reciprocity in independent field universes

The same small representatives used by the specified Artin map transport every principal-unit
group. The same Galois conjugation transports the actual upper ramification groups, by the existing
comparison of chosen valuation extensions. Native filtered reciprocity therefore gives the
filtration equality on the original fields, without choosing a norm-quotient isomorphism.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory RamificationTheory RamificationTheory.LocalField

universe u v

/-- Simultaneous shrinking transports the actual chosen-extension upper filtration. -/
theorem localUpperRamificationGroup_map_shrink
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L] (t : ℝ) :
    let : Small.{0} K := smallLocalField K
    let : Small.{0} L := Module.Finite.small K L
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
    let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
      HasseArf.shrink_finiteDimensional K L
    let : IsGalois (Shrink.{0} K) (Shrink.{0} L) :=
      IsGalois.of_equiv_equiv (f := (Shrink.ringEquiv K).symm)
        (g := (Shrink.ringEquiv L).symm) (HasseArf.shrinkAlgebra_commutes K L)
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
      shrinkLocalField_isNonarchimedeanLocalField K
    Subgroup.map (HasseArf.shrinkGalMulEquiv K L).toMonoidHom
        (localUpperRamificationGroup (Shrink.{0} K) (Shrink.{0} L) t) =
      localUpperRamificationGroup K L t := by
  intro sharedSmallK sharedSmallL sharedAlgebra sharedFinite sharedGalois sharedValuation
    sharedLocal
  let eK := Shrink.ringEquiv K
  let eL := Shrink.ringEquiv L
  let : Algebra (Shrink.{0} K) L := ((algebraMap K L).comp eK.toRingHom).toAlgebra
  have hcomp : (algebraMap (Shrink.{0} K) L).comp eK.symm.toRingHom =
      (RingEquiv.refl L).toRingHom.comp (algebraMap K L) := by
    apply RingHom.ext
    intro a
    change algebraMap K L (eK (eK.symm a)) = algebraMap K L a
    rw [RingEquiv.apply_symm_apply]
  let : FiniteDimensional (Shrink.{0} K) L :=
    Module.Finite.of_equiv_equiv eK.symm (RingEquiv.refl L) hcomp
  let : IsGalois (Shrink.{0} K) L :=
    IsGalois.of_equiv_equiv (f := eK.symm) (g := RingEquiv.refl L) hcomp
  let e : Shrink.{0} L ≃ₐ[Shrink.{0} K] L :=
    { eL with commutes' := fun a => HasseArf.shrinkAlgebra_apply K L a }
  have he (a : Shrink.{0} K) :
      algebraMap K L (eK a) = algebraMap (Shrink.{0} K) L a := rfl
  have hvaluation (a : Shrink.{0} K) :
      ValuativeRel.valuation (Shrink.{0} K) a ≤ 1 ↔ ValuativeRel.valuation K (eK a) ≤ 1 := by
    simpa only [Valuation.mem_integer_iff] using shrinkLocalField_mem_integer_iff K a
  let q := galoisGroupEquivOfBaseRingEquiv (Shrink.{0} K) K L eK he
  have hmap : q.toMonoidHom.comp (AlgEquiv.autCongr e).toMonoidHom =
      (HasseArf.shrinkGalMulEquiv K L).toMonoidHom := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    rfl
  have htarget := localUpperRamificationGroup_map_autCongr
    (Shrink.{0} K) (Shrink.{0} L) L e t
  have hbase := localUpperRamificationGroup_map_baseRingEquiv
    (Shrink.{0} K) K L eK he hvaluation t
  rw [← hmap, ← Subgroup.map_map, htarget]
  exact hbase

section Artin

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The image of the actual principal-unit group under the specified Artin map. -/
def artinPrincipalUnitGroup (n : ℕ) : Subgroup Gal(L/K) :=
  (fieldPrincipalUnits K n).map (abelianLocalArtinMonoidHom K L)

/-- The real step filtration of the same actual Artin principal-unit images. -/
def artinPrincipalUnitStepGroup (t : ℝ) : Subgroup Gal(L/K) :=
  natCeilStepFiltration (artinPrincipalUnitGroup K L) t

/-- Filtered reciprocity for the original fields and their actual chosen upper filtration. -/
theorem finiteAbelian_filteredLocalReciprocity (t : ℝ) (ht : 0 ≤ t) :
    artinPrincipalUnitStepGroup K L t = localUpperRamificationGroup K L t := by
  let : Small.{0} K := smallLocalField K
  let : Small.{0} L := Module.Finite.small K L
  let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
  let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_finiteDimensional K L
  let : IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_isAbelianGalois K L
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    shrinkLocalField_isNonarchimedeanLocalField K
  let eU := shrinkUnitsContinuousMulEquiv K
  let eG := HasseArf.shrinkGalMulEquiv K L
  have hArtin : (abelianLocalArtinMonoidHom K L).comp eU.toMulEquiv.toMonoidHom =
      eG.toMonoidHom.comp (_root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (Shrink.{0} K) (Shrink.{0} L)) := by
    apply MonoidHom.ext
    intro a
    rw [← _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom]
    apply AlgEquiv.ext
    intro x
    obtain ⟨z, rfl⟩ := (Shrink.ringEquiv L).surjective x
    change abelianLocalArtinMap K L (eU a) (Shrink.ringEquiv L z) =
      HasseArf.shrinkGalEquiv K L (_root_.LocalClassFieldTheory.abelianLocalArtinMap
        (Shrink.{0} K) (Shrink.{0} L) a) (Shrink.ringEquiv L z)
    rw [abelianLocalArtinMap_apply_shrink, ContinuousMulEquiv.symm_apply_apply,
      HasseArf.shrinkGalEquiv_apply]
  have hunits : (fieldPrincipalUnits (Shrink.{0} K) ⌈t⌉₊).map
      eU.toMulEquiv.toMonoidHom = fieldPrincipalUnits K ⌈t⌉₊ :=
    fieldPrincipalUnits_map_shrink K ⌈t⌉₊
  have himage :
      Subgroup.map eG.toMonoidHom
          (_root_.LocalClassFieldTheory.artinPrincipalUnitStepGroup
            (Shrink.{0} K) (Shrink.{0} L) t) = artinPrincipalUnitStepGroup K L t := by
    rw [_root_.LocalClassFieldTheory.artinPrincipalUnitStepGroup_eq_nativeArtinImage]
    change ((fieldPrincipalUnits (Shrink.{0} K) ⌈t⌉₊).map
      (_root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (Shrink.{0} K) (Shrink.{0} L))).map eG.toMonoidHom =
          (fieldPrincipalUnits K ⌈t⌉₊).map (abelianLocalArtinMonoidHom K L)
    rw [Subgroup.map_map, ← hArtin, ← Subgroup.map_map, hunits]
  rw [← himage, _root_.LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity
    (Shrink.{0} K) (Shrink.{0} L) t ht]
  exact localUpperRamificationGroup_map_shrink K L t

end Artin

/-- On native fields the entire principal-unit image is the original selected image. -/
theorem artinPrincipalUnitGroup_eq_native
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] (n : ℕ) :
    artinPrincipalUnitGroup K L n = _root_.LocalClassFieldTheory.artinPrincipalUnitGroup K L n := by
  rfl

/-- The same comparison holds at every real index of the original selected step filtration. -/
theorem artinPrincipalUnitStepGroup_eq_native
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] (t : ℝ) :
    artinPrincipalUnitStepGroup K L t =
      _root_.LocalClassFieldTheory.artinPrincipalUnitStepGroup K L t :=
  artinPrincipalUnitGroup_eq_native K L ⌈t⌉₊

end LocalClassFieldTheory.Universe
