/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ValuationSemilinear
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteTransfer
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormSubgroupFunctoriality

/-!
# Weil inclusion over a finite separable local extension

An embedding into the lower separable closure gives an open Weil subgroup.
The comparison uses the ordinary Weil group of the original upper field.
-/

@[expose] public section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation LocalFieldTheory ProCGroups.Abelian
open ClassFieldTower.Martinet.Shafarevich
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

section Generic

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

/-- A compatible equivalence of local separable closures preserves the integral Weil degree. -/
noncomputable def localWeilEquivOfClosureEquiv
    (a : K ≃+* L) (c : SeparableClosure K ≃+* SeparableClosure L)
    (hc : ∀ x : K, c (algebraMap K (SeparableClosure K) x) =
      algebraMap L (SeparableClosure L) (a x))
    (hv : localSeparableValuationSubring K =
      (localSeparableValuationSubring L).comap c.toRingHom) :
    localWeilGroup K ≃ₜ* localWeilGroup L := by
  let g := ClassFieldTheory.semilinearGaloisContinuousEquiv a c hc
  have hd (σ : Gal(SeparableClosure K/K)) :
      localResidueDegree L (g σ) = localResidueDegree K σ := by
    have h := localResidueDegree_semilinear_conjugation K L a c hc hv σ
    rw [← h]
    apply congrArg (localResidueDegree L)
    apply AlgEquiv.ext
    intro x
    rfl
  have hi (σ : Gal(SeparableClosure L/L)) :
      localResidueDegree K (g.symm σ) = localResidueDegree L σ := by
    rw [← hd, g.apply_symm_apply]
  let f (x : localWeilGroup K) : localWeilGroup L :=
    ⟨(g (localWeilToAbsolute K x), localWeilDegree K x),
      (hd _).trans (localResidueDegree_localWeilToAbsolute K x)⟩
  let j (x : localWeilGroup L) : localWeilGroup K :=
    ⟨(g.symm (localWeilToAbsolute L x), localWeilDegree L x),
      (hi _).trans (localResidueDegree_localWeilToAbsolute L x)⟩
  exact
    { toFun := f
      invFun := j
      left_inv := fun x => Subtype.ext (Prod.ext (g.symm_apply_apply _) rfl)
      right_inv := fun x => Subtype.ext (Prod.ext (g.apply_symm_apply _) rfl)
      map_mul' := fun x y => Subtype.ext (Prod.ext
        (map_mul (g.toMonoidHom.comp (localWeilToAbsolute K).toMonoidHom) x y)
        (map_mul (localWeilDegree K) x y))
      continuous_toFun := ((g.continuous.comp (localWeilToAbsolute K).continuous).prodMk
        (localWeilDegree K).continuous).subtype_mk _
      continuous_invFun := ((g.symm.continuous.comp (localWeilToAbsolute L).continuous).prodMk
        (localWeilDegree L).continuous).subtype_mk _ }

private theorem localWeilEquivOfClosureEquiv_toAbsolute
    (a : K ≃+* L) (c : SeparableClosure K ≃+* SeparableClosure L)
    (hc : ∀ x : K, c (algebraMap K (SeparableClosure K) x) =
      algebraMap L (SeparableClosure L) (a x))
    (hv : localSeparableValuationSubring K =
      (localSeparableValuationSubring L).comap c.toRingHom)
    (y : TopologicalAbelianization (localWeilGroup K)) :
    localWeilAbelianizationToAbsolute L
        (TopologicalAbelianization.congr (localWeilEquivOfClosureEquiv K L a c hc hv) y) =
      TopologicalAbelianization.congr (ClassFieldTheory.semilinearGaloisContinuousEquiv a c hc)
        (localWeilAbelianizationToAbsolute K y) := by
  obtain ⟨z, rfl⟩ := TopologicalAbelianization.surjective_mk (localWeilGroup K) y
  rfl

/-- Weil reciprocity intertwines the equivalences on units and on Weil abelianizations. -/
theorem localWeilReciprocity_equiv
    (a : K ≃+* L) (c : SeparableClosure K ≃+* SeparableClosure L)
    (hc : ∀ x : K, c (algebraMap K (SeparableClosure K) x) =
      algebraMap L (SeparableClosure L) (a x))
    (ha : SemilinearValuationCompatible K L a) (x : Kˣ) :
    TopologicalAbelianization.congr (localWeilEquivOfClosureEquiv K L a c hc
        (localSeparableValuationSubring_comap_semilinear K L a c hc ha))
        (localWeilReciprocity K x) =
      localWeilReciprocity L (Units.map a.toMonoidHom x) := by
  apply localWeilAbelianizationToAbsolute_injective L
  rw [localWeilEquivOfClosureEquiv_toAbsolute K L a c hc
      (localSeparableValuationSubring_comap_semilinear K L a c hc ha),
    localWeilAbelianizationToAbsolute_localWeilReciprocity,
    localWeilAbelianizationToAbsolute_localWeilReciprocity]
  exact separableAbsoluteLocalArtinMap_equiv K L a c hc ha x

variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  (i : L →ₐ[K] SeparableClosure K)

/-- The image of the chosen embedding gives an actual finite fixing subgroup. -/
noncomputable def localFiniteExtensionAbstractField :
    FiniteAbstractField (Gal(SeparableClosure K/K)) where
  field := RamificationTheory.closedFixingSubgroup K (SeparableClosure K) i.fieldRange
  finite := by
    let : FiniteDimensional K i.fieldRange := i.equivFieldRange.toLinearEquiv.finiteDimensional
    apply Nat.finite_of_card_ne_zero
    change (i.fieldRange.fixingSubgroup.subgroupOf (⊤ : Subgroup _)).index ≠ 0
    rw [show (i.fieldRange.fixingSubgroup.subgroupOf (⊤ : Subgroup _)).index =
        i.fieldRange.fixingSubgroup.index from Subgroup.relIndex_top_right _,
      ← IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K) i.fieldRange]
    exact (Module.finrank_pos : 0 < Module.finrank K i.fieldRange).ne'

local notation "H" => localFiniteExtensionAbstractField K L i
local notation "F" => finiteFixedField K H
local notation "fixedClosure" =>
  FunctionField.fixedFieldSeparableClosureEquiv K (SeparableClosure K) H

attribute [local instance] finiteFixedFieldFiniteDimensional finiteFixedFieldNormedField
  finiteFixedFieldValuativeRel finiteFixedFieldLocalField
  finiteFixedFieldSeparableClosureAlgebra weilFixedFieldAmbientAlgebra weilFixedFieldAmbientTower

/-- The original upper field is isomorphic to the fixed field of its image subgroup. -/
noncomputable def localFiniteExtensionFixedFieldEquiv : L ≃ₐ[K] F :=
  i.equivFieldRange.trans
    (IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup i.fieldRange).symm)

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- A comparison of separable closures lying over the given embedding of coefficient fields. -/
abbrev LocalFiniteExtensionClosureEquiv :=
  let : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
  SeparableClosure L ≃ₐ[L] SeparableClosure K

variable (e : LocalFiniteExtensionClosureEquiv K L i)

/-- The ambient separable closure is also a separable closure of the finite separable extension. -/
noncomputable def localFiniteExtensionClosureEquiv : LocalFiniteExtensionClosureEquiv K L i := by
  let : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
  let : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq' (i.comp_algebraMap).symm
  let : Algebra.IsSeparable L (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K L (SeparableClosure K)
  let : IsSepClosure L (SeparableClosure K) := ⟨inferInstance, inferInstance⟩
  exact IsSepClosure.equiv L (SeparableClosure L) (SeparableClosure K)

/-- The original closure identifies with the closure of the embedded fixed field. -/
noncomputable def localFiniteExtensionUpperClosureEquiv :
    SeparableClosure L ≃+* SeparableClosure F := by
  let : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
  exact e.toRingEquiv.trans (fixedClosure).symm.toRingEquiv

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra.IsSeparable K L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- The upper closure comparison commutes with the given field embedding. -/
theorem localFiniteExtensionUpperClosureEquiv_algebraMap (x : L) :
    localFiniteExtensionUpperClosureEquiv K L i e (algebraMap L (SeparableClosure L) x) =
      algebraMap F (SeparableClosure F) (localFiniteExtensionFixedFieldEquiv K L i x) := by
  let : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
  let e₀ := fixedClosure
  apply e₀.injective
  change e₀ (e₀.symm (e (algebraMap L (SeparableClosure L) x))) = _
  rw [e₀.apply_symm_apply, e.commutes, e₀.commutes]
  rfl

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The embedded fixed-field comparison preserves the original extended valuation. -/
theorem localFiniteExtensionFixedFieldEquiv_valuation :
    SemilinearValuationCompatible L F (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv := by
  let a := (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv
  let j : F →ₐ[K] SeparableClosure K := (abstractFixedField K (SeparableClosure K) (H).field).val
  let : Algebra L F := a.toRingHom.toAlgebra
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  change (ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation F)
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  change ValuativeRel.valuation L x ≤ 1 ↔ ValuativeRel.valuation F (a x) ≤ 1
  rw [← (ValuativeRel.valuation L).mem_valuationSubring_iff,
    ← (ValuativeRel.valuation F).mem_valuationSubring_iff,
    ← localSeparableValuationSubring_comap_embedding K L i,
    ← localSeparableValuationSubring_comap_embedding K F j]
  change i x ∈ localSeparableValuationSubring K ↔ j (a x) ∈ localSeparableValuationSubring K
  have h : j (a x) = i x := rfl
  rw [h]

/-- The original upper Weil group identifies with that of the embedded fixed field. -/
noncomputable def localFiniteExtensionUpperWeilEquiv : localWeilGroup L ≃ₜ* localWeilGroup F :=
  localWeilEquivOfClosureEquiv L F (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv
    (localFiniteExtensionUpperClosureEquiv K L i e)
    (localFiniteExtensionUpperClosureEquiv_algebraMap K L i e)
    (localSeparableValuationSubring_comap_semilinear L F
      (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv
      (localFiniteExtensionUpperClosureEquiv K L i e)
      (localFiniteExtensionUpperClosureEquiv_algebraMap K L i e)
      (localFiniteExtensionFixedFieldEquiv_valuation K L i))

/-- The original upper absolute group identifies with that of the embedded fixed field. -/
noncomputable def localFiniteExtensionUpperAbsoluteEquiv :
    Gal(SeparableClosure L/L) ≃ₜ* Gal(SeparableClosure F/F) :=
  ClassFieldTheory.semilinearGaloisContinuousEquiv
    (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv
    (localFiniteExtensionUpperClosureEquiv K L i e)
    (localFiniteExtensionUpperClosureEquiv_algebraMap K L i e)

private theorem upperWeilEquiv_reciprocity (x : Lˣ) :
    TopologicalAbelianization.congr (localFiniteExtensionUpperWeilEquiv K L i e)
      (localWeilReciprocity L x) =
      localWeilReciprocity F
        (Units.mapEquiv (localFiniteExtensionFixedFieldEquiv K L i).toMulEquiv x) :=
  localWeilReciprocity_equiv L F (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv
    (localFiniteExtensionUpperClosureEquiv K L i e)
    (localFiniteExtensionUpperClosureEquiv_algebraMap K L i e)
    (localFiniteExtensionFixedFieldEquiv_valuation K L i) x

private theorem upperAbsoluteEquiv_artin (x : Lˣ) :
    TopologicalAbelianization.congr (localFiniteExtensionUpperAbsoluteEquiv K L i e)
        (separableAbsoluteLocalArtinMap L x) =
      separableAbsoluteLocalArtinMap F
        (Units.mapEquiv (localFiniteExtensionFixedFieldEquiv K L i).toMulEquiv x) :=
  separableAbsoluteLocalArtinMap_equiv L F (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv
    (localFiniteExtensionUpperClosureEquiv K L i e)
    (localFiniteExtensionUpperClosureEquiv_algebraMap K L i e)
    (localFiniteExtensionFixedFieldEquiv_valuation K L i) x

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra.IsSeparable K L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
private theorem fixedFieldEquiv_map_baseUnits (x : Kˣ) :
    Units.mapEquiv (localFiniteExtensionFixedFieldEquiv K L i).toMulEquiv
        (Units.map (algebraMap K L) x) = Units.map (algebraMap K F) x := by
  apply Units.ext
  exact (localFiniteExtensionFixedFieldEquiv K L i).commutes (x : K)

/-- Inclusion of the absolute Galois group of the original field by restriction of scalars. -/
noncomputable def localFiniteExtensionAbsoluteInclusion :
    Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K) :=
  (localFixedFieldAbsoluteInclusion K H fixedClosure).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (localFiniteExtensionUpperAbsoluteEquiv K L i e))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra.IsSeparable K L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- Absolute inclusion acts on the actual closure by the given conjugation. -/
theorem localFiniteExtensionAbsoluteInclusion_apply
    (σ : Gal(SeparableClosure L/L)) (z : SeparableClosure K) :
    let _ : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
    localFiniteExtensionAbsoluteInclusion K L i e σ z = e (σ (e.symm z)) := by
  intro ambientAlgebra
  let e₀ := fixedClosure
  change e₀ (e₀.symm (e (σ (e.symm (e₀ (e₀.symm z)))))) = e (σ (e.symm z))
  rw [e₀.apply_symm_apply, e₀.apply_symm_apply]

/-- The ordinary Weil group of the original extension embeds continuously into the lower group. -/
noncomputable def localWeilFiniteExtensionInclusion : localWeilGroup L →ₜ* localWeilGroup K :=
  (localWeilFixedFieldInclusion K H fixedClosure).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (localFiniteExtensionUpperWeilEquiv K L i e))

/-- Weil and absolute inclusion use the same action on the original closure. -/
theorem localWeilFiniteExtensionInclusion_absolute (x : localWeilGroup L) :
    localWeilToAbsolute K (localWeilFiniteExtensionInclusion K L i e x) =
      localFiniteExtensionAbsoluteInclusion K L i e (localWeilToAbsolute L x) :=
  rfl

/-- The Weil inclusion is open for the discrete-degree topology on both groups. -/
theorem localWeilFiniteExtensionInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding (localWeilFiniteExtensionInclusion K L i e) :=
  (localWeilFixedFieldInclusion_isOpenEmbedding K H fixedClosure).comp
    (localFiniteExtensionUpperWeilEquiv K L i e).toHomeomorph.isOpenEmbedding

private theorem localWeilFiniteExtensionInclusion_range_eq_fixedFieldRange :
    (localWeilFiniteExtensionInclusion K L i e).toMonoidHom.range =
      (localWeilFixedFieldInclusion K H fixedClosure).toMonoidHom.range := by
  let f := (localWeilFixedFieldInclusion K H fixedClosure).toMonoidHom
  let u := (localFiniteExtensionUpperWeilEquiv K L i e).toMulEquiv
  change (f.comp u.toMonoidHom).range = f.range
  exact (MonoidHom.range_comp f u.toMonoidHom).trans
    ((congrArg (fun V => V.map f) u.range_eq_top).trans (MonoidHom.range_eq_map f).symm)

/-- The open Weil image is the preimage of the Galois subgroup fixing the embedded field. -/
theorem localWeilFiniteExtensionInclusion_range :
    (localWeilFiniteExtensionInclusion K L i e).toMonoidHom.range =
      i.fieldRange.fixingSubgroup.comap (localWeilToAbsolute K).toMonoidHom := by
  exact (localWeilFiniteExtensionInclusion_range_eq_fixedFieldRange K L i e).trans
    (localWeilFixedFieldInclusion_range K H fixedClosure)

/-- The index of the open Weil subgroup is the degree of the original extension. -/
theorem localWeilFiniteExtensionInclusion_index :
    (localWeilFiniteExtensionInclusion K L i e).toMonoidHom.range.index = Module.finrank K L := by
  rw [localWeilFiniteExtensionInclusion_range_eq_fixedFieldRange,
    localWeilFixedFieldInclusion_index]
  exact (localFiniteExtensionFixedFieldEquiv K L i).toLinearEquiv.finrank_eq.symm

/-- Weil inclusion corresponds to the norm of the original finite separable extension. -/
theorem localWeilFiniteExtensionInclusion_reciprocity_norm (x : Lˣ) :
    TopologicalAbelianization.map (localWeilFiniteExtensionInclusion K L i e)
        (localWeilReciprocity L x) =
      localWeilReciprocity K (normUnits K L x) := by
  let j := localWeilFixedFieldInclusion K H fixedClosure
  let b := localFiniteExtensionFixedFieldEquiv K L i
  let u := localFiniteExtensionUpperWeilEquiv K L i e
  have h : TopologicalAbelianization.map (localWeilFiniteExtensionInclusion K L i e)
      (localWeilReciprocity L x) =
      TopologicalAbelianization.map j
        (TopologicalAbelianization.congr u (localWeilReciprocity L x)) :=
    DFunLike.congr_fun
      (TopologicalAbelianization.map_comp j (ContinuousMonoidHom.toContinuousMonoidHom u)) _
  have hUpper := congrArg (TopologicalAbelianization.map j) (upperWeilEquiv_reciprocity K L i e x)
  have hNorm := localWeilFixedFieldInclusion_reciprocity_norm K H fixedClosure
    (Units.mapEquiv b.toMulEquiv x)
  have hField := congrArg (localWeilReciprocity K) (normUnits_algEquiv K L F b x)
  exact h.trans (hUpper.trans (hNorm.trans hField))

/-- Absolute Artin reciprocity commutes with the field norm and literal restriction of scalars. -/
theorem separableAbsoluteLocalArtinMap_finiteExtension_norm (x : Lˣ) :
    TopologicalAbelianization.map (localFiniteExtensionAbsoluteInclusion K L i e)
        (separableAbsoluteLocalArtinMap L x) =
      separableAbsoluteLocalArtinMap K (normUnits K L x) := by
  let j := localFixedFieldAbsoluteInclusion K H fixedClosure
  let b := localFiniteExtensionFixedFieldEquiv K L i
  let u := localFiniteExtensionUpperAbsoluteEquiv K L i e
  have h : TopologicalAbelianization.map (localFiniteExtensionAbsoluteInclusion K L i e)
      (separableAbsoluteLocalArtinMap L x) =
      TopologicalAbelianization.map j
        (TopologicalAbelianization.congr u (separableAbsoluteLocalArtinMap L x)) :=
    DFunLike.congr_fun
      (TopologicalAbelianization.map_comp j (ContinuousMonoidHom.toContinuousMonoidHom u)) _
  have hUpper := congrArg (TopologicalAbelianization.map j) (upperAbsoluteEquiv_artin K L i e x)
  have hNorm := separableAbsoluteLocalArtinMap_norm_restriction K H fixedClosure
    (Units.mapEquiv b.toMulEquiv x)
  have hField := congrArg (separableAbsoluteLocalArtinMap K) (normUnits_algEquiv K L F b x)
  exact h.trans (hUpper.trans (hNorm.trans hField))

/-- Transfer for the actual open Weil image, with target the original upper Weil abelianization. -/
noncomputable def localWeilFiniteExtensionTransfer :
    TopologicalAbelianization (localWeilGroup K) →ₜ*
      TopologicalAbelianization (localWeilGroup L) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (TopologicalAbelianization.congr (localFiniteExtensionUpperWeilEquiv K L i e)).symm).comp
      (localWeilFixedFieldTransfer K H fixedClosure)

/-- Absolute group transfer for the open fixing subgroup, valued on the original upper field. -/
noncomputable def localFiniteExtensionAbsoluteTransfer :
    localAbsoluteAbelianProfinite K →ₜ* localAbsoluteAbelianProfinite L :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (TopologicalAbelianization.congr (localFiniteExtensionUpperAbsoluteEquiv K L i e)).symm).comp
      (localFixedFieldAbsoluteTransfer K H fixedClosure)

private theorem upperWeilAbelianizationToAbsolute_apply
    (x : TopologicalAbelianization (localWeilGroup L)) :
    localWeilAbelianizationToAbsolute F
        (TopologicalAbelianization.congr (localFiniteExtensionUpperWeilEquiv K L i e) x) =
      TopologicalAbelianization.congr (localFiniteExtensionUpperAbsoluteEquiv K L i e)
        (localWeilAbelianizationToAbsolute L x) :=
  localWeilEquivOfClosureEquiv_toAbsolute L F
    (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv
    (localFiniteExtensionUpperClosureEquiv K L i e)
    (localFiniteExtensionUpperClosureEquiv_algebraMap K L i e)
    (localSeparableValuationSubring_comap_semilinear L F
      (localFiniteExtensionFixedFieldEquiv K L i).toRingEquiv
      (localFiniteExtensionUpperClosureEquiv K L i e)
      (localFiniteExtensionUpperClosureEquiv_algebraMap K L i e)
      (localFiniteExtensionFixedFieldEquiv_valuation K L i)) x

/-- The Weil and absolute transfers agree after projection from the Weil abelianization. -/
theorem localWeilFiniteExtensionTransfer_toAbsolute
    (x : TopologicalAbelianization (localWeilGroup K)) :
    localWeilAbelianizationToAbsolute L (localWeilFiniteExtensionTransfer K L i e x) =
      localFiniteExtensionAbsoluteTransfer K L i e (localWeilAbelianizationToAbsolute K x) := by
  let w := TopologicalAbelianization.congr (localFiniteExtensionUpperWeilEquiv K L i e)
  let g := TopologicalAbelianization.congr (localFiniteExtensionUpperAbsoluteEquiv K L i e)
  let z := localWeilFixedFieldTransfer K H fixedClosure x
  let t := localFixedFieldAbsoluteTransfer K H fixedClosure (localWeilAbelianizationToAbsolute K x)
  have h := upperWeilAbelianizationToAbsolute_apply K L i e (w.symm z)
  have hw := congrArg (localWeilAbelianizationToAbsolute F) (w.apply_symm_apply z)
  have ht := localWeilFixedFieldTransfer_toAbsolute K H fixedClosure x
  have hUpper : g (localWeilAbelianizationToAbsolute L (w.symm z)) = t :=
    h.symm.trans (hw.trans ht)
  exact g.injective (hUpper.trans (g.apply_symm_apply t).symm)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra.IsSeparable K L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- The norm image of the extension equals that of its maximal embedded abelian subfield. -/
theorem localFiniteExtension_norm_range_eq_maximalAbelian :
    (normUnits K L).range = localNormSubgroup K (localFixedFieldMaximalAbelian K H) :=
  (normSubgroup_algEquiv K L F (localFiniteExtensionFixedFieldEquiv K L i)).symm.trans
    (localFixedField_norm_range_eq_maximalAbelian K H)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- The original extension has the norm conductor of its maximal embedded abelian subfield. -/
theorem localFiniteExtension_conductor_eq_maximalAbelian :
    localConductorExponent K L = localConductorExponent K (localFixedFieldMaximalAbelian K H) :=
  localConductorExponent_eq_of_normSubgroup_eq K L (localFixedFieldMaximalAbelian K H)
    (localFiniteExtension_norm_range_eq_maximalAbelian K L i)

/-- Absolute group transfer corresponds to scalar inclusion of units in the original field. -/
theorem separableAbsoluteLocalArtinMap_finiteExtension_transfer (x : Kˣ) :
    localFiniteExtensionAbsoluteTransfer K L i e (separableAbsoluteLocalArtinMap K x) =
      separableAbsoluteLocalArtinMap L (Units.map (algebraMap K L) x) := by
  let u := TopologicalAbelianization.congr (localFiniteExtensionUpperAbsoluteEquiv K L i e)
  apply u.injective
  change u (u.symm (localFixedFieldAbsoluteTransfer K H fixedClosure
    (separableAbsoluteLocalArtinMap K x))) =
      u (separableAbsoluteLocalArtinMap L (Units.map (algebraMap K L) x))
  have hInverse := u.apply_symm_apply (localFixedFieldAbsoluteTransfer K H
    fixedClosure (separableAbsoluteLocalArtinMap K x))
  have hTransfer := separableAbsoluteLocalArtinMap_transfer_inclusion K H
    fixedClosure x
  have hUpper := upperAbsoluteEquiv_artin K L i e (Units.map (algebraMap K L) x)
  have hInclusion := congrArg (separableAbsoluteLocalArtinMap F)
    (fixedFieldEquiv_map_baseUnits K L i x)
  exact hInverse.trans (hTransfer.trans ((hUpper.trans hInclusion).symm))

/-- Weil transfer corresponds to inclusion of units in the original finite separable extension. -/
theorem localWeilFiniteExtensionTransfer_reciprocity_inclusion (x : Kˣ) :
    localWeilFiniteExtensionTransfer K L i e (localWeilReciprocity K x) =
      localWeilReciprocity L (Units.map (algebraMap K L) x) := by
  apply localWeilAbelianizationToAbsolute_injective L
  have hTransfer := localWeilFiniteExtensionTransfer_toAbsolute K L i e (localWeilReciprocity K x)
  have hBase := congrArg (localFiniteExtensionAbsoluteTransfer K L i e)
    (localWeilAbelianizationToAbsolute_localWeilReciprocity K x)
  have hArtin := separableAbsoluteLocalArtinMap_finiteExtension_transfer K L i e x
  have hUpper := localWeilAbelianizationToAbsolute_localWeilReciprocity L
    (Units.map (algebraMap K L) x)
  exact hTransfer.trans (hBase.trans (hArtin.trans hUpper.symm))

end Generic

end

end LocalClassFieldTheory
