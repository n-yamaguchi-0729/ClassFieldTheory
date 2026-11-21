/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NativeTransferCoordinates
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalFixedFieldArtinTransfer
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteNonabelianRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilNormNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianBaseEquiv

/-!
# Finite coordinates of absolute local transfer

Group transfer for the actual open fixing subgroup is computed by the
original finite transfer in every ambient-normal Galois quotient. The
relative finite quotient may itself be nonabelian.
-/

@[expose] public section

open scoped ValuativeRel

noncomputable section

namespace LocalClassFieldTheory

open ClassFormation ClassFieldTower.Martinet.Shafarevich CyclicCohomology FunctionField
open LocalFieldTheory ProCGroups.Abelian RamificationTheory

universe u

private def embeddedFiniteAbelianizedRestrictionCharacter
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Group.Abelianization Gal(L/K))]
    [DiscreteTopology (Group.Abelianization Gal(L/K))]
    (i : L →ₐ[K] SeparableClosure K) :
    Gal(SeparableClosure K/K) →ₜ* Group.Abelianization Gal(L/K) :=
  ⟨Group.Abelianization.of.comp (embeddedFiniteRestriction K L i),
    (continuous_of_discreteTopology :
      Continuous (Group.Abelianization.of : Gal(L/K) →* Group.Abelianization Gal(L/K))).comp
      (continuous_embeddedFiniteRestriction K L i)⟩

private theorem absoluteAbelianizedRestrictionOfEmbedding_eq_lift_character
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Group.Abelianization Gal(L/K))]
    [DiscreteTopology (Group.Abelianization Gal(L/K))]
    [T1Space (Group.Abelianization Gal(L/K))]
    (i : L →ₐ[K] SeparableClosure K) (x : localAbsoluteAbelianProfinite K) :
    absoluteAbelianizedRestrictionOfEmbedding K L i x =
      TopologicalAbelianization.lift (embeddedFiniteAbelianizedRestrictionCharacter K L i) x := by
  refine QuotientGroup.induction_on x fun σ => ?_
  exact (absoluteAbelianizedRestrictionOfEmbedding_mk K L i σ).trans
    (TopologicalAbelianization.lift_apply_mk
      (embeddedFiniteAbelianizedRestrictionCharacter K L i) σ).symm

section FiniteCoordinate

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))

local notation "Ω" => SeparableClosure K
local notation "F" => finiteFixedField K H

attribute [local instance] finiteFixedFieldFiniteDimensional finiteFixedFieldNormedField
  finiteFixedFieldValuativeRel finiteFixedFieldLocalField
  finiteFixedFieldSeparableClosureAlgebra weilFixedFieldAmbientAlgebra weilFixedFieldAmbientTower

variable (T : FiniteGaloisSubextension H.field) [T.field.toSubgroup.Normal]

local notation "E" => abstractFixedField K Ω T.field
local notation "P" => abstractRelativeFixedField K Ω T.below

local instance finiteTransferLowerFinite : FiniteDimensional K E :=
  abstractFixedField_finiteDimensional K Ω T.field T.toFiniteAbstractFieldExtension.field.finite

local instance finiteTransferLowerGalois : IsGalois K E :=
  IsGalois.of_fixedField_normal_subgroup T.field.toSubgroup

local instance finiteTransferUpperFinite : FiniteDimensional F P :=
  abstractRelativeFixedField_finiteDimensional K Ω H.field T.field T.below H.finite (T).finite

local instance finiteTransferUpperGalois : IsGalois F P :=
  abstractRelativeFixedField_isGalois K Ω H.field T.field T.below (T).normal

omit [T.field.toSubgroup.Normal] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] in
private theorem embeddedFiniteRestriction_eq_fixedFieldSubgroup
    (e : SeparableClosure F ≃ₐ[F] Ω) (τ : H.field.toSubgroup) :
    let i : P →ₐ[F] SeparableClosure F := (e.symm).toAlgHom.comp (P).val
    let k := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K (SeparableClosure K) H e
    embeddedFiniteRestriction F P i (k.symm τ) =
      fixedFieldSubgroupFiniteRestriction K Ω H T τ := by
  intro i k
  apply AlgEquiv.ext
  intro y
  apply (P).val.injective
  let σ := k.symm τ
  have hRestrict := congrArg e (embeddedFiniteRestriction_commutes F P i σ y)
  have hInclusion := congrArg (fun g : Gal(Ω/K) => g (y : Ω))
    (localFixedFieldAbsoluteInclusion_eq_subtype K H e σ)
  have hInverse := congrArg (fun g : H.field.toSubgroup => g.val (y : Ω))
    (k.apply_symm_apply τ)
  calc
    (P).val (embeddedFiniteRestriction F P i σ y) =
        e (i (embeddedFiniteRestriction F P i σ y)) := (e.apply_symm_apply _).symm
    _ = e (σ (i y)) := hRestrict
    _ = (k σ).val (y : Ω) := hInclusion
    _ = τ.val (y : Ω) := hInverse
    _ = (P).val (fixedFieldSubgroupFiniteRestriction K Ω H T τ y) :=
      (fixedFieldSubgroupFiniteRestriction_commutes K Ω H T τ y).symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem localFixedFieldAbsoluteTransfer_finiteCoordinate_mk
    (e : SeparableClosure F ≃ₐ[F] Ω) (σ : Gal(Ω/K)) :
    let z := TopologicalAbelianization.mk Gal(Ω/K) σ
    absoluteAbelianizedRestrictionOfEmbedding F P ((e.symm).toAlgHom.comp (P).val)
        (localFixedFieldAbsoluteTransfer K H e z) =
      nativeFixedFieldAbelianizedTransfer K H T (absoluteAbelianizedRestriction K E z) := by
  intro z
  let i : P →ₐ[F] SeparableClosure F := (e.symm).toAlgHom.comp (P).val
  let A := Group.Abelianization Gal(P/F)
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : T1Space A := ⟨fun _ => isClosed_discrete _⟩
  let χ := embeddedFiniteAbelianizedRestrictionCharacter F P i
  have hχ := absoluteAbelianizedRestrictionOfEmbedding_eq_lift_character F P i
  let k := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K (SeparableClosure K) H e
  have hcomp : χ.toMonoidHom.comp k.symm.toMulEquiv.toMonoidHom =
      Group.Abelianization.of.comp (fixedFieldSubgroupFiniteRestriction K Ω H T).toMonoidHom := by
    apply MonoidHom.ext
    intro τ
    exact congrArg (Group.Abelianization.of : Gal(P/F) → A)
      (embeddedFiniteRestriction_eq_fixedFieldSubgroup K H T e τ)
  let : Finite (Gal(Ω/K) ⧸ H.field.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite K Ω H.field H.finite
  let : H.field.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let χH : H.field.toSubgroup →* A :=
    Group.Abelianization.of.comp (fixedFieldSubgroupFiniteRestriction K Ω H T).toMonoidHom
  let χ' : H.field.toSubgroup →* A := χ.toMonoidHom.comp k.symm.toMulEquiv.toMonoidHom
  let y := localFixedFieldAbsoluteTransfer K H e z
  let b : Group.Abelianization Gal(E/K) := Group.Abelianization.of (AlgEquiv.restrictNormalHom E σ)
  let f := nativeFixedFieldAbelianizedTransfer K H T
  have hTransfer : TopologicalAbelianization.lift χ y = MonoidHom.transfer χ' σ :=
    localFixedFieldAbsoluteTransfer_character K H e χ σ
  have hCharacter : MonoidHom.transfer χ' σ = MonoidHom.transfer χH σ :=
    congrArg (fun χ₁ : H.field.toSubgroup →* A => MonoidHom.transfer χ₁ σ) hcomp
  have hRight : f b = MonoidHom.transfer χH σ :=
    nativeFixedFieldAbelianizedTransfer_restrict K H T σ
  have hBase := absoluteAbelianizedRestriction_mk K E σ
  have hBaseValue : absoluteAbelianizedRestriction K E z = b := hBase
  have hFiniteValue : f (absoluteAbelianizedRestriction K E z) = MonoidHom.transfer χH σ :=
    (congrArg f hBaseValue).trans hRight
  have hAbsoluteValue : absoluteAbelianizedRestrictionOfEmbedding F P i y =
      MonoidHom.transfer χ' σ := (hχ y).trans hTransfer
  exact hAbsoluteValue.trans (hCharacter.trans hFiniteValue.symm)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Each actual finite restriction of absolute local transfer is the same
finite Galois transfer, in the actual Galois abelianizations. -/
theorem localFixedFieldAbsoluteTransfer_finiteCoordinate
    (e : SeparableClosure F ≃ₐ[F] Ω) (z : localAbsoluteAbelianProfinite K) :
    absoluteAbelianizedRestrictionOfEmbedding F P ((e.symm).toAlgHom.comp (P).val)
        (localFixedFieldAbsoluteTransfer K H e z) =
      nativeFixedFieldAbelianizedTransfer K H T (absoluteAbelianizedRestriction K E z) := by
  refine QuotientGroup.induction_on z fun σ => ?_
  exact localFixedFieldAbsoluteTransfer_finiteCoordinate_mk K H T e σ

end FiniteCoordinate

private theorem finiteAbelianizedRestriction_conjugate_square
    {K Base Top : Type u} [Field K] [Field Base] [Field Top]
    [Algebra K Base] [Algebra Base Top] [Algebra K Top] [IsScalarTower K Base Top]
    [FiniteDimensional K Top] [IsGalois K Top]
    [FiniteDimensional Base Top] [IsGalois Base Top]
    [Algebra Base (SeparableClosure K)]
    (i : Top →ₐ[K] SeparableClosure K) (j : Top →ₐ[Base] SeparableClosure Base)
    (e : SeparableClosure Base ≃ₐ[Base] SeparableClosure K)
    (r : Gal(SeparableClosure Base/Base) →ₜ* Gal(SeparableClosure K/K))
    (hEmb : ∀ a : Top, e (j a) = i a)
    (hConj : ∀ (σ : Gal(SeparableClosure Base/Base)) (a : Top), (r σ) (i a) = e (σ (j a)))
    (z : localAbsoluteAbelianProfinite Base) :
    Group.Abelianization.map (AlgEquiv.restrictScalarsHom K)
        (absoluteAbelianizedRestrictionOfEmbedding Base Top j z) =
      absoluteAbelianizedRestrictionOfEmbedding K Top i
        (TopologicalAbelianization.map r z) := by
  refine QuotientGroup.induction_on z fun σ => ?_
  let τ := embeddedFiniteRestriction Base Top j σ
  let υ := embeddedFiniteRestriction K Top i (r σ)
  have h : AlgEquiv.restrictScalarsHom K τ = υ := by
    apply AlgEquiv.ext
    intro a
    apply i.injective
    change i (τ a) = i (υ a)
    calc
      i (τ a) = e (j (τ a)) := (hEmb (τ a)).symm
      _ = e (σ (j a)) := congrArg e (embeddedFiniteRestriction_commutes Base Top j σ a)
      _ = (r σ) (i a) := (hConj σ a).symm
      _ = i (υ a) := (embeddedFiniteRestriction_commutes K Top i (r σ) a).symm
  exact congrArg (Group.Abelianization.of : Gal(Top/K) →* _) h

/-- Project the actual absolute norm identity to a finite stage over a
base field of degree one. -/
private theorem finiteArtin_restrictScalars_of_absolute
    {K Base Top : Type u} [Field K] [Field Base] [Field Top]
    [Algebra K Base] [Algebra Base Top] [Algebra K Top] [IsScalarTower K Base Top]
    [FiniteDimensional K Top] [IsGalois K Top]
    [FiniteDimensional Base Top] [IsGalois Base Top]
    [Algebra Base (SeparableClosure K)]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel Base] [TopologicalSpace Base] [IsNonarchimedeanLocalField Base]
    (i : Top →ₐ[K] SeparableClosure K) (j : Top →ₐ[Base] SeparableClosure Base)
    (e : SeparableClosure Base ≃ₐ[Base] SeparableClosure K)
    (r : Gal(SeparableClosure Base/Base) →ₜ* Gal(SeparableClosure K/K))
    (hEmb : ∀ a : Top, e (j a) = i a)
    (hConj : ∀ (σ : Gal(SeparableClosure Base/Base)) (a : Top), (r σ) (i a) = e (σ (j a)))
    (hBase : Module.finrank K Base = 1) (x : Kˣ) (y : Baseˣ)
    (hn : TopologicalAbelianization.map r (separableAbsoluteLocalArtinMap Base y) =
      separableAbsoluteLocalArtinMap K x) :
    (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne (E := Top) hBase).abelianizationCongr
      (localArtinMonoidHom Base Top y) = localArtinMonoidHom K Top x := by
  let α := absoluteAbelianizedRestrictionOfEmbedding Base Top j
  let β := absoluteAbelianizedRestrictionOfEmbedding K Top i
  let eGal := ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne (E := Top) hBase
  let q := eGal.abelianizationCongr
  have hB : α (separableAbsoluteLocalArtinMap Base y) = localArtinMonoidHom Base Top y :=
    separableAbsoluteLocalArtinMap_abelianizedRestrictionOfEmbedding Base Top j y
  have hK : β (separableAbsoluteLocalArtinMap K x) = localArtinMonoidHom K Top x :=
    separableAbsoluteLocalArtinMap_abelianizedRestrictionOfEmbedding K Top i x
  have hq : q (α (separableAbsoluteLocalArtinMap Base y)) =
      β (TopologicalAbelianization.map r (separableAbsoluteLocalArtinMap Base y)) :=
    finiteAbelianizedRestriction_conjugate_square i j e r hEmb hConj
      (separableAbsoluteLocalArtinMap Base y)
  exact (congrArg q hB.symm).trans (hq.trans ((congrArg β hn).trans hK))

section TransferInclusion

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))

local notation "Ω" => SeparableClosure K
local notation "F" => finiteFixedField K H

attribute [local instance] finiteFixedFieldFiniteDimensional finiteFixedFieldNormedField
  finiteFixedFieldValuativeRel finiteFixedFieldLocalField
  finiteFixedFieldSeparableClosureAlgebra weilFixedFieldAmbientAlgebra weilFixedFieldAmbientTower

section EmbeddedTransfer

variable (M : IntermediateField K (SeparableClosure K))
  [FiniteDimensional K M] [IsGalois K M]

variable (h : (finiteGaloisAbstractExtensionOfEmbedding K M M.val).field.toSubgroup ≤
  H.field.toSubgroup)

local instance embeddedTransfer_normal :
    (finiteGaloisAbstractExtensionOfEmbedding K M M.val).field.toSubgroup.Normal :=
  inferInstanceAs (finiteGaloisFieldRangeOfEmbedding K M M.val).fixingSubgroup.Normal

/-- An embedded finite Galois extension of the ground field, viewed over its given
finite fixed subfield. -/
def embeddedTransferStage : FiniteGaloisSubextension H.field where
  field := (finiteGaloisAbstractExtensionOfEmbedding K M M.val).field
  below := h
  normal := inferInstanceAs
    (((finiteGaloisAbstractExtensionOfEmbedding K M M.val).field.toSubgroup).subgroupOf
      H.field.toSubgroup).Normal
  finite := by
    let : CompactSpace H.field.toSubgroup :=
      isCompact_iff_compactSpace.mp H.field.isClosed'.isCompact
    apply Subgroup.quotient_finite_of_isOpen
    let L := finiteGaloisFieldRangeOfEmbedding K M M.val
    have hOpen : IsOpen (L.fixingSubgroup : Set (Gal(Ω/K))) :=
      (InfiniteGalois.isOpen_iff_finite (K := Ω) L).mpr inferInstance
    change IsOpen ((fun σ : H.field.toSubgroup => σ.val) ⁻¹'
      (L.fixingSubgroup : Set (Gal(Ω/K))))
    exact hOpen.preimage continuous_subtype_val

local notation "T" => embeddedTransferStage K H M h
local notation "F₀" =>
  abstractFixedField K Ω (FiniteAbstractField.field (intrinsicFiniteAbstractBase K))
local notation "E" => abstractFixedField K Ω
  (finiteGaloisClosedFixingSubgroupOfEmbedding K M (IntermediateField.val M))
local notation "P" => abstractRelativeFixedField K Ω h

local instance embeddedTransferStage_normal : (T).field.toSubgroup.Normal :=
  inferInstanceAs (finiteGaloisAbstractExtensionOfEmbedding K M M.val).field.toSubgroup.Normal

local instance embeddedTransferBase_finite : FiniteDimensional K F₀ :=
  (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finiteDimensional

local instance embeddedTransferBase_normedField : NontriviallyNormedField F₀ :=
  finiteExtensionSpectralNormedField K F₀

local instance embeddedTransferBase_valuativeRel : ValuativeRel F₀ :=
  finiteExtensionSpectralValuativeRel K F₀

local instance embeddedTransferBase_localField : IsNonarchimedeanLocalField F₀ :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K F₀

local instance embeddedTransferTop_finite : FiniteDimensional K E :=
  (finiteGaloisEmbeddedFixedFieldEquiv K M M.val).toLinearEquiv.finiteDimensional

local instance embeddedTransferTop_galois : IsGalois K E :=
  IsGalois.of_fixedField_normal_subgroup
    (finiteGaloisAbstractExtensionOfEmbedding K M M.val).field.toSubgroup

local instance embeddedTransferRelative_finite : FiniteDimensional F P :=
  abstractRelativeFixedField_finiteDimensional K Ω H.field
    (finiteGaloisAbstractExtensionOfEmbedding K M M.val).field h
    H.finite (T).finite

local instance embeddedTransferRelative_galois : IsGalois F P :=
  abstractRelativeFixedField_isGalois K Ω H.field
    (finiteGaloisAbstractExtensionOfEmbedding K M M.val).field h (T).normal

private theorem embeddedBaseAbsoluteArtin_norm_eq (x : Kˣ) :
    let B := intrinsicFiniteAbstractBase K
    let b := finiteGaloisBaseFixedFieldEquiv K
    let x₀ := Units.map b.toRingHom.toMonoidHom x
    let : Algebra F₀ (SeparableClosure F₀) :=
      (separableClosure F₀ (AlgebraicClosure F₀)).algebra
    let e := fixedFieldSeparableClosureEquiv K Ω B
    let g := localFixedFieldAbsoluteInclusion K B e
    TopologicalAbelianization.map g (separableAbsoluteLocalArtinMap F₀ x₀) =
      separableAbsoluteLocalArtinMap K x := by
  intro B b x₀ algebraClosure e g
  have hF₀ : Module.finrank K F₀ = 1 := by
    rw [← b.toLinearEquiv.finrank_eq, Module.finrank_self]
  have hx₀ : x₀ = Units.map (algebraMap K F₀).toMonoidHom x :=
    Units.ext (b.commutes (x : K))
  have hnorm : normUnits K F₀ x₀ = x := by
    rw [hx₀]
    apply Units.ext
    change Algebra.norm K (algebraMap K F₀ (x : K)) = (x : K)
    rw [Algebra.norm_algebraMap, hF₀, pow_one]
  exact (separableAbsoluteLocalArtinMap_norm_restriction K B e x₀).trans
    (congrArg (separableAbsoluteLocalArtinMap K) hnorm)

private abbrev embeddedBaseRelativeAlgebra : Algebra F₀ E :=
  (abstractRelativeFixedField K Ω
    (finiteGaloisAbstractExtensionOfEmbedding K M M.val).below).algebra

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedBaseRelativeScalarTower :
    let : Algebra F₀ E := embeddedBaseRelativeAlgebra K M
    IsScalarTower K F₀ E := by
  intro localAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedBaseRelativeFiniteDimensional :
    let : Algebra F₀ E := embeddedBaseRelativeAlgebra K M
    FiniteDimensional F₀ E := by
  let B := intrinsicFiniteAbstractBase K
  let U := finiteGaloisAbstractExtensionOfEmbedding K M M.val
  exact abstractRelativeFixedField_finiteDimensional K Ω B.field U.field U.below B.finite U.finite

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem embeddedBaseRelativeIsGalois :
    let : Algebra F₀ E := embeddedBaseRelativeAlgebra K M
    IsGalois F₀ E := by
  let B := intrinsicFiniteAbstractBase K
  let U := finiteGaloisAbstractExtensionOfEmbedding K M M.val
  exact abstractRelativeFixedField_isGalois K Ω B.field U.field U.below U.normal

private theorem embeddedBaseArtin_restrictScalars_eq (x : Kˣ) :
    let : Algebra F₀ E := embeddedBaseRelativeAlgebra K M
    let : IsScalarTower K F₀ E := embeddedBaseRelativeScalarTower K M
    let : FiniteDimensional F₀ E := embeddedBaseRelativeFiniteDimensional K M
    let : IsGalois F₀ E := embeddedBaseRelativeIsGalois K M
    let b := finiteGaloisBaseFixedFieldEquiv K
    let x₀ := Units.map b.toRingHom.toMonoidHom x
    let hF₀ : Module.finrank K F₀ = 1 := by
      rw [← b.toLinearEquiv.finrank_eq, Module.finrank_self]
    let k₀ : Gal(E/F₀) ≃* Gal(E/K) :=
      ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF₀
    k₀.abelianizationCongr (localArtinMonoidHom F₀ E x₀) = localArtinMonoidHom K E x := by
  intro algebraOwner towerOwner finiteOwner galoisOwner b x₀ hF₀ k₀
  let B := intrinsicFiniteAbstractBase K
  let : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e := fixedFieldSeparableClosureEquiv K Ω B
  let j : E →ₐ[K] Ω := (E).val
  let U := finiteGaloisAbstractExtensionOfEmbedding K M M.val
  let E₀ := abstractRelativeFixedField K Ω U.below
  let j₀ : E →ₐ[F₀] SeparableClosure F₀ := e.symm.toAlgHom.comp E₀.val
  let g := localFixedFieldAbsoluteInclusion K B e
  let := finiteOwner
  let := galoisOwner
  have hN := embeddedBaseAbsoluteArtin_norm_eq K x
  have hRestrict := finiteArtin_restrictScalars_of_absolute (K := K) (Base := F₀) (Top := E)
    j j₀ e g (fun a => e.apply_symm_apply (j a)) (fun _ _ => rfl) hF₀ x x₀ hN
  dsimp only [k₀]
  exact hRestrict

/-- The finite transfer on the canonical Galois quotients carries finite
Artin to finite Artin of the actual scalar inclusion of the unit. -/
private theorem embeddedFiniteArtin_transfer (x : Kˣ) :
    nativeFixedFieldAbelianizedTransfer K H T (localArtinMonoidHom K E x) =
      localArtinMonoidHom F P (Units.map (algebraMap K F).toMonoidHom x) := by
  let B := intrinsicFiniteAbstractBase K
  let U := finiteGaloisAbstractExtensionOfEmbedding K M M.val
  let S := finiteAbstractFieldOverIntrinsicBase K H
  let hB := S.below
  let hUB := U.below
  let : (extensionSubgroup B.field U.field hUB).Normal := U.normal
  let : Finite (B.field.toSubgroup ⧸ extensionSubgroup B.field U.field hUB) := U.finite
  let E₀ := abstractRelativeFixedField K Ω hUB
  let : Algebra F₀ E := E₀.algebra
  let : IsScalarTower K F₀ E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let : FiniteDimensional F₀ E₀ :=
    abstractRelativeFixedField_finiteDimensional K Ω B.field U.field hUB B.finite U.finite
  let : IsGalois F₀ E₀ :=
    abstractRelativeFixedField_isGalois K Ω B.field U.field hUB U.normal
  let b := finiteGaloisBaseFixedFieldEquiv K
  let x₀ := Units.map b.toRingHom.toMonoidHom x
  let xF := Units.map (algebraMap K F).toMonoidHom x
  have hF₀ : Module.finrank K F₀ = 1 := by
    rw [← b.toLinearEquiv.finrank_eq, Module.finrank_self]
  let k₀ : Gal(E/F₀) ≃* Gal(E/K) :=
    ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF₀
  have hLower :
      k₀.abelianizationCongr (localArtinMonoidHom F₀ E₀ x₀) =
        localArtinMonoidHom K E x :=
    embeddedBaseArtin_restrictScalars_eq K M x
  have hInclusion :
      Units.map (IntermediateField.inclusion
        (abstractFixedField_le K Ω hB)).toRingHom.toMonoidHom x₀ = xF := by
    apply Units.ext
    apply Subtype.ext
    change (b (x : K) : Ω) = algebraMap K Ω (x : K)
    exact congrArg (fun y : F₀ => (y : Ω)) (b.commutes (x : K))
  have htransfer := localArtinMonoidHom_fixedField_transfer K B H U.field h hB x₀
  let transfer := fixedFieldAbelianizedTransfer K Ω S U.field h
  have hLower' : k₀.abelianizationCongr.symm (localArtinMonoidHom K E x) =
      localArtinMonoidHom F₀ E₀ x₀ :=
    (k₀.abelianizationCongr.symm_apply_eq).mpr hLower.symm
  change transfer (k₀.abelianizationCongr.symm (localArtinMonoidHom K E x)) =
    localArtinMonoidHom F P xF
  exact (congrArg transfer hLower').trans (htransfer.trans (congrArg (localArtinMonoidHom F P)
    hInclusion))

/-- Finite Galois projections of local transfer agree with Artin of scalar
inclusion, allowing the ambient-normal stage to be nonabelian. -/
private theorem embeddedAbsoluteArtin_transfer_coordinate
    (e : SeparableClosure F ≃ₐ[F] Ω) (x : Kˣ) :
    absoluteAbelianizedRestrictionOfEmbedding F P ((e.symm).toAlgHom.comp (P).val)
        (localFixedFieldAbsoluteTransfer K H e (separableAbsoluteLocalArtinMap K x)) =
      absoluteAbelianizedRestrictionOfEmbedding F P ((e.symm).toAlgHom.comp (P).val)
        (separableAbsoluteLocalArtinMap F (Units.map (algebraMap K F).toMonoidHom x)) := by
  let j : P →ₐ[F] SeparableClosure F := (e.symm).toAlgHom.comp (P).val
  let xF := Units.map (algebraMap K F).toMonoidHom x
  have hLeft := localFixedFieldAbsoluteTransfer_finiteCoordinate K H T e
    (separableAbsoluteLocalArtinMap K x)
  have hBase := separableAbsoluteLocalArtinMap_abelianizedRestriction K E x
  have hRight := separableAbsoluteLocalArtinMap_abelianizedRestrictionOfEmbedding F P j xF
  exact hLeft.trans ((congrArg (nativeFixedFieldAbelianizedTransfer K H T) hBase).trans
    ((embeddedFiniteArtin_transfer K H M h x).trans hRight.symm))

end EmbeddedTransfer

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem exists_embeddedTransferStage_ker_le
    {Q : Type u} [Group Q] (e : SeparableClosure F ≃ₐ[F] Ω)
    (π : Gal(SeparableClosure F/F) →* Q)
    (hπopen : IsOpen (π.ker : Set Gal(SeparableClosure F/F))) :
    ∃ M : FiniteGaloisIntermediateField K Ω,
      ∃ h : (finiteGaloisAbstractExtensionOfEmbedding K (↥M)
          M.toIntermediateField.val).field.toSubgroup ≤ H.field.toSubgroup,
        let U := finiteGaloisAbstractExtensionOfEmbedding K (↥M) M.toIntermediateField.val
        let : FiniteDimensional K (↥M.toIntermediateField) := M.finiteDimensional
        let : IsGalois K (↥M.toIntermediateField) := M.isGalois
        let T := embeddedTransferStage K H M.toIntermediateField h
        let P := abstractRelativeFixedField K Ω h
        let : FiniteDimensional F P :=
          abstractRelativeFixedField_finiteDimensional K Ω H.field U.field h H.finite T.finite
        let : IsGalois F P := abstractRelativeFixedField_isGalois K Ω H.field U.field h T.normal
        (embeddedFiniteRestriction F P ((e.symm).toAlgHom.comp P.val)).ker ≤ π.ker := by
  let G := Gal(Ω/K)
  let GF := Gal(SeparableClosure F/F)
  let k := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K (SeparableClosure K) H e
  let V : Subgroup H.field.toSubgroup := π.ker.map k.toMulEquiv.toMonoidHom
  have hVopen : IsOpen (V : Set H.field.toSubgroup) :=
    k.toHomeomorph.isOpenMap _ hπopen
  have hHopen : IsOpen (H.field.toSubgroup : Set G) :=
    abstractFiniteClosedSubgroup_isOpen K Ω H.field H.finite
  let W : OpenSubgroup G :=
    { toSubgroup := V.map H.field.toSubgroup.subtype
      isOpen' := hHopen.isOpenEmbedding_subtypeVal.isOpenMap _ hVopen }
  have hWH : W.toSubgroup ≤ H.field.toSubgroup := by
    rintro _ ⟨τ, _, rfl⟩
    exact τ.property
  let C := ProCGroups.ProC.OpenNormalSubgroup.normalCore W
  let S : ClosedSubgroup G :=
    ⟨C.toSubgroup, Subgroup.isClosed_of_isOpen _ C.isOpen'⟩
  let : S.toSubgroup.Normal := C.isNormal'
  let M : IntermediateField K Ω := abstractFixedField K Ω S
  let : IsGalois K M := IsGalois.of_fixedField_normal_subgroup S.toSubgroup
  let : FiniteDimensional K M := by
    apply (InfiniteGalois.isOpen_iff_finite (K := Ω) M).mp
    change IsOpen ((abstractFixedField K Ω S).fixingSubgroup : Set G)
    rw [InfiniteGalois.fixingSubgroup_fixedField S]
    exact C.isOpen'
  let U := finiteGaloisAbstractExtensionOfEmbedding K M M.val
  have hRange : finiteGaloisFieldRangeOfEmbedding K M M.val = M :=
    IntermediateField.fieldRange_val M
  have hUS : U.field = S := by
    change closedFixingSubgroup K Ω (finiteGaloisFieldRangeOfEmbedding K M M.val) = S
    rw [hRange]
    exact closedFixingSubgroup_abstractFixedField_eq K Ω S
  have hS : S.toSubgroup ≤ W.toSubgroup :=
    ProCGroups.ProC.OpenNormalSubgroup.normalCore_le W
  have hUH : U.field.toSubgroup ≤ H.field.toSubgroup := by
    rw [hUS]
    exact hS.trans hWH
  let T := embeddedTransferStage K H M hUH
  let P := abstractRelativeFixedField K Ω hUH
  let : FiniteDimensional F P :=
    abstractRelativeFixedField_finiteDimensional K Ω H.field U.field hUH H.finite (T).finite
  let : IsGalois F P := abstractRelativeFixedField_isGalois K Ω H.field U.field hUH T.normal
  let i : P →ₐ[F] SeparableClosure F := (e.symm).toAlgHom.comp (P).val
  let ρ := embeddedFiniteRestriction F P i
  have hker : ρ.ker ≤ π.ker := by
    intro σ hσ
    have hFixing : (k σ).val ∈ (abstractFixedField K Ω U.field).fixingSubgroup := by
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr ?_
      intro y hy
      let a : P := ⟨y, hy⟩
      have heq := embeddedFiniteRestriction_commutes F P i σ a
      have hρσ : ρ σ = 1 := MonoidHom.mem_ker.mp hσ
      have hAction : ρ σ a = a :=
        (congrArg (fun g : Gal(P/F) => g a) hρσ).trans (AlgEquiv.one_apply a)
      have hFix : e (i a) = e (σ (i a)) :=
        (congrArg (fun b : P => e (i b)) hAction).symm.trans (congrArg e heq)
      have hInclusion := congrArg (fun g : G => g y)
        (localFixedFieldAbsoluteInclusion_eq_subtype K H e σ)
      exact hInclusion.symm.trans (hFix.symm.trans (e.apply_symm_apply y))
    have hFixingEq : (abstractFixedField K Ω U.field).fixingSubgroup = S.toSubgroup :=
      (InfiniteGalois.fixingSubgroup_fixedField U.field).trans
        (congrArg ClosedSubgroup.toSubgroup hUS)
    have hSFix : (k σ).val ∈ S.toSubgroup :=
      Eq.mp (congrArg (fun V' : Subgroup G => (k σ).val ∈ V') hFixingEq) hFixing
    have hMap : (k σ).val ∈ V.map H.field.toSubgroup.subtype := hS hSFix
    have hV : k σ ∈ V := (Subgroup.mem_map_iff_mem Subtype.val_injective).mp hMap
    let f := k.toMulEquiv.toMonoidHom
    exact (Subgroup.mem_map_iff_mem (f := f) (K := π.ker) (x := σ) k.injective).mp hV
  let M₀ : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := M
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  exact ⟨M₀, hUH, hker⟩

/-- In an arbitrary finite separable fixed field, group transfer of the
absolute Artin value is the absolute Artin value of the actual inclusion.
Ambient normal cores permit simultaneous finite testing even when the
fixed field is non-Galois over the original base. -/
theorem separableAbsoluteLocalArtinMap_transfer_inclusion
    (e : SeparableClosure F ≃ₐ[F] Ω) (x : Kˣ) :
    localFixedFieldAbsoluteTransfer K H e (separableAbsoluteLocalArtinMap K x) =
      separableAbsoluteLocalArtinMap F (Units.map (algebraMap K F).toMonoidHom x) := by
  apply ProCGroups.ProC.OpenNormalSubgroup.eq_of_forall_quotientProj_eq
  intro N
  let : N.toSubgroup.Normal := N.isNormal'
  let GF := Gal(SeparableClosure F/F)
  let Q := localAbsoluteAbelianProfinite F ⧸ N.toSubgroup
  let q : localAbsoluteAbelianProfinite F →* Q := QuotientGroup.mk' N.toSubgroup
  let π : GF →* Q := q.comp (localAbsoluteAbelianizationQuotientMap F)
  have hπker : π.ker = (absoluteFiniteQuotientPreimage F N).toSubgroup := by
    ext σ
    let p := localAbsoluteAbelianizationQuotientMap F
    change q (p σ) = 1 ↔ p σ ∈ N.toSubgroup
    exact QuotientGroup.eq_one_iff (N := N.toSubgroup) (p σ)
  have hπopen : IsOpen (π.ker : Set GF) :=
    hπker ▸ (absoluteFiniteQuotientPreimage F N).isOpen'
  obtain ⟨M₀, hUH, hker⟩ := exists_embeddedTransferStage_ker_le K H e π hπopen
  let M := M₀.toIntermediateField
  let : FiniteDimensional K (↥M) := M₀.finiteDimensional
  let : IsGalois K (↥M) := M₀.isGalois
  let U := finiteGaloisAbstractExtensionOfEmbedding K M M.val
  let T := embeddedTransferStage K H M hUH
  let P := abstractRelativeFixedField K Ω hUH
  let : FiniteDimensional F P :=
    abstractRelativeFixedField_finiteDimensional K Ω H.field U.field hUH H.finite T.finite
  let : IsGalois F P := abstractRelativeFixedField_isGalois K Ω H.field U.field hUH T.normal
  let i : P →ₐ[F] SeparableClosure F := (e.symm).toAlgHom.comp (P).val
  let ρ := embeddedFiniteRestriction F P i
  have hρ : Function.Surjective ρ := embeddedFiniteRestriction_surjective F P i
  have hkerρ : ρ.ker ≤ π.ker := hker
  let : IsMulCommutative (localAbsoluteAbelianProfinite F) :=
    IsMulCommutative.of_comm fun a b => (localAbsoluteAbelianProfiniteCommGroup F).mul_comm a b
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N.toSubgroup
  let : IsMulCommutative Q := hq.isMulCommutative
  let c : Gal(P/F) →* Q := ρ.liftOfSurjective hρ ⟨π, hkerρ⟩
  let a : Group.Abelianization Gal(P/F) →* Q := Group.Abelianization.lift c
  let restriction := absoluteAbelianizedRestrictionOfEmbedding F P i
  have ha (y : localAbsoluteAbelianProfinite F) : a (restriction y) = q y := by
    refine QuotientGroup.induction_on y fun σ => ?_
    have hπσ : c (ρ σ) = π σ := MonoidHom.liftOfRightInverse_comp_apply (f := ρ)
      (f_inv := Function.surjInv hρ) (Function.rightInverse_surjInv hρ) ⟨π, hkerρ⟩ σ
    have hCoordinate := absoluteAbelianizedRestrictionOfEmbedding_mk F P i σ
    have hc := Group.Abelianization.lift_apply_of c (ρ σ)
    exact (congrArg a hCoordinate).trans (hc.trans hπσ)
  let y := localFixedFieldAbsoluteTransfer K H e (separableAbsoluteLocalArtinMap K x)
  let z := separableAbsoluteLocalArtinMap F (Units.map (algebraMap K F).toMonoidHom x)
  have hCoordinate : restriction y = restriction z :=
    embeddedAbsoluteArtin_transfer_coordinate K H M hUH e x
  change q y = q z
  exact (ha y).symm.trans ((congrArg a hCoordinate).trans (ha z))

/-- Under ordinary Weil reciprocity, group transfer is scalar inclusion
of the original field units. -/
theorem localWeilFixedFieldTransfer_reciprocity_inclusion
    (e : SeparableClosure F ≃ₐ[F] Ω) (x : Kˣ) :
    localWeilFixedFieldTransfer K H e (localWeilReciprocity K x) =
      localWeilReciprocity F (Units.map (algebraMap K F).toMonoidHom x) := by
  apply localWeilAbelianizationToAbsolute_injective F
  have hTransfer := localWeilFixedFieldTransfer_toAbsolute K H e (localWeilReciprocity K x)
  have hBase := congrArg (localFixedFieldAbsoluteTransfer K H e)
    (localWeilAbelianizationToAbsolute_localWeilReciprocity K x)
  have hArtin := separableAbsoluteLocalArtinMap_transfer_inclusion K H e x
  have hUpper := localWeilAbelianizationToAbsolute_localWeilReciprocity F
    (Units.map (algebraMap K F).toMonoidHom x)
  exact hTransfer.trans (hBase.trans (hArtin.trans hUpper.symm))

end TransferInclusion

end LocalClassFieldTheory
