/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicReciprocity
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalArtinSubgroupNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateSubgroupCarry
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteGaloisArtin
public import Nyll.GaloisCohomology.Cyclic.IntegralTateNegTwoProjection
public import Nyll.GaloisCohomology.Cyclic.TateH0.Main

/-! # The degree-minus-two local Tate isomorphism and the existing Artin map -/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory LocalClassFieldTheory LocalFieldTheory Module
open ClassFieldTower.Cohomology LocalFieldTheory.IsNonarchimedeanLocalField
open IntegralGroupCohomology.Universe
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

private theorem mulEquiv_preserves_generating_zpowers {J G : Type*} [Group J] [Group G]
    (e : J ≃* G) (g : J) (hg : ∀ x : J, x ∈ Subgroup.zpowers g) :
    ∀ y : G, y ∈ Subgroup.zpowers (e g) := by
  intro y
  obtain ⟨n, hn⟩ := hg (e.symm y)
  exact ⟨n, (map_zpow e g n).symm.trans ((congrArg e hn).trans (e.apply_symm_apply y))⟩

private theorem embeddedRestriction_autCongr_of_tower
    {K F E D : Type u} {L : Type v} [Field K] [Field F] [Field L] [Field E] [Field D]
    [Algebra K F] [Algebra K L] [Algebra K E] [Algebra K D] [Algebra F L] [Algebra F D]
    [IsScalarTower K F L] [IsScalarTower K F D] [Normal K E]
    (i : L ≃ₐ[K] E) (d : L ≃ₐ[F] D) (σ : Gal(L/F)) (τ : Gal(L/K))
    (h : ∀ x : L, σ x = τ x) :
    let j := (d.restrictScalars K).toAlgHom.comp i.symm.toAlgHom
    (AlgEquiv.autCongr i) τ = embeddedGaloisRestriction (B := F) j ((AlgEquiv.autCongr d) σ) := by
  intro j
  apply AlgEquiv.ext
  intro x
  apply j.injective
  change j ((AlgEquiv.autCongr i) τ x) =
    j (embeddedGaloisRestriction (B := F) j ((AlgEquiv.autCongr d) σ) x)
  rw [embeddedGaloisRestriction_commutes (B := F) j]
  change d (i.symm (i (τ (i.symm x)))) = d (σ (d.symm (d (i.symm x))))
  rw [i.symm_apply_apply, d.symm_apply_apply, h]

private theorem mapUnits_via_fieldEquiv
    {K : Type u} {L : Type v} {E D : Type u} [Field K] [Field L] [Field E] [Field D]
    [Algebra K L] [Algebra K E] [Algebra K D]
    (i : L ≃ₐ[K] E) (d : L ≃ₐ[K] D) (x : Lˣ) :
    Units.map d.toMonoidHom x =
      Units.map ((d.toAlgHom.comp i.symm.toAlgHom).toMonoidHom) (Units.map i.toMonoidHom x) := by
  apply Units.ext
  exact (congrArg d (i.symm_apply_apply (x : L))).symm

private theorem semilinearGaloisEquiv_refl_action
    {F₀ F L : Type*} [Field F₀] [Field F] [Field L] [Algebra F₀ L] [Algebra F L]
    (e : F₀ ≃+* F) (h : ∀ a : F₀, algebraMap F₀ L a = algebraMap F L (e a))
    (s : Gal(L/F₀)) (x : L) :
    (ClassFieldTheory.semilinearGaloisEquiv e (RingEquiv.refl L) h s) x = s x := rfl

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] (i : L →ₐ[K] SeparableClosure K)

local notation "G" => Gal(L/K)
local notation "J" => localLiftedGaloisGroup K L
local notation "U" => Rep.ofAlgebraAutOnUnits K L
local notation "V" => localLiftedUnitsRepresentation K L
local notation "E" => fundamentalClassStage K L i

private theorem localTateNakayama_fixedClass_of_cyclic_stage
    (F₀ : IntermediateField K L) (F : Type u) [Field F] [Algebra K F] [FiniteDimensional K F]
    [Algebra.IsSeparable K F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [Algebra F L] [IsScalarTower K F L] (e₀ : F₀ ≃ₐ[K] F)
    (hbase : ∀ x : F₀, algebraMap F₀ L x = algebraMap F L (e₀ x))
    (D : FiniteGaloisIntermediateField F (SeparableClosure F)) [Algebra K D] [IsScalarTower K F D]
    (eD : L ≃ₐ[F] D) (eHF : localLiftedFixingSubgroup K L F₀ ≃* Gal(L/F))
    (hRel : ∀ (s : localLiftedFixingSubgroup K L F₀) (x : L), eHF s x = s.val.down x)
    (gH : localLiftedFixingSubgroup K L F₀)
    (hgH : ∀ s : localLiftedFixingSubgroup K L F₀, s ∈ Subgroup.zpowers gH)
    [IsCyclic Gal(D/F)]
    (hgD : ∀ s : Gal(D/F), s ∈ Subgroup.zpowers ((eHF.trans (AlgEquiv.autCongr eD)) gH))
    (b : Fˣ)
    (hb : cyclicContinuousUnitClass F D ((eHF.trans (AlgEquiv.autCongr eD)) gH) hgD
      (Additive.ofMul b) = localFundamentalClass F D) :
    localTateNakayama K L i (-2) (-tateNegTwoUnitClass G gH.val.down) =
      fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L (normUnits K F b)) := by
  let H := localLiftedFixingSubgroup K L F₀
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (J ⧸ H) := Fintype.ofFinite (J ⧸ H)
  let : Fintype (G ⧸ F₀.fixingSubgroup) := Fintype.ofFinite _
  let eDK : L ≃ₐ[K] D := eD.restrictScalars K
  let iE : L ≃ₐ[K] E := i.equivFieldRange
  let j : E →ₐ[K] D := eDK.toAlgHom.comp iE.symm.toAlgHom
  let : Normal K E := (E).isGalois.to_normal
  let stageRestriction : Gal(D/F) →ₜ* Gal(E/K) := embeddedGaloisRestriction (B := F) j
  let stageAction : J ≃* Gal(E/K) := localLiftedStageGroupEquiv K L i
  let eH : H ≃* Gal(D/F) := eHF.trans (AlgEquiv.autCongr eD)
  let gD : Gal(D/F) := eH gH
  let b₀ := Units.mapEquiv e₀.symm.toMulEquiv b
  let a := normUnits K F b
  let l : V ≃+ liftedGaloisUnitsRep F D :=
    (ULift.moduleEquiv : ULift.{v} (Additive Lˣ) ≃ₗ[ℤ] Additive Lˣ).toAddEquiv.trans
      (Units.mapEquiv eD.toMulEquiv).toAdditive
  have hl (s : H) (x : V) : l ((V).ρ s.val x) = (liftedGaloisUnitsRep F D).ρ (eH s) (l x) := by
    have hAction :
        (Rep.ofAlgebraAutOnUnits F L).ρ (eHF s) x.down = (U).ρ s.val.down x.down := by
      apply Additive.toMul.injective
      apply Units.ext
      exact hRel s x.down.toMul.val
    have hMap := unitsMapEquiv_action F L D eD (eHF s) x.down
    exact (congrArg (Units.mapEquiv eD.toMulEquiv).toAdditive hAction.symm).trans hMap
  let c := localLiftedSubgroupTateH2Equiv K L H F D eH l hl
  have he (s : H) : stageAction s.val = stageRestriction (eH s) :=
    embeddedRestriction_autCongr_of_tower iE eD (eHF s) s.val.down (hRel s)
  have hl' (x : V) : l x =
      (Units.map j.toMonoidHom).toAdditive (localLiftedStageUnitsEquiv K L i x) :=
    congrArg (Additive.ofMul : Dˣ → Additive Dˣ)
      (mapUnits_via_fieldEquiv i.equivFieldRange eDK x.down.toMul)
  let y := localFundamentalTateClass K L i
  let B := localLiftedIntermediateUnitFixedVector K L F₀ b₀
  have hB : l B.val = (liftedBaseUnitCycle F D gD b).val := by
    apply Additive.toMul.injective
    apply Units.ext
    change eD (F₀.val (e₀.symm (b : F))) = algebraMap F D (b : F)
    have h := hbase (e₀.symm (b : F))
    rw [e₀.apply_symm_apply] at h
    exact (congrArg eD h).trans (eD.commutes (b : F))
  have hdeg : finrank K E = finrank K F * finrank F D := calc
    _ = finrank K L := iE.toLinearEquiv.finrank_eq.symm
    _ = finrank K F * finrank F L := (Module.finrank_mul_finrank K F L).symm
    _ = _ := congrArg (finrank K F * ·) eD.toLinearEquiv.finrank_eq
  have hy : tateRestrict H V 2 ((tateIsoCommon V 2).inv y) =
      tateCyclicCarryClass (Rep.res H.subtype V) gH hgH B := by
    apply c.injective
    change localLiftedSubgroupTateH2Equiv K L H F D eH l hl _ =
      localLiftedSubgroupTateH2Equiv K L H F D eH l hl _
    rw [localLiftedSubgroupTateH2Equiv_restriction K L i H F D eH l hl j he hl',
      localFundamentalTateClass_lift,
      embeddedRelativeRestriction_localFundamentalClass K F E D j hdeg,
      localLiftedSubgroupTateH2Equiv_carry K L H F D eH l hl gH hgH hgD B b hB]
    exact hb.symm
  have hnorm : normUnits K F₀ b₀ = a := normUnits_algEquiv K F F₀ e₀.symm b
  have hn : corestrictInvariants H V B =
      universeLiftFixedVector U (CyclicCohomology.baseUnitToInvariantUnit K L a) := by
    rw [localLiftedCorestrictInvariants_baseUnit K L F₀ b₀, hnorm]
    rfl
  rw [map_neg, localTateNakayama_apply]
  exact (congrArg Neg.neg (tateCupTrivialInteger_negTwo_bar_of_restrict_carry U H gH hgH y
    (CyclicCohomology.baseUnitToInvariantUnit K L a) B hy hn)).trans (neg_neg _)

private theorem localArtin_norm_eq_of_cyclic_stage
    (F : Type u) [Field F] [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [Algebra F L] [IsScalarTower K F L]
    (D : FiniteGaloisIntermediateField F (SeparableClosure F)) [IsAbelianGalois F D]
    (eD : L ≃ₐ[F] D) (σ : Gal(L/F)) (b : Fˣ)
    (hArtin : abelianLocalArtinMap F D b = ((AlgEquiv.autCongr eD) σ)⁻¹) :
    (topologicalAbelianization_finite_equiv K L).symm
      (Universe.localArtinMapOfEmbedding K L i (normUnits K F b)) =
      Group.Abelianization.of ((AlgEquiv.restrictScalarsHom K σ)⁻¹) := by
  let : FiniteDimensional F L := FiniteDimensional.right K F L
  let : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  let c := localFiniteExtensionClosureEquiv K F (i.comp (IsScalarTower.toAlgHom K F L))
  let j : L →ₐ[F] SeparableClosure F := localIntermediateUpperEmbedding K L F i c
  let jD : L →ₐ[F] SeparableClosure F := D.toIntermediateField.val.comp eD.toAlgHom
  let p := (topologicalAbelianization_finite_equiv F L).symm
  let m := Group.Abelianization.map (AlgEquiv.restrictScalarsHom K : Gal(L/F) →* Gal(L/K))
  have hN := localArtinMapOfEmbedding_norm_restrictScalars K L F i c b
  have hEmb := Universe.localArtinMapOfEmbedding_eq F L j jD
  have hComp := congrArg (fun f : Fˣ →ₜ* _ => m (p (f b))) hEmb
  have hA := localArtinMapOfEmbedding_eq_stage_abelian F L D eD b
  rw [hArtin, ← map_inv, MulEquiv.symm_apply_apply] at hA
  have hm : m (Group.Abelianization.of (σ⁻¹)) =
      Group.Abelianization.of ((AlgEquiv.restrictScalarsHom K σ)⁻¹) := by
    change Group.Abelianization.of (AlgEquiv.restrictScalarsHom K (σ⁻¹)) = _
    rw [map_inv]
  exact hN.trans (hComp.trans ((congrArg m hA).trans hm))

private theorem localTateNakayama_recovers_artin_at_cyclic_stage
    (F₀ : IntermediateField K L) (F : Type u) [Field F] [Algebra K F] [FiniteDimensional K F]
    [Algebra.IsSeparable K F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [Algebra F L] [IsScalarTower K F L] (e₀ : F₀ ≃ₐ[K] F)
    (hbase : ∀ x : F₀, algebraMap F₀ L x = algebraMap F L (e₀ x))
    (D : FiniteGaloisIntermediateField F (SeparableClosure F)) [Algebra K D] [IsScalarTower K F D]
    (eD : L ≃ₐ[F] D) (eHF : localLiftedFixingSubgroup K L F₀ ≃* Gal(L/F))
    (hRel : ∀ (s : localLiftedFixingSubgroup K L F₀) (x : L), eHF s x = s.val.down x)
    (gH : localLiftedFixingSubgroup K L F₀)
    (hgH : ∀ s : localLiftedFixingSubgroup K L F₀, s ∈ Subgroup.zpowers gH)
    [IsCyclic Gal(D/F)] [IsAbelianGalois F D]
    (hgD : ∀ s : Gal(D/F), s ∈ Subgroup.zpowers ((eHF.trans (AlgEquiv.autCongr eD)) gH))
    :
    ∃ a : Kˣ,
      localTateNakayama K L i (-2) (-tateNegTwoUnitClass G gH.val.down) =
        fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a) ∧
      (topologicalAbelianization_finite_equiv K L).symm
        (Universe.localArtinMapOfEmbedding K L i a) = Group.Abelianization.of gH.val.down⁻¹ := by
  let gD := (eHF.trans (AlgEquiv.autCongr eD)) gH
  obtain ⟨b, hb, hArtin⟩ := exists_cyclicFundamentalClass_baseUnit F D gD hgD
  refine ⟨normUnits K F b, ?_, ?_⟩
  · exact localTateNakayama_fixedClass_of_cyclic_stage K L i F₀ F e₀ hbase D eD eHF hRel
      gH hgH hgD b hb
  · have hg : AlgEquiv.restrictScalarsHom K (eHF gH) = gH.val.down := AlgEquiv.ext (hRel gH)
    have h := localArtin_norm_eq_of_cyclic_stage K L i F D eD (eHF gH) b hArtin
    exact h.trans (congrArg (fun τ : Gal(L/K) => Group.Abelianization.of (τ⁻¹)) hg)

/-- A negative original bar representative has a base unit representing its
Tate–Nakayama image whose geometric Artin value is the inverse group element. -/
theorem localTateNakayama_neg_bar_recovers_artin (g : G) :
    ∃ a : Kˣ,
      localTateNakayama K L i (-2) (-tateNegTwoUnitClass G g) =
        fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a) ∧
      (topologicalAbelianization_finite_equiv K L).symm
        (Universe.localArtinMapOfEmbedding K L i a) = Group.Abelianization.of g⁻¹ := by
  let Ω := SeparableClosure K
  let F₀ := IntermediateField.fixedField (Subgroup.zpowers g)
  let f := i.comp F₀.val
  let F := f.fieldRange
  let e₀ := f.equivFieldRange
  let : FiniteDimensional K F := e₀.toLinearEquiv.finiteDimensional
  let : Algebra F L := (F₀.val.toRingHom.comp e₀.symm.toRingHom).toAlgebra
  let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg F₀.val (e₀.symm.commutes x)).symm)
  let : FiniteDimensional F L := FiniteDimensional.right K F L
  let : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  let : NontriviallyNormedField F := finiteExtensionSpectralNormedField K F
  let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F := finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let : Algebra.IsSeparable F Ω := Algebra.isSeparable_tower_top_of_isSeparable K F Ω
  let : IsSepClosure F Ω := ⟨inferInstance, inferInstance⟩
  let : Algebra F (SeparableClosure F) := (separableClosure F (AlgebraicClosure F)).algebra
  let j₀ := IsSepClosure.equiv F Ω (SeparableClosure F)
  have hF (x : F) : i (algebraMap F L x) = F.val x := by
    change f (e₀.symm x) = F.val x
    exact congrArg F.val (e₀.apply_symm_apply x)
  let iF : L →ₐ[F] Ω := { __ := i.toRingHom, commutes' := hF }
  let i' := j₀.toAlgHom.comp iF
  let D : FiniteGaloisIntermediateField F (SeparableClosure F) :=
    i'.finiteGaloisFieldRange
  let fDalgebra : Algebra F D := finiteGaloisStageAlgebra D
  let : Algebra F D := fDalgebra
  let : SMul F D := fDalgebra.toSMul
  let kDalgebra : Algebra K D := ((algebraMap F D).comp (algebraMap K F)).toAlgebra
  let : Algebra K D := kDalgebra
  let : SMul K D := kDalgebra.toSMul
  let : IsScalarTower K F D := IsScalarTower.of_algebraMap_eq'
    (R := K) (S := F) (A := D) rfl
  let eD : L ≃ₐ[F] D := i'.equivFieldRange
  let H := localLiftedFixingSubgroup K L F₀
  let eH₀ : H ≃* F₀.fixingSubgroup := {
    toFun := fun h => ⟨h.val.down, h.property⟩
    invFun := fun h => ⟨ULift.up h.val, h.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hbase (x : F₀) : algebraMap F₀ L x = algebraMap F L (e₀ x) :=
    (congrArg F₀.val (e₀.symm_apply_apply x)).symm
  let relEquiv := ClassFieldTheory.semilinearGaloisEquiv e₀.toRingEquiv (RingEquiv.refl L) hbase
  let eHF : H ≃* Gal(L/F) := (eH₀.trans F₀.fixingSubgroupEquiv).trans relEquiv
  have hRel (s : H) (x : L) : eHF s x = s.val.down x :=
    semilinearGaloisEquiv_refl_action e₀.toRingEquiv hbase (F₀.fixingSubgroupEquiv (eH₀ s)) x
  let eH : H ≃* Gal(D/F) := eHF.trans (AlgEquiv.autCongr eD)
  have hfix : F₀.fixingSubgroup = Subgroup.zpowers g :=
    IntermediateField.fixingSubgroup_fixedField _
  let gH : H := ⟨ULift.up g, by
    change g ∈ F₀.fixingSubgroup
    rw [hfix]
    exact Subgroup.mem_zpowers g⟩
  have hgH (s : H) : s ∈ Subgroup.zpowers gH := by
    have hs : s.val.down ∈ F₀.fixingSubgroup := s.property
    rw [hfix] at hs
    obtain ⟨n, hn⟩ := hs
    exact ⟨n, Subtype.ext (ULift.ext hn)⟩
  let gD : Gal(D/F) := eH gH
  have hgD : ∀ s : Gal(D/F), s ∈ Subgroup.zpowers gD :=
    mulEquiv_preserves_generating_zpowers eH gH hgH
  let : IsCyclic Gal(D/F) := CyclicCohomology.isCyclic_of_generator gD hgD
  let : IsAbelianGalois F D := IsAbelianGalois.of_isCyclic F D
  exact localTateNakayama_recovers_artin_at_cyclic_stage K L i F₀ F e₀ hbase D eD eHF hRel
    gH hgH hgD

/-- Equality of the original fixed classes implies equality under the
existing Artin map because their quotient is an original field norm. -/
theorem localArtinMapOfEmbedding_eq_of_tateFixedClass_eq (a b : Kˣ)
    (h : fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a) =
      fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L b)) :
    Universe.localArtinMapOfEmbedding K L i a = Universe.localArtinMapOfEmbedding K L i b := by
  let A := CyclicCohomology.baseUnitToInvariantUnit K L a
  let B := CyclicCohomology.baseUnitToInvariantUnit K L b
  let Q := fixedNormSubmodule U
  have he : Q.mkQ A = Q.mkQ B :=
    (tateZeroEquivFixedQuotient_fixedClass U A).symm.trans
      ((congrArg (tateZeroEquivFixedQuotient U) h).trans
        (tateZeroEquivFixedQuotient_fixedClass U B))
  have hz : A - B ∈ Q := by
    apply (Submodule.Quotient.mk_eq_zero Q).mp
    change Q.mkQ (A - B) = 0
    exact ((Q.mkQ).map_sub A B).trans (sub_eq_zero.mpr he)
  obtain ⟨z, hz⟩ := hz
  let f := Units.map (algebraMap K L).toMonoidHom
  change (U).ρ.norm z = Additive.ofMul (f a / f b) at hz
  have hnorm : normUnits K L z.toMul = a / b := by
    apply Units.ext
    apply (algebraMap K L).injective
    calc
      algebraMap K L ((normUnits K L z.toMul : Kˣ) : K) =
          (Additive.toMul (show Additive Lˣ from (U).ρ.norm z) : Lˣ).val :=
        (CyclicCohomology.unitsNormLinearMap_apply_val K L z.toMul).symm
      _ = algebraMap K L ((a / b : Kˣ) : K) := by
        rw [hz]
        exact congrArg Units.val (map_div f a b).symm
  let art := Universe.localArtinMapOfEmbedding K L i
  have hart : art (a / b) = 1 := by
    change a / b ∈ art.ker
    rw [Universe.localArtinMapOfEmbedding_ker]
    exact ⟨z.toMul, hnorm⟩
  rw [map_div] at hart
  exact div_eq_one.mp hart

/-- The inverse degree-minus-two isomorphism in the original bar convention
is the original finite Artin map on each base-field unit. -/
theorem localTateNakayama_symm_fixedClass_eq_geometricArtin (a : Kˣ) :
    tateNegTwoUnitAbelianizationEquiv G
        ((localTateNakayama K L i (-2)).symm
          (fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a))) =
      Additive.ofMul ((topologicalAbelianization_finite_equiv K L).symm
        (Universe.localArtinMapOfEmbedding K L i a)) := by
  let e := localTateNakayama K L i (-2)
  let q := tateNegTwoUnitAbelianizationEquiv.{v, v} G
  let x := e.symm (fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a))
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (q (-x)).toMul
  have hx : -tateNegTwoUnitClass G g = x := by
    apply neg_injective
    apply q.injective
    rw [neg_neg]
    exact (tateNegTwoUnitAbelianizationEquiv_class G g).trans (congrArg Additive.ofMul hg)
  obtain ⟨b, hb, hb'⟩ := localTateNakayama_neg_bar_recovers_artin K L i g
  have hfix : fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a) =
      fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L b) := by
    exact (e.apply_symm_apply _).symm.trans ((congrArg e hx.symm).trans hb)
  have ha' := localArtinMapOfEmbedding_eq_of_tateFixedClass_eq K L i a b hfix
  change q x = _
  rw [← hx, map_neg, tateNegTwoUnitAbelianizationEquiv_class, ha', hb']
  exact congrArg Additive.ofMul (map_inv Group.Abelianization.of g).symm

/-- The negative bar convention yields the arithmetic Artin map, the
inverse of the geometric value already defined on the original extension. -/
theorem localTateNakayama_symm_fixedClass_eq_arithmeticArtin (a : Kˣ) :
    -tateNegTwoUnitAbelianizationEquiv G
        ((localTateNakayama K L i (-2)).symm
          (fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a))) =
      Additive.ofMul (((topologicalAbelianization_finite_equiv K L).symm
        (Universe.localArtinMapOfEmbedding K L i a))⁻¹) := by
  rw [localTateNakayama_symm_fixedClass_eq_geometricArtin]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The original degree-zero Tate comparison sends a base unit's actual
fixed representative to its actual field norm class. -/
theorem localTateZeroNormQuotient_fixedClass (a : Kˣ) :
    CyclicCohomology.universeH0TateUnitsAddEquivNormQuotient K L
        (fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a)) =
      Additive.ofMul (normClass K L a) := by
  let x := CyclicCohomology.baseUnitToInvariantUnit K L a
  let B := (IntegralGroupCohomology.coefficientFunctor G).obj U
  let y : B.ρ.invariants := ⟨x.val, x.property⟩
  have h₁ : (tateIsoCommon U 0).hom (fixedClass U x) = TateCohomology.fixedClass B y :=
    TateCohomology.groupEquivIso_hom_fixedClass (MulEquiv.ulift : ULift.{v} G ≃* G)
      (nativeCarrierEquiv U) (nativeCarrierEquiv_comm U) (nativeFixedEquiv U x) y rfl
  let S : ShortComplex (ModuleCat (ULift.{v} ℤ)) :=
    .mk B.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ B) (Rep.norm_comp_d_eq_zero B)
  let z : S.moduleCatLeftHomologyData.K := ⟨y.val, by
    change y.val ∈ LinearMap.ker (groupCohomology.d₀₁ B).hom
    rw [groupCohomology.d₀₁_ker_eq_invariants]
    exact y.property⟩
  let e := TateCohomology.isoZeroBoundary B ≪≫ S.moduleCatHomologyIso
  have hz : (TateCohomology.isoZeroBoundary B).hom (TateCohomology.fixedClass B y) =
      S.homologyπ (S.moduleCatCyclesIso.inv z) := TateCohomology.isoZeroBoundary_fixedCycle B y
  have h₂ : e.hom (TateCohomology.fixedClass B y) = S.moduleCatLeftHomologyData.π z := by
    exact (congrArg S.moduleCatHomologyIso.hom hz).trans
      ((S.π_moduleCatCyclesIso_hom_apply (S.moduleCatCyclesIso.inv z)).trans
        (congrArg S.moduleCatLeftHomologyData.π (Iso.inv_hom_id_apply S.moduleCatCyclesIso z)))
  have h₃ : TateCohomology.fixedClass B y = CyclicCohomology.integralUnitsTateClass K L x := by
    change TateCohomology.fixedClass B y = e.inv (S.moduleCatLeftHomologyData.π z)
    exact (Iso.hom_inv_id_apply e (TateCohomology.fixedClass B y)).symm.trans (congrArg e.inv h₂)
  change CyclicCohomology.integralH0TateUnitsAddEquivNormQuotient K L
    ((tateIsoCommon U 0).hom (fixedClass U x)) = _
  rw [h₁, h₃, CyclicCohomology.integralH0TateUnitsAddEquivNormQuotient_class]
  exact congrArg (fun b : Kˣ => Additive.ofMul (normClass K L b))
    (CyclicCohomology.invariantUnitToBaseUnit_baseUnitToInvariantUnit K L a)

/-- The arithmetic Artin equivalence on the original norm quotient obtained
by inverting the signed degree-minus-two Tate–Nakayama map. -/
def localTateArithmeticArtinNormQuotientEquiv :
    Additive (NormQuotient K L) ≃+ Additive (Group.Abelianization G) := by
  let e₀ := (CyclicCohomology.universeH0TateUnitsAddEquivNormQuotient K L).symm
  let e₁ := (localTateNakayama K L i (-2)).symm.toAddEquiv
  let e₂ := tateNegTwoUnitAbelianizationEquiv G
  exact ((e₀.trans e₁).trans e₂).trans (AddEquiv.neg _)

/-- The recovered norm-quotient map has the existing arithmetic value on each original unit. -/
theorem localTateArithmeticArtinNormQuotientEquiv_apply (a : Kˣ) :
    localTateArithmeticArtinNormQuotientEquiv K L i (Additive.ofMul (normClass K L a)) =
      Additive.ofMul (((topologicalAbelianization_finite_equiv K L).symm
        (Universe.localArtinMapOfEmbedding K L i a))⁻¹) := by
  let e := CyclicCohomology.universeH0TateUnitsAddEquivNormQuotient K L
  let x := fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a)
  have hx : e.symm (Additive.ofMul (normClass K L a)) = x :=
    (congrArg e.symm (localTateZeroNormQuotient_fixedClass K L a)).symm.trans (e.symm_apply_apply x)
  change -tateNegTwoUnitAbelianizationEquiv G
    ((localTateNakayama K L i (-2)).symm (e.symm (Additive.ofMul (normClass K L a)))) = _
  rw [hx]
  exact localTateNakayama_symm_fixedClass_eq_arithmeticArtin K L i a

end ClassFieldTheory.Brauer
