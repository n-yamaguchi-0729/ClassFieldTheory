/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilRestriction
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
public import Nyll.ProCGroups.Abelian.OpenSubgroupTransfer

/-!
# Norm and transfer for absolute and Weil local reciprocity

Finite abelian restriction detects the absolute Artin value. The extension
used on the upper side is the actual compositum in the chosen separable
closure, so the finite norm identity applies to the same representatives.
-/

@[expose] public section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation ClassFieldTower.Martinet.Shafarevich LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ProCGroups.Abelian

noncomputable section

private theorem sup_isAbelianGalois_over_left
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (F E : IntermediateField K Ω) [FiniteDimensional K E] [IsAbelianGalois K E] :
    let : Algebra F (F ⊔ E : IntermediateField K Ω) :=
      (F.inclusion le_sup_left).toRingHom.toAlgebra
    IsAbelianGalois F (F ⊔ E : IntermediateField K Ω) := by
  intro FA
  let C : IntermediateField K Ω := F ⊔ E
  let A : IntermediateField K C := F.restrict (show F ≤ C from le_sup_left)
  let B : IntermediateField K C := E.restrict (show E ≤ C from le_sup_right)
  let ea : F ≃ₐ[K] A := IntermediateField.restrictAlgEquiv le_sup_left
  let eb : E ≃ₐ[K] B := IntermediateField.restrictAlgEquiv le_sup_right
  let : FiniteDimensional K B := eb.toLinearEquiv.finiteDimensional
  let hB : IsAbelianGalois K B := IsAbelianGalois.of_algHom eb.symm.toAlgHom
  let : IsGalois K B := hB.toIsGalois
  let : Normal K B := hB.toIsGalois.to_normal
  have hsup : B ⊔ A = ⊤ := by
    apply IntermediateField.lift_injective C
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
    exact sup_comm _ _
  let : IsGalois A C := IsGalois.sup_right B A hsup
  let r : Gal(C / A) →* Gal(B / K) := IntermediateField.restrictRestrictAlgEquivMapHom K B A C
  have hr : Function.Injective r :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective B A hsup
  let : IsAbelianGalois A C :=
    { is_comm.comm := fun x y => by
        apply hr
        rw [map_mul, map_mul]
        exact IsMulCommutative.is_comm.comm _ _ }
  apply ClassFieldTheory.isAbelianGalois_of_equiv_equiv ea.symm.toRingEquiv (RingEquiv.refl C)
  apply RingHom.ext
  intro y
  exact congrArg (fun a : A => (a : C)) (ea.apply_symm_apply y)

universe u v

private theorem restrictClosureAut_eq_abelianLocalArtin
    (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (e : SeparableClosure F ≃ₐ[F] Ω) (L : IntermediateField F Ω)
    [FiniteDimensional F L] [IsAbelianGalois F L] (x : Fˣ)
    (σ : Gal(SeparableClosure F/F))
    (hσ : TopologicalAbelianization.mk Gal(SeparableClosure F/F) σ =
      separableAbsoluteLocalArtinMap F x) :
    AlgEquiv.restrictNormalHom L (AlgEquiv.autCongr e σ) =
      abelianLocalArtinMonoidHom F L x := by
  let M : IntermediateField F (SeparableClosure F) := L.map e.symm.toAlgHom
  let c : M ≃ₐ[F] L := (L.equivMap e.symm.toAlgHom).symm
  let : FiniteDimensional F M := c.symm.toLinearEquiv.finiteDimensional
  let : IsAbelianGalois F M := IsAbelianGalois.of_algHom c.toAlgHom
  have hM : AlgEquiv.restrictNormalHom M σ = abelianLocalArtinMonoidHom F M x := by
    rw [← abelianLocalArtinMap_toMonoidHom F M]
    exact (absoluteAbelianRestriction_mk F M σ).symm.trans
      ((congrArg (absoluteAbelianRestriction F M) hσ).trans
        (separableAbsoluteLocalArtinMap_restriction F M x))
  have hnat := DFunLike.congr_fun
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom_autCongr F M L c) x
  change AlgEquiv.autCongr c (abelianLocalArtinMonoidHom F M x) = _ at hnat
  refine Eq.trans ?_ ((congrArg (AlgEquiv.autCongr c) hM).trans hnat)
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  let t := AlgEquiv.restrictNormalHom M σ
  have hc (a : M) : (c a : Ω) = e a := by
    apply e.symm.injective
    have h := IntermediateField.coe_equivMap_apply L e.symm.toAlgHom (c a)
    exact h.symm.trans ((congrArg (fun y : M => (y : SeparableClosure F))
      (c.symm_apply_apply a)).trans (e.symm_apply_apply (a : SeparableClosure F)).symm)
  change ((AlgEquiv.restrictNormalHom L (AlgEquiv.autCongr e σ)) z : Ω) =
    (c (t (c.symm z)) : Ω)
  calc
    _ = e (σ (e.symm (z : Ω))) := AlgEquiv.restrictNormalHom_apply L _ z
    _ = e (σ (c.symm z : M)) :=
      congrArg (fun y : SeparableClosure F => e (σ y))
        (IntermediateField.coe_equivMap_apply L e.symm.toAlgHom z).symm
    _ = e (t (c.symm z) : M) :=
      congrArg e (AlgEquiv.restrictNormalHom_apply M σ (c.symm z)).symm
    _ = _ := (hc (t (c.symm z))).symm

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (H : FiniteAbstractField (Gal(SeparableClosure K/K)))

local notation "F" => finiteFixedField K H
local notation "Ω" => SeparableClosure K

attribute [local instance] finiteFixedFieldFiniteDimensional finiteFixedFieldNormedField
attribute [local instance] finiteFixedFieldValuativeRel finiteFixedFieldLocalField
attribute [local instance] finiteFixedFieldSeparableClosureAlgebra
attribute [local instance] weilFixedFieldAmbientAlgebra weilFixedFieldAmbientTower
attribute [local instance] localAbsoluteAbelianProfiniteCommGroup

private theorem restrictNormalHom_through_fixedField
    {A B P : Type u} [Field A] [Field B] [Field P]
    [Algebra A B] [Algebra A P] [Algebra B P] [IsScalarTower A B P]
    (E : IntermediateField A P) [Normal A E] (L : IntermediateField B P) [Normal B L]
    [Algebra A L] [IsScalarTower A B L] [Algebra E L] [IsScalarTower A E L]
    (h : ∀ a : E, (algebraMap E L a : P) = (a : P)) (τ : Gal(P/B)) :
    AlgEquiv.restrictNormalHom E (τ.restrictScalars A) =
      AlgEquiv.restrictNormalHom E ((AlgEquiv.restrictNormalHom L τ).restrictScalars A) := by
  let ρ := AlgEquiv.restrictNormalHom L τ
  let ρA := ρ.restrictScalars A
  apply AlgEquiv.ext
  intro a
  apply Subtype.ext
  have hCommute := congrArg (fun z : L => (z : P)) (ρA.restrictNormal_commutes E a)
  calc
    (AlgEquiv.restrictNormalHom E (τ.restrictScalars A) a : P) = τ (a : P) :=
      AlgEquiv.restrictNormalHom_apply E _ a
    _ = τ (algebraMap E L a : P) := congrArg τ (h a).symm
    _ = (ρ (algebraMap E L a) : P) := (AlgEquiv.restrictNormalHom_apply L τ _).symm
    _ = _ := by
      change (ρ (algebraMap E L a) : P) = (AlgEquiv.restrictNormalHom E ρA a : P)
      exact hCommute.symm.trans (h _)

private theorem separableAbsoluteLocalArtinMap_norm_restriction_compositum
    (e : SeparableClosure F ≃ₐ[F] Ω)
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsAbelianGalois K E]
    (L : IntermediateField F Ω)
    [fin : @FiniteDimensional F (↥L) _ _ L.algebra.toModule]
    [ab : @IsAbelianGalois F (↥L) _ _ L.algebra]
    [aKL : Algebra K (↥L)] [@IsScalarTower K F (↥L) _ L.algebra.toSMul aKL.toSMul]
    [aEL : Algebra E (↥L)] [@IsScalarTower K (↥E) (↥L) _ aEL.toSMul aKL.toSMul]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (hE : ∀ z : E, (algebraMap E L z : Ω) = (z : Ω)) (x : Fˣ) :
    absoluteAbelianRestriction K E
      (TopologicalAbelianization.map (localFixedFieldAbsoluteInclusion K H e)
        (separableAbsoluteLocalArtinMap F x)) =
      absoluteAbelianRestriction K E (separableAbsoluteLocalArtinMap K (normUnits K F x)) := by
  let aFL : Algebra F (↥L) := L.algebra
  let finFL : @FiniteDimensional F (↥L) _ _ aFL.toModule := fin
  let gFL : @IsAbelianGalois F (↥L) _ _ aFL := ab
  let : @Normal F (↥L) _ _ aFL := gFL.toIsGalois.to_normal
  obtain ⟨sigma, hsigma⟩ := TopologicalAbelianization.surjective_mk
    Gal(SeparableClosure F/F) (separableAbsoluteLocalArtinMap F x)
  let tau := AlgEquiv.autCongr e sigma
  have hL := @restrictClosureAut_eq_abelianLocalArtin F Ω _ _ _ _ _ _ e L fin ab x sigma hsigma
  have hr := DFunLike.congr_fun
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction K F E L) x
  change AlgEquiv.restrictNormalHom E
      ((abelianLocalArtinMonoidHom F L x).restrictScalars K) =
    abelianLocalArtinMonoidHom K E (normUnits K F x) at hr
  let incl := localFixedFieldAbsoluteInclusion K H e
  let abMap := TopologicalAbelianization.map incl
  have hRep : abMap (separableAbsoluteLocalArtinMap F x) =
      TopologicalAbelianization.mk Gal(Ω/K) (incl sigma) :=
    (congrArg abMap hsigma.symm).trans (TopologicalAbelianization.map_apply_mk incl sigma)
  have hLeft := (congrArg (absoluteAbelianRestriction K E) hRep).trans
    (absoluteAbelianRestriction_mk K E (incl sigma))
  have hcoord := restrictNormalHom_through_fixedField E L hE tau
  have hincl : incl sigma = tau.restrictScalars K := rfl
  have hproj := congrArg (AlgEquiv.restrictNormalHom E) hincl
  have hStep := hproj.trans hcoord
  have hMid := congrArg (fun g : Gal(L/F) => AlgEquiv.restrictNormalHom E (g.restrictScalars K)) hL
  have hRight := separableAbsoluteLocalArtinMap_restriction K E (normUnits K F x)
  change _ = (abelianLocalArtinMap K E).toMonoidHom (normUnits K F x) at hRight
  rw [abelianLocalArtinMap_toMonoidHom] at hRight
  exact hLeft.trans (hStep.trans (hMid.trans (hr.trans hRight.symm)))

private theorem separableAbsoluteLocalArtinMap_norm_restriction_finite
    (e : SeparableClosure F ≃ₐ[F] Ω)
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsAbelianGalois K E]
    (x : Fˣ) :
    absoluteAbelianRestriction K E
      (TopologicalAbelianization.map (localFixedFieldAbsoluteInclusion K H e)
        (separableAbsoluteLocalArtinMap F x)) =
      absoluteAbelianRestriction K E (separableAbsoluteLocalArtinMap K (normUnits K F x)) := by
  let B : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) H.field
  let C : IntermediateField K Ω := B ⊔ E
  let hBC : B ≤ C := le_sup_left
  let L : IntermediateField B Ω := B.extendScalars hBC
  let : FiniteDimensional K C := IntermediateField.finiteDimensional_sup B E
  let aFL : Algebra F (↥L) := L.algebra
  let aKL : Algebra K (↥L) := C.algebra'
  let tKFL : @IsScalarTower K F (↥L) _ aFL.toSMul aKL.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let finKL : FiniteDimensional K (↥L) := (inferInstance : FiniteDimensional K C)
  let finFL : @FiniteDimensional F (↥L) _ _ aFL.toModule := FiniteDimensional.right K F (↥L)
  let abFL : @IsAbelianGalois F (↥L) _ _ aFL := sup_isAbelianGalois_over_left B E
  let j : E →ₐ[K] C := E.inclusion (show E ≤ C from le_sup_right)
  let aEL : Algebra E (↥L) := j.toRingHom.toAlgebra
  let : SMul E (↥L) := aEL.toSMul
  let : @IsScalarTower K E (↥L) _ aEL.toSMul aKL.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  exact separableAbsoluteLocalArtinMap_norm_restriction_compositum K H e E L (fun _ => rfl) x

/-- The existing absolute Artin map commutes with the actual norm and the
map of absolute abelianizations induced by the chosen closure embedding. -/
theorem separableAbsoluteLocalArtinMap_norm_restriction
    (e : SeparableClosure F ≃ₐ[F] Ω)
    (x : Fˣ) :
    TopologicalAbelianization.map (localFixedFieldAbsoluteInclusion K H e)
        (separableAbsoluteLocalArtinMap F x) =
      separableAbsoluteLocalArtinMap K (normUnits K F x) := by
  apply ProCGroups.ProC.OpenNormalSubgroup.eq_of_forall_quotientProj_eq
  intro N₀
  let N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K) := N₀
  let : N.toSubgroup.Normal := N.isNormal'
  let : FiniteDimensional K (absoluteFiniteQuotientField K N) :=
    absoluteFiniteQuotientField_finiteDimensional K N
  let : IsAbelianGalois K (absoluteFiniteQuotientField K N) :=
    absoluteFiniteQuotientField_isAbelianGalois K N
  let eN : localAbsoluteAbelianProfinite K ⧸ N.toSubgroup ≃ₜ*
      Gal(absoluteFiniteQuotientField K N / K) := absoluteFiniteQuotientEquiv K N
  have h := separableAbsoluteLocalArtinMap_norm_restriction_finite K H e
    (absoluteFiniteQuotientField K N) x
  have hr (a : localAbsoluteAbelianProfinite K) :
      absoluteAbelianRestriction K (absoluteFiniteQuotientField K N) a =
        absoluteFiniteQuotientEquiv K N (QuotientGroup.mk a) := by
    refine QuotientGroup.induction_on a fun sigma => ?_
    exact (absoluteAbelianRestriction_mk K (absoluteFiniteQuotientField K N) sigma).trans
      (absoluteFiniteQuotientEquiv_mk_mk K N sigma).symm
  exact eN.injective ((hr _).symm.trans (h.trans (hr _)))

/-- Under the ordinary local reciprocity equivalences, the map of Weil
abelianizations for a finite extension is the actual field norm. -/
theorem localWeilFixedFieldInclusion_reciprocity_norm
    (e : SeparableClosure F ≃ₐ[F] Ω)
    (x : Fˣ) :
    TopologicalAbelianization.map (localWeilFixedFieldInclusion K H e)
        (localWeilReciprocity F x) =
      localWeilReciprocity K (normUnits K F x) := by
  apply localWeilAbelianizationToAbsolute_injective K
  let f := localWeilFixedFieldInclusion K H e
  let g := localFixedFieldAbsoluteInclusion K H e
  let j := localWeilToAbsolute K
  let i := localWeilToAbsolute F
  have hs : j.comp f = g.comp i :=
    ContinuousMonoidHom.ext fun z => localWeilFixedFieldInclusion_absolute K H e z
  have hm := (TopologicalAbelianization.map_comp j f).symm.trans
    ((congrArg TopologicalAbelianization.map hs).trans (TopologicalAbelianization.map_comp g i))
  have h (w : TopologicalAbelianization (localWeilGroup F)) :
      localWeilAbelianizationToAbsolute K (TopologicalAbelianization.map f w) =
        TopologicalAbelianization.map g (localWeilAbelianizationToAbsolute F w) :=
    DFunLike.congr_fun hm w
  have hAt := h (localWeilReciprocity F x)
  change localWeilAbelianizationToAbsolute K
      (TopologicalAbelianization.map f (localWeilReciprocity F x)) = _
  rw [hAt, localWeilAbelianizationToAbsolute_localWeilReciprocity,
    localWeilAbelianizationToAbsolute_localWeilReciprocity]
  exact separableAbsoluteLocalArtinMap_norm_restriction K H e x


/-- A unit belongs to the actual norm image exactly when its absolute Artin
class comes from the actual upper absolute abelianization. -/
theorem normUnits_mem_range_iff_separableAbsoluteLocalArtinMap
    (e : SeparableClosure F ≃ₐ[F] Ω)
    (x : Kˣ) :
    x ∈ (normUnits K F).range ↔
      separableAbsoluteLocalArtinMap K x ∈
        (TopologicalAbelianization.map
          (localFixedFieldAbsoluteInclusion K H e)).toMonoidHom.range := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨separableAbsoluteLocalArtinMap F y,
      separableAbsoluteLocalArtinMap_norm_restriction K H e y⟩
  · rintro ⟨p, hp⟩
    obtain ⟨sigma, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(SeparableClosure F/F) p
    let g := localFixedFieldAbsoluteInclusion K H e sigma
    have hArtin : TopologicalAbelianization.mk Gal(Ω/K) g =
        separableAbsoluteLocalArtinMap K x :=
      (TopologicalAbelianization.map_apply_mk (localFixedFieldAbsoluteInclusion K H e) sigma).symm
        |>.trans hp
    let n := valuationUnitsMulHom K x
    have hgn : localResidueDegree K g = localWeilIntegerInclusion n := by
      change localAbsoluteAbelianResidueDegree K
          (TopologicalAbelianization.mk Gal(Ω/K) g) =
        localWeilIntegerInclusion (valuationUnitsMulHom K x)
      exact (congrArg (localAbsoluteAbelianResidueDegree K) hArtin).trans
        (localAbsoluteAbelianResidueDegree_separableAbsoluteLocalArtinMap K x)
    let w : localWeilGroup K := ⟨(g, n), hgn⟩
    have hw : w ∈ (localWeilFixedFieldInclusion K H e).toMonoidHom.range := by
      rw [localWeilFixedFieldInclusion_range]
      change localFixedFieldAbsoluteInclusion K H e sigma ∈ H.field.toSubgroup
      rw [localFixedFieldAbsoluteInclusion_eq_subtype K H e]
      exact Subtype.property _
    obtain ⟨v, hv⟩ := hw
    let y := (localWeilReciprocity F).symm (TopologicalAbelianization.mk (localWeilGroup F) v)
    refine ⟨y, ?_⟩
    apply (localWeilReciprocity K).injective
    apply localWeilAbelianizationToAbsolute_injective K
    rw [← localWeilFixedFieldInclusion_reciprocity_norm K H e y]
    have hy : localWeilReciprocity F y = TopologicalAbelianization.mk (localWeilGroup F) v :=
      (localWeilReciprocity F).apply_symm_apply _
    let j := localWeilAbelianizationToAbsolute K
    let f := localWeilFixedFieldInclusion K H e
    let qK := TopologicalAbelianization.mk (localWeilGroup K)
    have hv' : f v = w := hv
    have h₁ := congrArg (fun p => j (TopologicalAbelianization.map f p)) hy
    have h₂ := congrArg j (TopologicalAbelianization.map_apply_mk f v)
    have h₃ := congrArg (fun z => j (qK z)) hv'
    have h₄ : j (qK w) = TopologicalAbelianization.mk Gal(Ω/K) g :=
      TopologicalAbelianization.map_apply_mk (localWeilToAbsolute K) w
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans
      (hArtin.trans (localWeilAbelianizationToAbsolute_localWeilReciprocity K x).symm))))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem localFixedFieldAbsoluteAbelianization_image_eq
    (e : SeparableClosure F ≃ₐ[F] Ω) :
    (TopologicalAbelianization.map (localFixedFieldAbsoluteInclusion K H e)).toMonoidHom.range =
      H.field.toSubgroup.map (TopologicalAbelianization.mk Gal(Ω/K)) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨g, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(SeparableClosure F/F) p
    refine ⟨localFixedFieldAbsoluteInclusion K H e g, ?_, ?_⟩
    · rw [localFixedFieldAbsoluteInclusion_eq_subtype K H e]
      exact Subtype.property _
    · exact (TopologicalAbelianization.map_apply_mk
        (localFixedFieldAbsoluteInclusion K H e) g).symm
  · rintro ⟨g, hg, rfl⟩
    let s := abstractSubgroupEquivGaloisGroup K Ω H.field
    let gF := (AlgEquiv.autCongr e).symm (s ⟨g, hg⟩)
    refine ⟨TopologicalAbelianization.mk Gal(SeparableClosure F/F) gF, ?_⟩
    refine (TopologicalAbelianization.map_apply_mk
      (localFixedFieldAbsoluteInclusion K H e) gF).trans ?_
    apply congrArg (TopologicalAbelianization.mk Gal(Ω/K))
    have hgF : AlgEquiv.autCongr e gF = s ⟨g, hg⟩ :=
      (AlgEquiv.autCongr e).apply_symm_apply (s ⟨g, hg⟩)
    exact (localFixedFieldAbsoluteInclusion_eq_subtype K H e gF).trans
      (congrArg Subtype.val ((congrArg s.symm hgF).trans (s.symm_apply_apply ⟨g, hg⟩)))

/-- The open normal image of the upper fixing group in the lower absolute
abelianization. It depends on the embedded fixed field itself. -/
def localFixedFieldAbelianImage : OpenNormalSubgroup (localAbsoluteAbelianProfinite K) where
  toOpenSubgroup :=
    { toSubgroup := H.field.toSubgroup.map (TopologicalAbelianization.mk Gal(Ω/K))
      isOpen' := by
        change IsOpen ((TopologicalAbelianization.mk Gal(Ω/K)) ''
          (H.field.toSubgroup : Set Gal(Ω/K)))
        exact QuotientGroup.isOpenMap_coe _
          (abstractFiniteClosedSubgroup_isOpen K Ω H.field H.finite) }
  isNormal' := by
    change (H.field.toSubgroup.map (TopologicalAbelianization.mk Gal(Ω/K))).Normal
    infer_instance

/-- The maximal abelian subfield of the actual finite fixed field. -/
def localFixedFieldMaximalAbelian : IntermediateField K Ω :=
  absoluteFiniteQuotientField K (localFixedFieldAbelianImage K H)

/-- The abelian fixed-field construction retains the finite degree over the base. -/
instance localFixedFieldMaximalAbelian_finiteDimensional :
    FiniteDimensional K (localFixedFieldMaximalAbelian K H) :=
  absoluteFiniteQuotientField_finiteDimensional K (localFixedFieldAbelianImage K H)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem localFixedFieldMaximalAbelian_le :
    localFixedFieldMaximalAbelian K H ≤ abstractFixedField K Ω H.field := by
  apply IntermediateField.fixedField_le
  intro g hg
  exact ⟨g, hg, rfl⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Every abelian subextension embedded into the finite fixed field is
contained in its maximal abelian subfield. -/
theorem le_localFixedFieldMaximalAbelian
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsAbelianGalois K E]
    (hEF : E ≤ abstractFixedField K Ω H.field) :
    E ≤ localFixedFieldMaximalAbelian K H := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup E]
  apply IntermediateField.fixedField_le
  intro g hg
  obtain ⟨h, hh, hq⟩ := hg
  have hfix : h ∈ E.fixingSubgroup := by
    apply IntermediateField.fixingSubgroup_antitone hEF
    rw [InfiniteGalois.fixingSubgroup_fixedField H.field]
    exact hh
  have hr := congrArg (absoluteAbelianRestriction K E) hq
  have hrestrict := (absoluteAbelianRestriction_mk K E h).symm.trans
    (hr.trans (absoluteAbelianRestriction_mk K E g))
  rw [← IntermediateField.restrictNormalHom_ker] at hfix ⊢
  exact hrestrict.symm.trans (MonoidHom.mem_ker.mp hfix)

/-- Local norm limitation for an actual finite separable fixed field. The
norm image is that of the largest abelian subextension in the same closure. -/
theorem localFixedField_norm_range_eq_maximalAbelian :
    (normUnits K F).range = localNormSubgroup K (localFixedFieldMaximalAbelian K H) := by
  let : Algebra.IsSeparable F Ω := Algebra.isSeparable_tower_top_of_isSeparable K F Ω
  let : IsSepClosure F Ω := ⟨inferInstance, inferInstance⟩
  let closureEquiv := IsSepClosure.equiv F (SeparableClosure F) Ω
  let N := localFixedFieldAbelianImage K H
  ext x
  rw [normUnits_mem_range_iff_separableAbsoluteLocalArtinMap K H closureEquiv,
    localFixedFieldAbsoluteAbelianization_image_eq K H closureEquiv]
  let q := separableAbsoluteLocalArtinMap K x
  change q ∈ N.toSubgroup ↔ x ∈ localNormSubgroup K (absoluteFiniteQuotientField K N)
  rw [← absoluteFiniteArtinMap_ker K N, MonoidHom.mem_ker]
  change q ∈ N.toSubgroup ↔ absoluteFiniteArtinMap K N x = 1
  rw [← separableAbsoluteLocalArtinMap_finiteProjection K N x]
  exact (QuotientGroup.eq_one_iff q).symm

/-- The norm conductor of a finite separable local extension is the
conductor of its maximal abelian subfield in the same separable closure. -/
theorem localFixedField_conductor_eq_maximalAbelian :
    localConductorExponent K F =
      localConductorExponent K (localFixedFieldMaximalAbelian K H) :=
  localConductorExponent_eq_of_normSubgroup_eq K F (localFixedFieldMaximalAbelian K H)
    (localFixedField_norm_range_eq_maximalAbelian K H)

/-- The open subgroup fixing the specified finite local field in the chosen closure. -/
def localFixedFieldOpenSubgroup : OpenSubgroup Gal(Ω/K) where
  toSubgroup := H.field.toSubgroup
  isOpen' := abstractFiniteClosedSubgroup_isOpen K Ω H.field H.finite

local instance localFixedFieldOpenSubgroup_finite :
    Finite (Gal(Ω/K) ⧸ (localFixedFieldOpenSubgroup K H : Subgroup Gal(Ω/K))) :=
  ambientQuotientFiniteOfAbstractFinite K Ω H.field H.finite

/-- Transfer between the actual local absolute abelianizations, along the
fixing subgroup identified by the comparison of separable closures. -/
noncomputable def localFixedFieldAbsoluteTransfer
    (e : SeparableClosure F ≃ₐ[F] Ω) :
    localAbsoluteAbelianProfinite K →ₜ* localAbsoluteAbelianProfinite F :=
  let k := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e
  (ContinuousMonoidHom.toContinuousMonoidHom (TopologicalAbelianization.congr k.symm)).comp
    (openSubgroupTransfer (localFixedFieldOpenSubgroup K H))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Computing an upper character on absolute transfer uses the original
group transfer of the character on the actual fixing subgroup. -/
theorem localFixedFieldAbsoluteTransfer_character
    (e : SeparableClosure F ≃ₐ[F] Ω)
    {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]
    (χ : Gal(SeparableClosure F/F) →ₜ* A) (σ : Gal(Ω/K)) :
    let : Finite (Gal(Ω/K) ⧸ H.field.toSubgroup) :=
      ambientQuotientFiniteOfAbstractFinite K Ω H.field H.finite
    let : H.field.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    TopologicalAbelianization.lift χ
        (localFixedFieldAbsoluteTransfer K H e (TopologicalAbelianization.mk Gal(Ω/K) σ)) =
      MonoidHom.transfer
        (χ.toMonoidHom.comp
          (MulEquiv.toMonoidHom
            (FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e).symm.toMulEquiv))
        σ := by
  intro hFinite hindex
  let B := localFixedFieldOpenSubgroup K H
  let : IsTopologicalGroup B :=
    inferInstanceAs (IsTopologicalGroup ↥(B : Subgroup (Gal(Ω/K))))
  let k := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e
  exact lift_openSubgroupTransfer_congr_apply_mk B k.symm χ σ

private theorem abelianizedSquare_apply
    {A B X Y : Type*} [Group A] [Group B] [Group X] [Group Y]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup X] [IsTopologicalGroup Y]
    (a : A →ₜ* X) (b : A →ₜ* B) (c : X →ₜ* Y) (d : B →ₜ* Y)
    (h : ∀ t, c (a t) = d (b t)) (z : TopologicalAbelianization A) :
    TopologicalAbelianization.map c (TopologicalAbelianization.map a z) =
      TopologicalAbelianization.map d (TopologicalAbelianization.map b z) := by
  have hs : c.comp a = d.comp b := ContinuousMonoidHom.ext h
  have hm := (TopologicalAbelianization.map_comp c a).symm.trans
    ((congrArg TopologicalAbelianization.map hs).trans (TopologicalAbelianization.map_comp d b))
  exact DFunLike.congr_fun hm z

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Compatible equivalences of the actual absolute inclusions transport group transfer. -/
theorem localFixedFieldAbsoluteTransfer_congr_of_inclusion
    (e : SeparableClosure F ≃ₐ[F] Ω)
    (M : Type v) [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    (J : FiniteAbstractField Gal(SeparableClosure M/M))
    (e' : SeparableClosure (finiteFixedField M J) ≃ₐ[finiteFixedField M J] SeparableClosure M)
    (f : Gal(Ω/K) ≃ₜ* Gal(SeparableClosure M/M))
    (g : Gal(SeparableClosure F/F) ≃ₜ*
      Gal(SeparableClosure (finiteFixedField M J)/finiteFixedField M J))
    (hsq : ∀ σ : Gal(SeparableClosure F/F),
      f (localFixedFieldAbsoluteInclusion K H e σ) = localFixedFieldAbsoluteInclusion M J e' (g σ))
    (z : localAbsoluteAbelianProfinite K) :
    TopologicalAbelianization.congr g (localFixedFieldAbsoluteTransfer K H e z) =
      localFixedFieldAbsoluteTransfer M J e' (TopologicalAbelianization.congr f z) := by
  let A := localFixedFieldOpenSubgroup K H
  let : IsTopologicalGroup A :=
    inferInstanceAs (IsTopologicalGroup ↥(A : Subgroup Gal(Ω/K)))
  let B := localFixedFieldOpenSubgroup M J
  let : IsTopologicalGroup B :=
    inferInstanceAs (IsTopologicalGroup ↥(B : Subgroup Gal(SeparableClosure M/M)))
  let k := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K (SeparableClosure K) H e
  let l := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure M (SeparableClosure M) J e'
  have hval (a : A) : (l (g (k.symm a)) : Gal(SeparableClosure M/M)) = f a := by
    calc
      (l (g (k.symm a)) : Gal(SeparableClosure M/M)) =
          localFixedFieldAbsoluteInclusion M J e' (g (k.symm a)) :=
        (localFixedFieldAbsoluteInclusion_eq_subtype M J e' _).symm
      _ = f (localFixedFieldAbsoluteInclusion K H e (k.symm a)) := (hsq _).symm
      _ = f (k (k.symm a)).val := congrArg f (localFixedFieldAbsoluteInclusion_eq_subtype K H e _)
      _ = f a := congrArg (fun b : A => f b.val) (k.apply_symm_apply a)
  refine openSubgroupTransfer_congr_of_inclusion A B k.symm l.symm f g (fun a => ?_) z
  exact (congrArg
    (fun e₀ : Gal(SeparableClosure (finiteFixedField M J)/finiteFixedField M J) ≃ₜ* B =>
      (e₀ (g (k.symm a)) : Gal(SeparableClosure M/M)))
    (ContinuousMulEquiv.symm_symm l)).trans (hval a)

/-- The open image of the upper Weil group in the base Weil group. -/
def localWeilFixedFieldOpenImage
    (e : SeparableClosure F ≃ₐ[F] Ω) : OpenSubgroup (localWeilGroup K) where
  toSubgroup := (localWeilFixedFieldInclusion K H e).toMonoidHom.range
  isOpen' := localWeilFixedFieldInclusion_isOpen_range K H e

local instance localWeilFixedFieldOpenImage_finite
    (e : SeparableClosure F ≃ₐ[F] Ω) :
    Finite (localWeilGroup K ⧸
      (localWeilFixedFieldOpenImage K H e : Subgroup (localWeilGroup K))) := by
  apply Nat.finite_of_card_ne_zero
  change (localWeilFixedFieldInclusion K H e).toMonoidHom.range.index ≠ 0
  rw [localWeilFixedFieldInclusion_index K H e]
  exact Module.finrank_pos.ne'

/-- The transfer in the opposite direction is the continuous group transfer
for the actual open Weil image. -/
noncomputable def localWeilFixedFieldTransfer
    (e : SeparableClosure F ≃ₐ[F] Ω) :
    TopologicalAbelianization (localWeilGroup K) →ₜ*
      TopologicalAbelianization (localWeilGroup F) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (TopologicalAbelianization.congr (localWeilFixedFieldInclusionEquivRange K H e).symm)).comp
      (openSubgroupTransfer (localWeilFixedFieldOpenImage K H e))

/-- Weil and absolute transfer agree on the same Weil representative. -/
theorem localWeilFixedFieldTransfer_toAbsolute
    (e : SeparableClosure F ≃ₐ[F] Ω)
    (z : TopologicalAbelianization (localWeilGroup K)) :
    localWeilAbelianizationToAbsolute F (localWeilFixedFieldTransfer K H e z) =
      localFixedFieldAbsoluteTransfer K H e (localWeilAbelianizationToAbsolute K z) := by
  let W := localWeilFixedFieldOpenImage K H e
  let : IsTopologicalGroup W :=
    inferInstanceAs (IsTopologicalGroup ↥(W : Subgroup (localWeilGroup K)))
  let B := localFixedFieldOpenSubgroup K H
  let : IsTopologicalGroup B :=
    inferInstanceAs (IsTopologicalGroup ↥(B : Subgroup (Gal(Ω/K))))
  let f := localWeilToAbsolute K
  let wEquiv := localWeilFixedFieldInclusionEquivRange K H e
  let bEquiv := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K (SeparableClosure K) H e
  have hcomap : (B : Subgroup Gal(Ω/K)).comap f.toMonoidHom =
      (W : Subgroup (localWeilGroup K)) :=
    (localWeilFixedFieldInclusion_range K H e).symm
  have hm (w : W) : f w.1 ∈ (B : Subgroup Gal(Ω/K)) :=
    show w.1 ∈ (B : Subgroup Gal(Ω/K)).comap f.toMonoidHom from hcomap.symm ▸ w.property
  let fW : W →ₜ* B :=
    { toMonoidHom := (f.toMonoidHom.comp (W : Subgroup (localWeilGroup K)).subtype).codRestrict
        (B : Subgroup Gal(Ω/K)) hm
      continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk hm }
  have hinverse (w : W) :
      localWeilToAbsolute F (wEquiv.symm w) = bEquiv.symm (fW w) := by
    apply bEquiv.injective
    apply Subtype.ext
    let z := wEquiv.symm w
    have hw := congrArg Subtype.val (wEquiv.apply_symm_apply w)
    have hb := localFixedFieldAbsoluteInclusion_eq_subtype K H e (localWeilToAbsolute F z)
    have ha := localWeilFixedFieldInclusion_absolute K H e z
    have hEq := congrArg (fun u : B => u.val) (bEquiv.apply_symm_apply (fW w))
    exact hb.symm.trans (ha.symm.trans ((congrArg f hw).trans hEq.symm))
  have hmap (x : TopologicalAbelianization W) :
      localWeilAbelianizationToAbsolute F (TopologicalAbelianization.congr wEquiv.symm x) =
        TopologicalAbelianization.congr bEquiv.symm (TopologicalAbelianization.map fW x) := by
    exact abelianizedSquare_apply (ContinuousMonoidHom.toContinuousMonoidHom wEquiv.symm) fW
      (localWeilToAbsolute F) (ContinuousMonoidHom.toContinuousMonoidHom bEquiv.symm) hinverse x
  change localWeilAbelianizationToAbsolute F
      (TopologicalAbelianization.congr wEquiv.symm (openSubgroupTransfer W z)) =
    TopologicalAbelianization.congr bEquiv.symm
      (openSubgroupTransfer B (TopologicalAbelianization.map f z))
  have hTransfer := openSubgroupTransfer_natural_of_coset_surjective W B f hcomap
    (localWeilToAbsolute_fixingCoset_surjective K H) fW (fun _ => rfl) z
  exact (hmap (openSubgroupTransfer W z)).trans
    (congrArg (TopologicalAbelianization.congr bEquiv.symm) hTransfer)

/-- The transfer of a Weil class multiplies the discrete degree by the
actual ramification index. -/
theorem localWeilFixedFieldTransfer_degree
    (e : SeparableClosure F ≃ₐ[F] Ω)
    (x : TopologicalAbelianization (localWeilGroup K)) :
    let : Valuation.HasExtension
        (ValuativeRel.valuation K) (ValuativeRel.valuation F) :=
      finiteExtensionSpectralValuation_hasExtension K F
    (localWeilAbelianizationDegree F (localWeilFixedFieldTransfer K H e x)).toAdd =
      Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[F] : Ideal 𝒪[F]) •
        (localWeilAbelianizationDegree K x).toAdd := by
  intro hVal
  let hInt : IsIntegralClosure 𝒪[F] 𝒪[K] F :=
    localCompleteDVF_integerRing_isIntegralClosure K F
  let W := localWeilFixedFieldOpenImage K H e
  let : IsTopologicalGroup W :=
    inferInstanceAs (IsTopologicalGroup ↥(W : Subgroup (localWeilGroup K)))
  let k := localWeilFixedFieldInclusionEquivRange K H e
  let d := H.residueDegree (localResidueDatum K)
  let r := Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[F] : Ideal 𝒪[F])
  let i : W →ₜ* localWeilGroup K :=
    ⟨(W : Subgroup (localWeilGroup K)).subtype, continuous_subtype_val⟩
  let compare := TopologicalAbelianization.congr k.symm
  let dW := TopologicalAbelianization.lift ((localWeilDegree K).comp i)
  let P (z : TopologicalAbelianization W) :=
    (dW z).toAdd = (d : ℕ) • (localWeilAbelianizationDegree F (compare z)).toAdd
  have hW_mk (w : W) : P (TopologicalAbelianization.mk W w) := by
    have hw : localWeilFixedFieldInclusion K H e (k.symm w) = w.1 :=
      congrArg Subtype.val (k.apply_symm_apply w)
    change (localWeilDegree K w.1).toAdd = (d : ℕ) • (localWeilDegree F (k.symm w)).toAdd
    have he := congrArg (fun w : localWeilGroup K => (localWeilDegree K w).toAdd) hw
    exact he.symm.trans (localWeilFixedFieldInclusion_degree K H e (k.symm w))
  have hW : ∀ p : TopologicalAbelianization W, P p :=
    (TopologicalAbelianization.surjective_mk W).forall.mpr hW_mk
  have hrf : r * (d : ℕ) = Module.finrank K F := by
    change r * (H.residueDegree (localResidueDatum K) : ℕ) = _
    rw [localResidueDatum_residueDegree_eq_residueFinrank K H]
    exact @maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure
      K F _ _ _ _ _ _ _ _ _ _ _ hVal hInt
  let P₀ (y : TopologicalAbelianization (localWeilGroup K)) :=
    (localWeilAbelianizationDegree F (localWeilFixedFieldTransfer K H e y)).toAdd =
      r • (localWeilAbelianizationDegree K y).toAdd
  have hmk (w : localWeilGroup K) : P₀ (TopologicalAbelianization.mk (localWeilGroup K) w) := by
    let p := openSubgroupTransfer W (TopologicalAbelianization.mk (localWeilGroup K) w)
    have h := congrArg Multiplicative.toAdd
      (openSubgroupTransfer_character W (Multiplicative ℤ) (localWeilDegree K) w)
    change (dW p).toAdd =
      (W : Subgroup (localWeilGroup K)).index • (localWeilDegree K w).toAdd at h
    have h := (hW p).symm.trans h
    change (d : ℕ) • (localWeilAbelianizationDegree F (compare p)).toAdd =
      (localWeilFixedFieldInclusion K H e).toMonoidHom.range.index •
        (localWeilDegree K w).toAdd at h
    let z : ℤ := (localWeilDegree K w).toAdd
    have hIndex : (localWeilFixedFieldInclusion K H e).toMonoidHom.range.index =
        (d : ℕ) * r :=
      (localWeilFixedFieldInclusion_index K H e).trans (hrf.symm.trans (Nat.mul_comm _ _))
    have hScalar := (congrArg (fun n : ℕ => n • z) hIndex).trans (mul_smul (d : ℕ) r z)
    have hd : ((d : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr d.ne_zero
    let degF (a : TopologicalAbelianization (localWeilGroup F)) : ℤ :=
      (localWeilAbelianizationDegree F a).toAdd
    have hcancel : degF (compare p) = r • z :=
      mul_left_cancel₀ hd (by simpa only [nsmul_eq_mul] using h.trans hScalar)
    have hlf : localWeilFixedFieldTransfer K H e (TopologicalAbelianization.mk (localWeilGroup K) w)
        = compare p := rfl
    have hlk : (localWeilAbelianizationDegree K
        (TopologicalAbelianization.mk (localWeilGroup K) w)).toAdd = z := rfl
    exact (congrArg degF hlf).trans (hcancel.trans (congrArg (r • ·) hlk.symm))
  exact ((TopologicalAbelianization.surjective_mk (localWeilGroup K)).forall.mpr hmk) x

end
end LocalClassFieldTheory
