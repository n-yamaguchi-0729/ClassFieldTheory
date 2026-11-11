/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The rationality proof adapts the existing NYLL owner corresponding to:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_isRational_pointEquivPlace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/
module

public import Nyll.AlgebraicCurves.Places.ValuationRings.IsRationalRangeStalkSectionEq
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictEqMem
public import Nyll.AlgebraicCurves.Places.Restriction.OrdAlgebraMapEqOrdComapEq
public import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncConstantExtensionOrders

/-! # Actual rational section boundary places under constant extension


The geometric place is the point obtained by lifting the original rational
section through the actual base-change square. Its arithmetic order comparison
is derived from stalk functoriality, integrality, and separability of constants.
In particular, no inertia-preservation or order-comparison assumption is used.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace AlgebraicCurve.CurveModel

universe u v

/-- A specified rational section gives a rational place over any base field.
This does not require the base field to be algebraically closed. -/
theorem isRational_placeOfPoint_of_section
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (M : CurveModel k F) (σ : Spec (.of k) ⟶ M.C)
    (hσ : σ ≫ M.toBase = 𝟙 _)
    (x : closedPoints M.C) (hx : x.val = σ (IsLocalRing.closedPoint k)) :
    (M.placeOfPoint x).IsRational := by
  let : Algebra k M.C.functionField := M.functionFieldAlgebra
  let V := M.placeOfPoint x
  have hff : ∀ a : k, M.ffEquiv (algebraMap k F a) =
      algebraMap k M.C.functionField a := M.ffEquiv_algebraMap
  have hr : (Place.congrRingEquiv M.ffEquiv hff V).IsRational := by
    apply Place.isRational_of_range_stalk_section_eq M.toBase σ hσ
    rw [Place.congrRingEquiv_toValuationSubring]
    have h := M.range_stalk_eq x
    rw [hx] at h
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      change M.ffEquiv.symm (algebraMap _ M.C.functionField s) ∈
        V.toValuationSubring.toSubring
      rw [← h]
      exact ⟨s, rfl⟩
    · intro hg
      change M.ffEquiv.symm g ∈ V.toValuationSubring.toSubring at hg
      rw [← h] at hg
      obtain ⟨s, hs⟩ := hg
      exact ⟨s, M.ffEquiv.symm.injective hs⟩
  intro r
  obtain ⟨a, ha⟩ := hr (Place.congrResidueAlgEquiv M.ffEquiv hff V r)
  refine ⟨a, (Place.congrResidueAlgEquiv M.ffEquiv hff V).injective ?_⟩
  rw [AlgEquiv.commutes]
  exact ha

/-- Stalk functoriality places every arithmetic local function in the
valuation ring at the actual corresponding geometric closed point. -/
theorem placeOfPoint_le_comap_of_functionFieldMap
    {k κ F E : Type u} [Field k] [Field κ] [Field F] [Field E]
    [Algebra k F] [Algebra κ E] [Algebra F E]
    (M₀ : CurveModel k F) (M : CurveModel κ E)
    (f : M.C ⟶ M₀.C) (hf : DenseRange f)
    (hfield : ∀ z : F,
      f.functionFieldMap hf (M₀.ffEquiv z) = M.ffEquiv (algebraMap F E z))
    (y : closedPoints M.C) (hy : IsClosed ({f y.val} : Set M₀.C)) :
    (M₀.placeOfPoint ⟨f y.val, hy⟩).toValuationSubring ≤
      (M.placeOfPoint y).toValuationSubring.comap (algebraMap F E) := by
  intro z hz
  have hz' : z ∈ ((M₀.ffEquiv.symm : M₀.C.functionField ≃+* F).toRingHom.comp
      (algebraMap (M₀.C.presheaf.stalk (f y.val)) M₀.C.functionField)).range := by
    rw [M₀.range_stalk_eq ⟨f y.val, hy⟩]
    exact hz
  obtain ⟨t, ht⟩ := hz'
  have ht' : M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t) = z := ht
  have hnat : algebraMap F E (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t)) =
      M.ffEquiv.symm (algebraMap _ M.C.functionField (f.stalkMap y.val t)) := by
    apply M.ffEquiv.injective
    rw [RingEquiv.apply_symm_apply, ← hfield, RingEquiv.apply_symm_apply]
    exact f.functionFieldMap_algebraMap_stalk hf y.val t
  change algebraMap F E z ∈ (M.placeOfPoint y).toValuationSubring.toSubring
  rw [← ht', hnat, ← M.range_stalk_eq y]
  exact ⟨f.stalkMap y.val t, rfl⟩

/-- For rational function fields, the one-sided stalk inclusion already
forces exact normalized order compatibility. -/
theorem ratFunc_ord_eq_of_place_le_comap
    {k κ : Type u} [Field k] [Field κ] [Algebra k κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    (V : Place k (RatFunc k)) (W : Place κ (RatFunc κ))
    (hmem : V.toValuationSubring ≤
      W.toValuationSubring.comap (algebraMap (RatFunc k) (RatFunc κ))) :
    ∀ z : RatFunc k, W.ord (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z := by
  let : Algebra.IsIntegral (RatFunc k) (RatFunc κ) :=
    ratFunc_constantExtension_isIntegral (k := k) (L := κ)
  have hr := Place.restrict_eq_of_forall_mem V (W.forgetConstants (K := k))
    (fun z hz => hmem hz)
  have hc : W.toValuationSubring.comap (algebraMap (RatFunc k) (RatFunc κ)) =
      V.toValuationSubring := by
    have h := congrArg Place.toValuationSubring hr
    simpa only [Place.restrict_toValuationSubring,
      Place.forgetConstants_toValuationSubring] using h
  exact Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top
    (ratFunc_constantExtension_adjoin_eq_top (k := k) (L := κ)) V W hc

/-- Construct the actual source cusp for an omitted rational section,
including a section at infinity. The function-field chart is the only field
comparison input; normalized orders are a conclusion. -/
theorem exists_rational_section_boundaryPlace_ord_eq
    {k κ : Type u} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    (M₀ : CurveModel k (RatFunc k)) (M : CurveModel κ (RatFunc κ))
    (eC : M.C ≅ pullback M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap k κ))))
    (heC : eC.hom ≫ pullback.snd M₀.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) = M.toBase)
    (hπ : DenseRange (eC.hom ≫ pullback.fst M₀.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))))
    (hchart : ∀ z : RatFunc k,
      (eC.hom ≫ pullback.fst M₀.toBase
        (Spec.map (CommRingCat.ofHom (algebraMap k κ)))).functionFieldMap hπ
        (M₀.ffEquiv z) = M.ffEquiv (algebraMap (RatFunc k) (RatFunc κ) z))
    {X U : Scheme.{u}} (i : X ⟶ M₀.C) (j : U ⟶ M.C) (q : U ⟶ X)
    (hproj : j ≫ eC.hom ≫ pullback.fst M₀.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) = q ≫ i)
    (σ : Spec (.of k) ⟶ M₀.C) (hσ : σ ≫ M₀.toBase = 𝟙 _)
    (hclosed : IsClosed ({σ (IsLocalRing.closedPoint k)} : Set M₀.C))
    (houtside : σ (IsLocalRing.closedPoint k) ∉ Set.range i) :
    ∃ V : Place k (RatFunc k), V.IsRational ∧
      ∃ p : M.openBoundaryPlaces j,
        (eC.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap k κ))))
          (M.placeEquiv.symm p.val).val = σ (IsLocalRing.closedPoint k) ∧
        ∀ z : RatFunc k,
          p.val.ord (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z := by
  let τ₀ : Spec (.of κ) ⟶ pullback M₀.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k κ)) ≫ σ) (𝟙 _)
      (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  let τ : Spec (.of κ) ⟶ M.C := τ₀ ≫ eC.inv
  have hτ : τ ≫ M.toBase = 𝟙 _ := by
    dsimp only [τ]
    rw [Category.assoc, ← heC, eC.inv_hom_id_assoc]
    exact pullback.lift_snd _ _ _
  have hτπ : τ ≫ eC.hom ≫ pullback.fst M₀.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) =
        Spec.map (CommRingCat.ofHom (algebraMap k κ)) ≫ σ := by
    dsimp only [τ]
    rw [Category.assoc, eC.inv_hom_id_assoc]
    exact pullback.lift_fst _ _ _
  let y : closedPoints M.C := pointEquivClosedPoint M.toBase ⟨τ, hτ⟩
  let π := eC.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
  have hcenter : π y.val = σ (IsLocalRing.closedPoint k) := by
    have h := congrArg (fun g : Spec (.of κ) ⟶ M₀.C => g (IsLocalRing.closedPoint κ)) hτπ
    change π (τ (IsLocalRing.closedPoint κ)) =
      σ (Spec.map (CommRingCat.ofHom (algebraMap k κ)) (IsLocalRing.closedPoint κ)) at h
    change π (τ (IsLocalRing.closedPoint κ)) = σ (IsLocalRing.closedPoint k)
    exact h.trans (congrArg σ (Subsingleton.elim _ _))
  have hy : IsClosed ({π y.val} : Set M₀.C) := by rw [hcenter]; exact hclosed
  let x : closedPoints M₀.C := ⟨π y.val, hy⟩
  let V := M₀.placeOfPoint x
  have hV : V.IsRational := M₀.isRational_placeOfPoint_of_section σ hσ x hcenter
  have hb : M.placeOfPoint y ∈ M.openBoundaryPlaces j := by
    change (M.placeEquiv.symm (M.placeOfPoint y)).val ∉ Set.range j
    rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
    rintro ⟨u, hu⟩
    apply houtside
    refine ⟨q u, ?_⟩
    have hs := congrArg (fun g : U ⟶ M₀.C => g u) hproj
    change π (j u) = i (q u) at hs
    exact hs.symm.trans ((congrArg π hu).trans hcenter)
  let p : M.openBoundaryPlaces j := ⟨M.placeOfPoint y, hb⟩
  refine ⟨V, hV, p, ?_, ?_⟩
  · change π (M.placeEquiv.symm (M.placeOfPoint y)).val = _
    rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
    exact hcenter
  · exact ratFunc_ord_eq_of_place_le_comap V (M.placeOfPoint y)
      (M₀.placeOfPoint_le_comap_of_functionFieldMap M π hπ hchart y hy)

end AlgebraicCurve.CurveModel
