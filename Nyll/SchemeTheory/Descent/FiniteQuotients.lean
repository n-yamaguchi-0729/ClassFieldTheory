/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Nyll.SchemeTheory.Morphisms.SeparatedQuasiCompactDescent
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Nyll.SchemeTheory.Descent.AffineFiniteLocallyFreeQuotient
public import Nyll.SchemeTheory.Descent.FiniteLocallyFreeQuotientBaseChange
public import Nyll.SchemeTheory.Descent.QuotientOverlapCocycle

/-!
# Finite quotients and invariant affine neighborhoods

Glue local fppf quotients, construct invariant affine neighborhoods for finite locally free
relations, and descend invariant affine opens through the quotient map.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_fppf_quotient_of_forall_exists_quotient_restrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace

universe u
namespace SchemeTheory.Descent.QuotientGluing

theorem AlgebraicGeometry.Scheme.quotient_baseChange_of_fppf_of_isPullback
    {X R Y X' R' Y' : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}
    [QuasiCompact p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p)
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {gX : X' ⟶ X} (hX : IsPullback gX p' p g)
    {s' t' : R' ⟶ X'} {gR : R' ⟶ R} (hsq : IsPullback gR s' s gX) (htq : gR ≫ t = t' ≫ gX)
    (w' : s' ≫ p' = t' ≫ p') :
    QuasiCompact p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) := by
  have : QuasiCompact p' := MorphismProperty.of_isPullback (P := @QuasiCompact) hX inferInstance
  have : Flat p' := MorphismProperty.of_isPullback (P := @Flat) hX inferInstance
  have : LocallyOfFinitePresentation p' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hX inferInstance
  have : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hX inferInstance
  have hker : IsPullback s' t' p' p' := by
    refine IsPullback.of_isLimit' ⟨w'⟩ (PullbackCone.IsLimit.mk _ (fun c => ?_) (fun c => ?_)
      (fun c => ?_) (fun c m hm₁ hm₂ => ?_))
    · refine hsq.lift (hR.lift (c.fst ≫ gX) (c.snd ≫ gX) ?_) c.fst ?_
      · rw [Category.assoc, Category.assoc, hX.w, ← Category.assoc, ← Category.assoc, c.condition]
      · rw [IsPullback.lift_fst]
    · exact hsq.lift_snd _ _ _
    · apply hX.hom_ext
      · rw [Category.assoc, ← htq, ← Category.assoc, hsq.lift_fst, hR.lift_snd]
      · rw [Category.assoc, ← w', ← Category.assoc, hsq.lift_snd, c.condition]
    · apply hsq.hom_ext
      · rw [hsq.lift_fst]
        apply hR.hom_ext
        · rw [IsPullback.lift_fst, Category.assoc, hsq.w, ← Category.assoc, hm₁]
        · rw [IsPullback.lift_snd, Category.assoc, htq, ← Category.assoc, hm₂]
      · rw [hsq.lift_snd]
        exact hm₁
  have hk : IsKernelPair p' s' t' := hker
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hker, ⟨?_⟩⟩
  exact hk.toCoequalizer (regularEpiOfEffectiveEpi p')
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace GlueData
open _root_.AlgebraicGeometry.Scheme.GlueData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

/-- Open-chart gluing data with a cocycle on triple intersections. -/
structure MkCore where

  /-- The chart index type. -/
  {J : Type u}
  /-- The schemes to be glued. -/
  U : J → Scheme.{u}
  /-- The transition domains. -/
  V : ∀ i, J → (U i).Opens
  /-- The transition morphisms. -/
  t : ∀ i j, (V i j : Scheme.{u}) ⟶ (V j i : Scheme.{u})
  /-- Each chart overlaps itself everywhere. -/
  V_id : ∀ i, V i i = ⊤
  /-- The diagonal transition is the identity. -/
  t_id : ∀ i, t i i = 𝟙 _
  /-- Transitions preserve triple intersections. -/
  t_inter : ∀ i j k, (V i j).ι ⁻¹ᵁ (V i k) ≤ t i j ⁻¹ᵁ ((V j i).ι ⁻¹ᵁ (V j k))
  /-- The transition cocycle equation. -/
  cocycle : ∀ i j k,
    (t i j).resLE ((V j i).ι ⁻¹ᵁ (V j k)) ((V i j).ι ⁻¹ᵁ (V i k)) (t_inter i j k) ≫
      ((U j).restrictRestrictComm (V j i) (V j k)).hom ≫ ((V j k).ι ⁻¹ᵁ (V j i)).ι ≫
        t j k ≫ (V k j).ι =
    ((U i).restrictRestrictComm (V i j) (V i k)).hom ≫ ((V i k).ι ⁻¹ᵁ (V i j)).ι ≫
      t i k ≫ (V k i).ι
namespace MkCore

variable (h : MkCore.{u})

/-- The overlap of two chart domains inside a third chart. -/
abbrev W (i j k : h.J) : (h.V i j : Scheme.{u}).Opens := (h.V i j).ι ⁻¹ᵁ (h.V i k)

/-- The transition map restricted to a triple overlap. -/
noncomputable abbrev τ (i j k : h.J) : (h.W i j k : Scheme.{u}) ⟶ (h.W j i k : Scheme.{u}) :=
  (h.t i j).resLE (h.W j i k) (h.W i j k) (h.t_inter i j k)

/-- Exchange the two restrictions defining a triple overlap. -/
noncomputable abbrev σ (i j k : h.J) : (h.W i j k : Scheme.{u}) ≅ (h.W i k j : Scheme.{u}) :=
  (h.U i).restrictRestrictComm (h.V i j) (h.V i k)

@[reassoc]
lemma σ_hom_ι_ι (i j k : h.J) :
    (h.σ i j k).hom ≫ (h.W i k j).ι ≫ (h.V i k).ι = (h.W i j k).ι ≫ (h.V i j).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc]
lemma σ_hom_σ_hom (i j k : h.J) : (h.σ i j k).hom ≫ (h.σ i k j).hom = 𝟙 _ := by
  rw [← cancel_mono ((h.W i j k).ι ≫ (h.V i j).ι), Category.assoc, σ_hom_ι_ι, σ_hom_ι_ι,
    Category.id_comp]

@[reassoc]
lemma σ_self_hom_ι (i j : h.J) : (h.σ j i i).hom ≫ (h.W j i i).ι = (h.W j i i).ι := by
  rw [← cancel_mono (h.V j i).ι, Category.assoc, σ_hom_ι_ι]

@[reassoc]
lemma τ_ι (i j k : h.J) : h.τ i j k ≫ (h.W j i k).ι = (h.W i j k).ι ≫ h.t i j :=
  Scheme.Hom.resLE_comp_ι _ _

lemma cocycle' (i j k : h.J) :
    h.τ i j k ≫ (h.σ j i k).hom ≫ (h.W j k i).ι ≫ h.t j k ≫ (h.V k j).ι =
      (h.σ i j k).hom ≫ (h.W i k j).ι ≫ h.t i k ≫ (h.V k i).ι :=
  h.cocycle i j k

lemma W_self (i j : h.J) : h.W i j i = ⊤ := by
  change (h.V i j).ι ⁻¹ᵁ h.V i i = ⊤
  rw [h.V_id]
  rfl

scoped instance (i j : h.J) : IsIso (h.W i j i).ι := by
  rw [show (h.W i j i).ι = ((h.V i j : Scheme.{u}).isoOfEq (h.W_self i j)).hom ≫
      (⊤ : (h.V i j : Scheme.{u}).Opens).ι from ((h.V i j : Scheme.{u}).isoOfEq_hom_ι _).symm]
  have : IsIso (⊤ : (h.V i j : Scheme.{u}).Opens).ι := (Scheme.topIso _).isIso_hom
  infer_instance

@[reassoc (attr := simp)]
lemma t_inv (i j : h.J) : h.t i j ≫ h.t j i = 𝟙 _ := by
  have c := h.cocycle' i j i
  rw [h.t_id, Category.id_comp, σ_hom_ι_ι, σ_self_hom_ι_assoc, τ_ι_assoc] at c
  rw [← cancel_epi (h.W i j i).ι, ← cancel_mono (h.V i j).ι]
  simpa only [Category.assoc, Category.comp_id] using c

scoped instance (i j : h.J) : IsIso (h.t i j) := ⟨h.t j i, h.t_inv i j, h.t_inv j i⟩

/-- Identify an intersection pullback with its open restriction. -/
noncomputable abbrev isoW (i j k : h.J) :
    pullback (h.V i j).ι (h.V i k).ι ≅ (h.W i j k : Scheme.{u}) :=
  pullbackRestrictIsoRestrict (h.V i j).ι (h.V i k)

/-- The transition map between the two pullbacks in the gluing cocycle. -/
noncomputable def t' (i j k : h.J) :
    pullback (h.V i j).ι (h.V i k).ι ⟶ pullback (h.V j k).ι (h.V j i).ι :=
  (h.isoW i j k).hom ≫ h.τ i j k ≫ (h.σ j i k).hom ≫ (h.isoW j k i).inv

lemma core (i j k : h.J) :
    h.τ i j k ≫ (h.σ j i k).hom ≫ h.τ j k i ≫ (h.σ k j i).hom ≫ h.τ k i j ≫ (h.σ i k j).hom =
      𝟙 _ := by
  rw [← cancel_mono ((h.W i j k).ι ≫ (h.V i j).ι)]
  simp only [Category.assoc, Category.id_comp]
  rw [σ_hom_ι_ι, τ_ι_assoc, h.cocycle' j k i, σ_hom_σ_hom_assoc, τ_ι_assoc, t_inv_assoc]

/-- Convert open-overlap data to the canonical scheme gluing data. -/
noncomputable def glueData : Scheme.GlueData.{u} where
  J := h.J
  U := h.U
  V ij := h.V ij.1 ij.2
  f i j := (h.V i j).ι
  f_id i := h.V_id i ▸ (Scheme.topIso (h.U i)).isIso_hom
  f_open i j := inferInstance
  t := h.t
  t_id := h.t_id
  t' := h.t'
  t_fac i j k := by
    change h.t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ h.t i j
    rw [t', Category.assoc, Category.assoc, Category.assoc, ← pullbackRestrictIsoRestrict_hom_ι,
      Category.assoc, cancel_epi, ← cancel_mono (h.V j i).ι]
    change h.τ i j k ≫ (h.σ j i k).hom ≫ ((h.V j k).ι ∣_ h.V j i) ≫ (h.V j i).ι = _
    rw [morphismRestrict_ι, σ_hom_ι_ι, Category.assoc, τ_ι_assoc]
  cocycle i j k := by
    change h.t' i j k ≫ h.t' j k i ≫ h.t' k i j = 𝟙 _
    simp only [t', Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (h.core i j k), Iso.hom_inv_id]

@[scoped simp]
lemma glueData_J : h.glueData.J = h.J := rfl
@[scoped simp]
lemma glueData_U (i : h.J) : h.glueData.U i = h.U i := rfl
@[scoped simp]
lemma glueData_V (i j : h.J) : h.glueData.V (i, j) = (h.V i j : Scheme.{u}) := rfl
@[scoped simp]
lemma glueData_f (i j : h.J) : h.glueData.f i j = (h.V i j).ι := rfl
@[scoped simp]
lemma glueData_t (i j : h.J) : h.glueData.t i j = h.t i j := rfl

lemma t_ι_ι (i j : h.J) :
    h.t i j ≫ (h.V j i).ι ≫ h.glueData.ι j = (h.V i j).ι ≫ h.glueData.ι i :=
  h.glueData.glue_condition i j

scoped instance (i : h.J) : IsOpenImmersion (h.glueData.ι i) :=
  _root_.AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion h.glueData
    (show h.glueData.J from i)

lemma preimage_opensRange (i j : h.J) :
    (h.glueData.ι i) ⁻¹ᵁ (h.glueData.ι j).opensRange = h.V i j := by
  have hP := h.glueData.vPullbackConeIsLimit i j
  let e := hP.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ pullback.fst (h.glueData.ι i) (h.glueData.ι j) = (h.V i j).ι :=
    hP.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingCospan.left
  have hrange : Set.range (pullback.fst (h.glueData.ι i) (h.glueData.ι j)) =
      (h.V i j : Set (h.U i)) := by
    rw [← Scheme.Opens.range_ι (h.V i j), ← he]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := (Scheme.homeoOfIso e).surjective a
      exact ⟨b, (Scheme.Hom.comp_apply _ _ b).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨e.hom b, (Scheme.Hom.comp_apply _ _ b).symm⟩
  ext1
  exact (Scheme.Pullback.range_fst (h.glueData.ι i) (h.glueData.ι j)).symm.trans hrange
end MkCore
end AlgebraicGeometry.Scheme.GlueData
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace QuotGlue
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Saturation

variable {X Y R : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}

lemma preimage_image_eq (hR : IsPullback s t p p) (O : X.Opens) (hO : s ⁻¹ᵁ O = t ⁻¹ᵁ O) :
    p ⁻¹' (p '' (O : Set X)) = O := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro x ⟨o, ho, hox⟩
  obtain ⟨r, hrs, hrt⟩ := Scheme.exists_preimage_of_isPullback hR x o hox.symm
  have : r ∈ t ⁻¹ᵁ O := by change t r ∈ O; rw [hrt]; exact ho
  rw [← hO] at this
  change s r ∈ O at this
  rwa [hrs] at this

lemma isOpen_image [Flat p] [LocallyOfFinitePresentation p]
    (O : X.Opens) : IsOpen (p '' (O : Set X)) :=
  p.isOpenMap _ O.2

/-- The open image under a flat morphism of finite presentation. -/
def imageOpens [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) : Y.Opens :=
  ⟨p '' (O : Set X), isOpen_image O⟩

@[scoped simp]
lemma coe_imageOpens [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) :
    (imageOpens (p := p) O : Set Y) = p '' (O : Set X) := rfl

lemma preimage_imageOpens (hR : IsPullback s t p p) [Flat p] [LocallyOfFinitePresentation p]
    (O : X.Opens) (hO : s ⁻¹ᵁ O = t ⁻¹ᵁ O) : p ⁻¹ᵁ imageOpens (p := p) O = O :=
  Opens.ext (preimage_image_eq hR O hO)

lemma imageOpens_top [Flat p] [LocallyOfFinitePresentation p] [Surjective p] :
    imageOpens (p := p) ⊤ = ⊤ :=
  Opens.ext (by
    change p '' Set.univ = Set.univ
    rw [Set.image_univ, p.surjective.range_eq])

lemma le_imageOpens_iff [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) (x : X) (hx : x ∈ O)
    :
    p x ∈ imageOpens (p := p) O :=
  ⟨x, hx, rfl⟩
end Saturation

section RestrictPkg

variable {X Y R : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}

lemma preimage_preimage_eq (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    s ⁻¹ᵁ (p ⁻¹ᵁ U) = t ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  change (s ≫ p) ⁻¹ᵁ U = (t ≫ p) ⁻¹ᵁ U
  rw [hw]

/-- Restrict the second relation map to a saturated open subset. -/
noncomputable def tRes (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    (s ⁻¹ᵁ (p ⁻¹ᵁ U) : Scheme.{u}) ⟶ (p ⁻¹ᵁ U : Scheme.{u}) :=
  (R.isoOfEq (preimage_preimage_eq hw U)).hom ≫ (t ∣_ (p ⁻¹ᵁ U))

@[reassoc]
lemma tRes_ι (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    tRes hw U ≫ (p ⁻¹ᵁ U).ι = (s ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ t := by
  rw [tRes, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

lemma sRes_w (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    (s ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U) = tRes hw U ≫ (p ∣_ U) := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    morphismRestrict_ι_assoc, tRes_ι_assoc, hw]

theorem restrict_pkg (hw : s ≫ p = t ≫ p) [QuasiCompact p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] (hR : IsPullback s t p p) (U : Y.Opens) :
    QuasiCompact (p ∣_ U) ∧ Flat (p ∣_ U) ∧ LocallyOfFinitePresentation (p ∣_ U) ∧
      Surjective (p ∣_ U) ∧ IsPullback (s ∣_ (p ⁻¹ᵁ U)) (tRes hw U) (p ∣_ U) (p ∣_ U) ∧
      Nonempty (IsColimit (Cofork.ofπ (p ∣_ U) (sRes_w hw U))) :=
  Scheme.quotient_baseChange_of_fppf_of_isPullback hR
    (isPullback_morphismRestrict p U).flip (isPullback_morphismRestrict s (p ⁻¹ᵁ U)).flip
    (tRes_ι hw U).symm (sRes_w hw U)
end RestrictPkg

section Compare

variable {R₁ X₁ Y₁ R₂ X₂ Y₂ : Scheme.{u}} {s₁ t₁ : R₁ ⟶ X₁} {s₂ t₂ : R₂ ⟶ X₂}
  {p₁ : X₁ ⟶ Y₁} {p₂ : X₂ ⟶ Y₂} {w₁ : s₁ ≫ p₁ = t₁ ≫ p₁} {w₂ : s₂ ≫ p₂ = t₂ ≫ p₂}

/-- The canonical isomorphism between coequalizers of isomorphic relations. -/
noncomputable def quotIso (h₁ : IsColimit (Cofork.ofπ p₁ w₁)) (h₂ : IsColimit (Cofork.ofπ p₂ w₂))
    (eR : R₁ ≅ R₂) (eX : X₁ ≅ X₂) (hs : s₁ ≫ eX.hom = eR.hom ≫ s₂) (ht : t₁ ≫ eX.hom = eR.hom ≫ t₂)
      :
    Y₁ ≅ Y₂ :=
  IsColimit.coconePointsIsoOfNatIso h₁ h₂ (parallelPair.ext eR eX hs ht)

@[reassoc]
lemma π_quotIso_hom (h₁ : IsColimit (Cofork.ofπ p₁ w₁)) (h₂ : IsColimit (Cofork.ofπ p₂ w₂))
    (eR : R₁ ≅ R₂) (eX : X₁ ≅ X₂) (hs : s₁ ≫ eX.hom = eR.hom ≫ s₂) (ht : t₁ ≫ eX.hom = eR.hom ≫ t₂)
      :
    p₁ ≫ (quotIso h₁ h₂ eR eX hs ht).hom = eX.hom ≫ p₂ := by
  exact IsColimit.comp_coconePointsIsoOfNatIso_hom h₁ h₂ (parallelPair.ext eR eX hs ht)
    WalkingParallelPair.one
end Compare

section Main

variable {X R : Scheme.{u}} (s t : R ⟶ X) (W : X → X.Opens) (hxW : ∀ x, x ∈ W x)
  (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)

/-- Restrict the second relation map to an invariant chart. -/
noncomputable abbrev tW (x : X) : (s ⁻¹ᵁ W x : Scheme.{u}) ⟶ (W x : Scheme.{u}) :=
  (R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)

@[reassoc]
lemma tW_ι (x : X) : tW s t W hinv x ≫ (W x).ι = (s ⁻¹ᵁ W x).ι ≫ t := by
  rw [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

variable (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      QuasiCompact p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

/-- Choose the local quotient scheme on a chart. -/
noncomputable def Yloc (x : X) : Scheme.{u} := (loc x).choose

/-- The chosen local quotient morphism. -/
noncomputable def ploc (x : X) : (W x : Scheme.{u}) ⟶ Yloc s t W hinv loc x :=
  (loc x).choose_spec.choose
lemma ploc_spec (x : X) :
    (s ∣_ W x) ≫ ploc s t W hinv loc x = tW s t W hinv x ≫ ploc s t W hinv loc x ∧
      QuasiCompact (ploc s t W hinv loc x) ∧ Flat (ploc s t W hinv loc x) ∧
      LocallyOfFinitePresentation (ploc s t W hinv loc x) ∧ Surjective (ploc s t W hinv loc x) ∧
      IsPullback (s ∣_ W x) (tW s t W hinv x) (ploc s t W hinv loc x) (ploc s t W hinv loc x) :=
  (loc x).choose_spec.choose_spec

scoped instance (x : X) : QuasiCompact (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc x).2.1
scoped instance (x : X) : Flat (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc x).2.2.1
scoped instance (x : X) : LocallyOfFinitePresentation (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.2.1
scoped instance (x : X) : Surjective (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc
    x).2.2.2.2.1

lemma inv_overlap (x y : X) :
    (s ∣_ W x) ⁻¹ᵁ ((W x).ι ⁻¹ᵁ W y) = (tW s t W hinv x) ⁻¹ᵁ ((W x).ι ⁻¹ᵁ W y) := by
  change ((s ∣_ W x) ≫ (W x).ι) ⁻¹ᵁ W y = (tW s t W hinv x ≫ (W x).ι) ⁻¹ᵁ W y
  rw [morphismRestrict_ι, tW_ι]
  change (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (s ⁻¹ᵁ W y) = (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (t ⁻¹ᵁ W y)
  rw [hinv y]

/-- The quotient-chart open corresponding to an overlap of source charts. -/
noncomputable def V (x y : X) : (Yloc s t W hinv
    loc x).Opens :=
  imageOpens (p := ploc s t W hinv loc x) ((W x).ι ⁻¹ᵁ W y)
lemma preimage_V (x y : X) : ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y = (W x).ι ⁻¹ᵁ W y :=
  preimage_imageOpens (ploc_spec s t W hinv loc x).2.2.2.2.2 _ (inv_overlap s t W hinv x y)

lemma range_overlap (x y : X) :
    Set.range ((ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) =
      (W x ⊓ W y : X.Opens) := by
  rw [preimage_V]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range,
      TopologicalSpace.Opens.coe_inf,
    Set.inter_comm]

variable {s t W hinv}

lemma hw (x : X) : (s ∣_ W x) ≫ ploc s t W hinv loc x = tW s t W hinv x ≫ ploc s t W hinv loc x :=
  (ploc_spec s t W hinv loc x).1

lemma hpb (x : X) :
    IsPullback (s ∣_ W x) (tW s t W hinv x) (ploc s t W hinv loc x) (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.2.2.2

/-- Restrict the chosen quotient morphism to a chart overlap. -/
noncomputable abbrev pV (x y : X) := ploc s t W hinv loc x ∣_ V s t W hinv loc x y

/-- The local coequalizer restricted to an overlap. -/
noncomputable def coeqV (x y : X) :
    IsColimit (Cofork.ofπ (pV loc x y) (sRes_w (hw loc x) (V s t W hinv loc x y))) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.2.2.some

lemma isPullback_V (x y : X) :
    IsPullback ((s ∣_ W x) ∣_ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y))
      (tRes (hw loc x) (V s t W hinv loc x y)) (pV loc x y) (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.2.1

/-- Identify the two descriptions of a chart overlap. -/
noncomputable def eX (x y : X) :
    (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y : Scheme.{u}) ≅
      (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _ ≫ (W x).ι) (Scheme.Opens.ι _ ≫ (W y).ι)
    (by rw [range_overlap, range_overlap, inf_comm])

@[reassoc]
lemma eX_hom_ι (x y : X) :
    (eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι = Scheme.Opens.ι _ ≫ (W x).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma sres_preimage (x y : X) :
    (s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y) = (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (s ⁻¹ᵁ W y)
      := by
  rw [preimage_V]
  change ((s ∣_ W x) ≫ (W x).ι) ⁻¹ᵁ W y = _
  rw [morphismRestrict_ι]
  rfl

lemma range_roverlap (x y : X) :
    Set.range (((s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y)).ι ≫ (s ⁻¹ᵁ W x).ι)
      =
      (s ⁻¹ᵁ W x ⊓ s ⁻¹ᵁ W y : R.Opens) := by
  rw [sres_preimage]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range,
      TopologicalSpace.Opens.coe_inf,
    Set.inter_comm]

/-- Identify the induced relation schemes on a chart overlap. -/
noncomputable def eR (x y : X) :
    ((s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y) : Scheme.{u}) ≅
      ((s ∣_ W y) ⁻¹ᵁ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x) : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W x).ι) (Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W y).ι)
    (by rw [range_roverlap, range_roverlap, inf_comm])

@[reassoc]
lemma eR_hom_ι (x y : X) :
    (eR loc x y).hom ≫ Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W y).ι = Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W x).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma hs_comm (x y : X) :
    ((s ∣_ W x) ∣_ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y)) ≫ (eX loc x y).hom =
      (eR loc x y).hom ≫ ((s ∣_ W y) ∣_ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x)) := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
    morphismRestrict_ι_assoc, morphismRestrict_ι]
  simp only [Category.assoc]
  rw [morphismRestrict_ι_assoc, morphismRestrict_ι, eR_hom_ι_assoc]

lemma ht_comm (x y : X) :
    tRes (hw loc x) (V s t W hinv loc x y) ≫ (eX loc x y).hom =
      (eR loc x y).hom ≫ tRes (hw loc y) (V s t W hinv loc y x) := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
    tRes_ι_assoc, tW_ι]
  simp only [Category.assoc]
  rw [tRes_ι_assoc, tW_ι, eR_hom_ι_assoc]

/-- The transition isomorphism between local quotients. -/
noncomputable def φ (x y : X) :
    (V s t W hinv loc x y : Scheme.{u}) ≅ (V s t W hinv loc y x : Scheme.{u}) :=
  quotIso (coeqV loc x y) (coeqV loc y x) (eR loc x y) (eX loc x y) (hs_comm loc x y) (ht_comm loc x
    y)

@[reassoc]
lemma pV_φ_hom (x y : X) : pV loc x y ≫ (φ loc x y).hom = (eX loc x y).hom ≫ pV loc y x :=
  π_quotIso_hom _ _ _ _ _ _

lemma V_self (x : X) : V s t W hinv loc x x = ⊤ := by
  rw [V, Scheme.Opens.ι_preimage_self]
  exact imageOpens_top

scoped instance epi_pV (x y : X) : Epi (pV loc x y) := by
  have h := restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)
  have : Flat (pV loc x y) := h.2.1
  have : LocallyOfFinitePresentation (pV loc x y) := h.2.2.1
  have : Surjective (pV loc x y) := h.2.2.2.1
  infer_instance

lemma eX_self (x : X) : (eX loc x x).hom = 𝟙 _ := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W x).ι), eX_hom_ι, Category.id_comp]

lemma φ_self (x : X) : (φ loc x x).hom = 𝟙 _ := by
  rw [← cancel_epi (pV loc x x), pV_φ_hom, eX_self, Category.id_comp, Category.comp_id]
end Main
end AlgebraicGeometry.Scheme.QuotGlue
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace QuotGlue
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Core

variable {X R : Scheme.{u}} {s t : R ⟶ X} {W : X → X.Opens}
  {hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x}
  (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      QuasiCompact p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

scoped instance quasiCompact_pV (x y : X) : QuasiCompact (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).1
scoped instance flat_pV (x y : X) : Flat (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.1
scoped instance lfp_pV (x y : X) : LocallyOfFinitePresentation (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.1
scoped instance surj_pV (x y : X) : Surjective (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.1

scoped instance epi_pV_restrict (x y : X) (O : (V s t W hinv loc x y : Scheme.{u}).Opens) :
    Epi (pV loc x y ∣_ O) := by
  have h := restrict_pkg (sRes_w (hw loc x) (V s t W hinv loc x y)) (isPullback_V loc x y) O
  have : Flat (pV loc x y ∣_ O) := h.2.1
  have : LocallyOfFinitePresentation (pV loc x y ∣_ O) := h.2.2.1
  have : Surjective (pV loc x y ∣_ O) := h.2.2.2.1
  infer_instance

lemma ι_mem_preimage_V {x y z : X} (u : ↑(ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y))
    (hu : ((ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ ploc s t W hinv loc x) u ∈
      V s t W hinv loc x z) :
    (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι u ∈
      ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z :=
  hu

lemma core_t_inter (x y z : X) :
    (V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z) ≤
      (φ loc x y).hom ⁻¹ᵁ ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) := by
  intro v hv
  obtain ⟨u, rfl⟩ := (pV loc x y).surjective v
  have hv' : ((pV loc x y ≫ (V s t W hinv loc x y).ι) u) ∈ V s t W hinv loc x z := hv
  rw [morphismRestrict_ι] at hv'
  have hu : (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι u ∈
      ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z := hv'
  rw [preimage_V] at hu
  change ((pV loc x y ≫ (φ loc x y).hom) ≫ (V s t W hinv loc y x).ι) u ∈ V s t W hinv loc y z
  rw [pV_φ_hom, Category.assoc, morphismRestrict_ι]
  change ploc s t W hinv loc y (((eX loc x y).hom ≫ Scheme.Opens.ι _) u) ∈
    imageOpens (p := ploc s t W hinv loc y) ((W y).ι ⁻¹ᵁ W z)
  refine le_imageOpens_iff _ _ ?_
  change (((eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι) u) ∈ W z
  rw [eX_hom_ι]
  exact hu

lemma core_cocycle (x y z : X) :
    ((φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z))
        ((V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z)) (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫
        ((V s t W hinv loc y z).ι ⁻¹ᵁ (V s t W hinv loc y x)).ι ≫
          (φ loc y z).hom ≫ (V s t W hinv loc z y).ι) =
    ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
        (V s t W hinv loc x z)).hom ≫
      ((V s t W hinv loc x z).ι ⁻¹ᵁ (V s t W hinv loc x y)).ι ≫
        (φ loc x z).hom ≫ (V s t W hinv loc z x).ι := by
  exact _root_.AlgebraicGeometry.Scheme.QuotGlue.overlap_cocycle W
    (Yloc s t W hinv loc) (ploc s t W hinv loc) (V s t W hinv loc)
    (eX loc) (φ loc) (preimage_V s t W hinv loc)
    (eX_hom_ι loc) (pV_φ_hom loc) (epi_pV_restrict loc)
    (core_t_inter loc) x y z

/-- The gluing datum for the local quotient schemes and their overlap isomorphisms. -/
noncomputable def core : Scheme.GlueData.MkCore.{u}
    where
  U := Yloc s t W hinv loc
  V := V s t W hinv loc
  t x y := (φ loc x y).hom
  V_id := V_self loc
  t_id := φ_self loc
  t_inter := core_t_inter loc
  cocycle := core_cocycle loc
@[scoped simp]
lemma core_J : (core loc).J = X := rfl
@[scoped simp]
lemma core_U (x : X) : (core loc).U x = Yloc s t W hinv loc x := rfl
@[scoped simp]
lemma core_V (x y : X) : (core loc).V x y = V s t W hinv loc x y := rfl
@[scoped simp]
lemma core_t (x y : X) : (core loc).t x y = (φ loc x y).hom := rfl
end Core
end AlgebraicGeometry.Scheme.QuotGlue
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace QuotGlue
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Main56

variable {X R : Scheme.{u}} {s t : R ⟶ X} {W : X → X.Opens} (hxW : ∀ x, x ∈ W x)
  {hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x}
  (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      QuasiCompact p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

/-- The canonical gluing data of the chosen local quotients. -/
noncomputable abbrev D := (core loc).glueData

/-- Include a local quotient chart into the glued quotient. -/
noncomputable def ιY (x : X) : Yloc s t W hinv loc x ⟶ (D loc).glued := (D loc).ι x

lemma ιY_def (x : X) : ιY loc x = (D loc).ι x := rfl

scoped instance isOpenImmersion_ιY (x : X) : IsOpenImmersion (ιY loc x) :=
  Scheme.GlueData.ι_isOpenImmersion (D loc) (show (core loc).J from x)

/-- The covering of the source by the given invariant charts. -/
noncomputable def coverW : X.OpenCover :=
  Scheme.Cover.mkOfCovers X (fun x => (W x : Scheme.{u})) (fun x => (W x).ι)
    (fun x => ⟨x, ⟨x, hxW x⟩, rfl⟩)

@[scoped simp]
lemma coverW_f (x : X) : (coverW hxW).f x = (W x).ι := rfl

/-- Map a source chart into the glued quotient. -/
noncomputable abbrev chart (x : X) : (W x : Scheme.{u}) ⟶ (D loc).glued :=
  ploc s t W hinv loc x ≫ ιY loc x

/-- Lift a pair of chart morphisms to their common overlap. -/
noncomputable def liftOverlap {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X)) :
    T ⟶ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y : Scheme.{u}) :=
  IsOpenImmersion.lift (Scheme.Opens.ι _) a (by
    rw [Scheme.Opens.range_ι, preimage_V]
    rintro _ ⟨z, rfl⟩
    exact ha ⟨z, rfl⟩)

@[reassoc (attr := simp)]
lemma liftOverlap_ι {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X)) :
    liftOverlap loc x y a ha ≫ Scheme.Opens.ι _ = a :=
  IsOpenImmersion.lift_fac _ _ _

lemma chart_comp_eq {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (b : T ⟶ (W y : Scheme.{u})) (hab : a ≫ (W x).ι = b ≫ (W y).ι) :
    a ≫ chart loc x = b ≫ chart loc y := by
  have ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X) := by
    rw [hab]; rintro _ ⟨z, rfl⟩; exact (b z).2
  have hb : Set.range (b ≫ (W y).ι) ⊆ (W x : Set X) := by
    rw [← hab]; rintro _ ⟨z, rfl⟩; exact (a z).2
  let a' := liftOverlap loc x y a ha
  let b' := liftOverlap loc y x b hb
  have hab' : a' ≫ (eX loc x y).hom = b' := by
    rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
      liftOverlap_ι_assoc, liftOverlap_ι_assoc, hab]
  calc a ≫ chart loc x
      = a' ≫ Scheme.Opens.ι _ ≫ ploc s t W hinv loc x ≫ ιY loc x := by
        rw [liftOverlap_ι_assoc]
    _ = a' ≫ pV loc x y ≫ (V s t W hinv loc x y).ι ≫ ιY loc x := by
        rw [← morphismRestrict_ι_assoc]
    _ = a' ≫ pV loc x y ≫ (φ loc x y).hom ≫ (V s t W hinv loc y x).ι ≫ ιY loc y := by
        have := (core loc).t_ι_ι x y
        simp only [core_t, core_V] at this
        rw [show (V s t W hinv loc x y).ι ≫ ιY loc x =
          (φ loc x y).hom ≫ (V s t W hinv loc y x).ι ≫ ιY loc y from this.symm]
    _ = b' ≫ pV loc y x ≫ (V s t W hinv loc y x).ι ≫ ιY loc y := by
        rw [pV_φ_hom_assoc, ← Category.assoc, hab']
    _ = b ≫ chart loc y := by
        rw [morphismRestrict_ι_assoc, liftOverlap_ι_assoc]

/-- The quotient map obtained by gluing the local quotient maps. -/
noncomputable def pglued : X ⟶ (D loc).glued :=
  (coverW hxW).glueMorphisms (fun x => chart loc x) fun x y =>
    chart_comp_eq loc x y _ _ pullback.condition

lemma ι_pglued (x : X) : (W x).ι ≫ pglued hxW loc = chart loc x :=
  (coverW hxW).ι_glueMorphisms _ _ x

lemma s_pglued : s ≫ pglued hxW loc = t ≫ pglued hxW loc := by
  let 𝒰 : R.OpenCover := Scheme.Cover.mkOfCovers X (fun x => (s ⁻¹ᵁ W x : Scheme.{u}))
    (fun x => (s ⁻¹ᵁ W x).ι) (fun r => ⟨s r, ⟨r, hxW (s r)⟩, rfl⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ ?_
  change ∀ x : X, _
  intro x
  change (s ⁻¹ᵁ W x).ι ≫ s ≫ pglued hxW loc = (s ⁻¹ᵁ W x).ι ≫ t ≫ pglued hxW loc
  rw [← morphismRestrict_ι_assoc, ι_pglued, ← tW_ι_assoc s t W hinv, ι_pglued, chart,
    ← Category.assoc, hw loc x]
  simp only [tW, Category.assoc]

lemma preimage_chart (x : X) :
    pglued hxW loc ⁻¹ᵁ (ιY loc x).opensRange = (W x).ι.opensRange := by
  ext z
  rw [Scheme.Opens.opensRange_ι]
  constructor
  · intro hz
    change pglued hxW loc z ∈ Set.range (ιY loc x) at hz
    have hzW : z ∈ W z := hxW z
    have hpz : pglued hxW loc z = ιY loc z (ploc s t W hinv loc z ⟨z, hzW⟩) := by
      have h := congrArg (fun φ : (W z : Scheme.{u}) ⟶ _ => φ ⟨z, hzW⟩) (ι_pglued hxW loc z)
      exact h
    rw [hpz] at hz
    have : ploc s t W hinv loc z ⟨z, hzW⟩ ∈ (ιY loc z) ⁻¹ᵁ (ιY loc x).opensRange := hz
    have hpre : (ιY loc z) ⁻¹ᵁ (ιY loc x).opensRange = V s t W hinv loc z x :=
      (core loc).preimage_opensRange z x
    rw [hpre] at this
    have : (⟨z, hzW⟩ : (W z : Scheme.{u})) ∈ ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z x := this
    rw [preimage_V] at this
    exact this
  · intro hz
    change pglued hxW loc z ∈ Set.range (ιY loc x)
    refine ⟨ploc s t W hinv loc x ⟨z, hz⟩, ?_⟩
    have h := congrArg (fun φ : (W x : Scheme.{u}) ⟶ _ => φ ⟨z, hz⟩) (ι_pglued hxW loc x)
    exact h.symm

lemma isPullback_chart (x : X) :
    IsPullback (ploc s t W hinv loc x) (W x).ι (ιY loc x) (pglued hxW loc) :=
  IsOpenImmersion.isPullback (ploc s t W hinv loc x) (W x).ι (ιY loc x) (pglued hxW loc)
    (ι_pglued hxW loc x) (preimage_chart hxW loc x)

lemma property_pglued (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ x : X, P (ploc s t W hinv loc x)) : P (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change P (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp (P := P) _ _ (h x)

private theorem targetLocalOfRingHomProperty (P : MorphismProperty Scheme.{u})
    (Q : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop)
    [HasRingHomProperty P Q] : IsZariskiLocalAtTarget P := inferInstance

lemma quasiCompact_pglued : QuasiCompact (pglued hxW loc) := by
  have : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    QuasiCompact.isZariskiLocalAtTarget
  exact property_pglued hxW loc (@QuasiCompact.{u}) (fun _ => inferInstance)

lemma flat_pglued : Flat (pglued hxW loc) := by
  have : IsZariskiLocalAtTarget (@Flat.{u}) :=
    targetLocalOfRingHomProperty (@Flat.{u}) RingHom.Flat
  exact property_pglued hxW loc (@Flat.{u}) (fun _ => inferInstance)

lemma lfp_pglued : LocallyOfFinitePresentation (pglued hxW loc) := by
  have : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    targetLocalOfRingHomProperty (@LocallyOfFinitePresentation.{u}) RingHom.FinitePresentation
  exact property_pglued hxW loc (@LocallyOfFinitePresentation.{u}) (fun _ => inferInstance)

lemma surjective_pglued : Surjective (pglued hxW loc) :=
  property_pglued hxW loc (@Surjective.{u}) (fun _ => inferInstance)

lemma isPullback_pglued : IsPullback s t (pglued hxW loc) (pglued hxW loc) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (coverW hxW) ?_
  change ∀ x : X, _
  intro x
  dsimp only [Scheme.Cover.pullbackHom, Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f, coverW_f, coverW,
    Scheme.Cover.mkOfCovers_X, Scheme.Cover.mkOfCovers_f]
  have K : IsPullback (s ∣_ W x) (tW s t W hinv x ≫ (W x).ι) ((W x).ι ≫ pglued hxW loc)
      (pglued hxW loc) := by
    rw [ι_pglued]
    exact (hpb loc x).paste_vert (isPullback_chart hxW loc x)
  have hsq := (isPullback_morphismRestrict s (W x)).flip
  refine IsPullback.of_iso K hsq.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · erw [Iso.refl_hom, Category.comp_id]
    exact hsq.isoPullback_hom_snd.symm
  · erw [Iso.refl_hom, Category.comp_id, tW_ι, ← Category.assoc, hsq.isoPullback_hom_fst]
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (Category.id_comp ((W x).ι ≫ pglued hxW loc)).symm
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

include hxW loc in
theorem main :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      QuasiCompact p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  have := quasiCompact_pglued hxW loc
  have := flat_pglued hxW loc
  have := lfp_pglued hxW loc
  have := surjective_pglued hxW loc
  have hk : IsKernelPair (pglued hxW loc) s t := isPullback_pglued hxW loc
  exact ⟨_, pglued hxW loc, s_pglued hxW loc, inferInstance, inferInstance, inferInstance,
    inferInstance, isPullback_pglued hxW loc, ⟨hk.toCoequalizer (regularEpiOfEffectiveEpi _)⟩⟩
end Main56
end AlgebraicGeometry.Scheme.QuotGlue

end SchemeTheory.Descent.QuotientGluing

open SchemeTheory.Descent.QuotientGluing
open SchemeTheory.Descent.QuotientGluing.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

theorem exists_fppf_quotient_of_forall_exists_quotient_restrict
    {X R : Scheme.{u}} (s t : R ⟶ X)
    (W : X → X.Opens) (hxW : ∀ x, x ∈ W x) (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)
    (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  obtain ⟨Y, p, w, hqc, hfl, hlfp, hsurj, hpb, hcol⟩ :=
    QuotGlue.main (s := s) (t := t) (W := W) hxW (hinv := hinv) (fun x => by
      obtain ⟨Y, p, h0, hF, hL, hQ, hS, hP⟩ := loc x
      exact ⟨Y, p, h0, hQ, hF, hL, hS, hP⟩)
  exact ⟨Y, p, w, hfl, hlfp, hqc, hsurj, hpb, hcol⟩

end AlgebraicGeometry.Scheme
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

namespace SchemeTheory.Descent.InvariantAffineNeighborhoods

namespace InvariantNeighborhoods

variable {X R : Scheme.{u}} (s t : R ⟶ X)

/-- The equivalence class of a scheme point under the finite relation. -/
def cls (w : X) : Set X := {w' | ∃ r : R, s r = w ∧ t r = w'}

section points

variable (hequiv : ∀ T : Scheme.{u},
  _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
include hequiv

theorem mem_cls_self (w : X) : w ∈ cls s t w := by
  obtain ⟨e, hes, het⟩ := (hequiv X).refl (𝟙 X)
  refine ⟨e w, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hes]; rfl
  · rw [← Scheme.Hom.comp_apply, het]; rfl

theorem exists_inv (r : R) : ∃ r' : R, s r' = t r ∧ t r' = s r := by
  obtain ⟨ι, hιs, hιt⟩ := (hequiv R).symm ⟨𝟙 R, Category.id_comp s, Category.id_comp t⟩
  exact ⟨ι r, by rw [← Scheme.Hom.comp_apply, hιs], by rw [← Scheme.Hom.comp_apply, hιt]⟩

theorem cls_symm {w w' : X} (h : w' ∈ cls s t w) : w ∈ cls s t w' := by
  obtain ⟨r, rfl, rfl⟩ := h
  obtain ⟨r', h₁, h₂⟩ := exists_inv s t hequiv r
  exact ⟨r', h₁, h₂⟩

theorem cls_trans {w w' w'' : X} (h : w' ∈ cls s t w) (h' : w'' ∈ cls s t w') : w'' ∈ cls s t w :=
    by
  obtain ⟨r₁, rfl, rfl⟩ := h
  obtain ⟨r₂, h₂, rfl⟩ := h'
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback r₁ r₂ h₂.symm
  obtain ⟨c, hcs, hct⟩ := (hequiv (pullback t s)).trans
    (⟨pullback.fst t s, rfl, rfl⟩ : ∃ φ : pullback t s ⟶ R, φ ≫ s = pullback.fst t s ≫ s ∧ φ ≫ t =
      pullback.fst t s ≫ t)
    (⟨pullback.snd t s, pullback.condition.symm, rfl⟩ : ∃ φ : pullback t s ⟶ R, φ ≫ s = pullback.fst
      t s ≫ t ∧ φ ≫ t = pullback.snd t s ≫ t)
  refine ⟨c z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hcs, Scheme.Hom.comp_apply, hz₁]
  · rw [← Scheme.Hom.comp_apply, hct, Scheme.Hom.comp_apply, hz₂]

theorem cls_eq_of_mem {w w' : X} (h : w' ∈ cls s t w) : cls s t w' = cls s t w :=
  Set.ext fun _ => ⟨fun h'' => cls_trans s t hequiv h h'', fun h'' => cls_trans s t hequiv (cls_symm
    s t hequiv h) h''⟩

end points

section S1

variable [IsFinite t] (U : X.Opens)

/-- The largest open subset whose equivalence classes stay in the chosen open. -/
def W' : X.Opens :=
  ⟨(t.base '' ((s ⁻¹ᵁ U ⊓ t ⁻¹ᵁ U : R.Opens) : Set R)ᶜ)ᶜ, by
    rw [isOpen_compl_iff]
    exact t.isClosedMap _ (isClosed_compl_iff.mpr (Opens.isOpen _))⟩

theorem mem_W'_iff (w : X) : w ∈ W' s t U ↔ ∀ z : R, t z = w → s z ∈ U ∧ t z ∈ U := by
  change w ∈ (t.base '' _)ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and, SetLike.mem_coe]
  constructor
  · intro h z hz
    by_contra hc
    exact h z (fun hm => hc hm) hz
  · intro h z hz hzw
    exact hz (h z hzw)

variable (hequiv : ∀ T : Scheme.{u},
  _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
include hequiv

theorem W'_le : W' s t U ≤ U := by
  intro w hw
  have hw' : w ∈ W' s t U := hw
  rw [mem_W'_iff] at hw'
  obtain ⟨e, hes, het⟩ := (hequiv X).refl (𝟙 X)
  have h2 : t (e w) = w := by rw [← Scheme.Hom.comp_apply, het]; rfl
  exact h2 ▸ (hw' (e w) h2).2

theorem cls_subset_W' {x : X} (hx : cls s t x ⊆ (U : Set X)) : cls s t x ⊆ (W' s t U : Set X) := by
  intro w' hw'
  change w' ∈ W' s t U
  rw [mem_W'_iff]
  intro z hz
  refine ⟨hx ?_, hx (hz ▸ hw')⟩
  have : s z ∈ cls s t w' := cls_symm s t hequiv ⟨z, rfl, hz⟩
  rwa [cls_eq_of_mem s t hequiv hw'] at this

theorem preimage_W'_le : s ⁻¹ᵁ W' s t U ≤ t ⁻¹ᵁ U := by
  intro r hr
  change s r ∈ W' s t U at hr
  rw [mem_W'_iff] at hr
  obtain ⟨r', h₁, h₂⟩ := exists_inv s t hequiv r
  have := (hr r' h₂).1
  rwa [h₁] at this

end S1

section S4

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.Projective A B]

theorem exists_norm : ∃ N : B → A, ∀ (b : B) (p : PrimeSpectrum A),
    N b ∉ p.asIdeal ↔ ∀ q : PrimeSpectrum B, q.comap (algebraMap A B) = p → b ∉ q.asIdeal := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A B
  obtain ⟨ι, hι⟩ := Module.projective_lifting_property π (LinearMap.id) hπ
  let ψ : B → Module.End A (Fin n → A) := fun b =>
    ι ∘ₗ LinearMap.mulLeft A b ∘ₗ π + (LinearMap.id - ι ∘ₗ π)
  refine ⟨fun b => LinearMap.det (ψ b), fun b p => ?_⟩
  let κ := p.asIdeal.ResidueField
  have hker : ∀ a : A, algebraMap A κ a = 0 ↔ a ∈ p.asIdeal := fun a => by
    rw [Ideal.algebraMap_residueField_eq_zero]
  have key : ∀ {K : Type u} [CommRing K] [Algebra A K],
      Function.Bijective ((ψ b).baseChange K) ↔
        Function.Bijective ((LinearMap.mulLeft A b).baseChange K) := by
    intro K _ _
    set πK := π.baseChange K
    set ιK := ι.baseChange K
    set mK := (LinearMap.mulLeft A b).baseChange K
    have hιK : πK ∘ₗ ιK = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hι, LinearMap.baseChange_id]
    have hψK : (ψ b).baseChange K = ιK ∘ₗ mK ∘ₗ πK + (LinearMap.id - ιK ∘ₗ πK) := by
      simp only [ψ, LinearMap.baseChange_add, LinearMap.baseChange_sub, LinearMap.baseChange_comp,
        LinearMap.baseChange_id, πK, ιK, mK]
    rw [hψK]
    have hιK' : ∀ y, πK (ιK y) = y := fun y => LinearMap.congr_fun hιK y
    have hιinj : Function.Injective ιK := Function.LeftInverse.injective hιK'
    set Ψ := ιK ∘ₗ mK ∘ₗ πK + (LinearMap.id - ιK ∘ₗ πK) with hΨ
    have Ψι : ∀ y, Ψ (ιK y) = ιK (mK y) := fun y => by
      simp only [hΨ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply, hιK', sub_self, add_zero]
    have Ψker : ∀ v, πK v = 0 → Ψ v = v := fun v hv => by
      simp only [hΨ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply, hv, map_zero, sub_zero, zero_add]
    have πΨ : ∀ v, πK (Ψ v) = mK (πK v) := fun v => by
      simp only [hΨ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply, map_add, map_sub, hιK', sub_self, add_zero]
    constructor
    · intro hΨb
      constructor
      · intro y₁ y₂ h
        apply hιinj
        apply hΨb.1
        rw [Ψι, Ψι, h]
      · intro y
        obtain ⟨v, hv⟩ := hΨb.2 (ιK y)
        refine ⟨πK v, ?_⟩
        rw [← πΨ, hv, hιK']
    · intro hm
      constructor
      · intro v₁ v₂ h
        have h1 : mK (πK v₁) = mK (πK v₂) := by rw [← πΨ, ← πΨ, h]
        have h2 : πK v₁ = πK v₂ := hm.1 h1
        have h3 : Ψ (v₁ - ιK (πK v₁)) = v₁ - ιK (πK v₁) := Ψker _ (by rw [map_sub, hιK', sub_self])
        have h4 : Ψ (v₂ - ιK (πK v₂)) = v₂ - ιK (πK v₂) := Ψker _ (by rw [map_sub, hιK', sub_self])
        have h5 : Ψ (v₁ - ιK (πK v₁)) = Ψ (v₂ - ιK (πK v₂)) := by
          rw [map_sub, map_sub, h, Ψι, Ψι, h2]
        rw [h3, h4, h2] at h5
        exact sub_left_inj.mp h5
      · intro v
        obtain ⟨y, hy⟩ := hm.2 (πK v)
        refine ⟨ιK y + (v - ιK (πK v)), ?_⟩
        rw [map_add, Ψι, Ψker _ (by rw [map_sub, hιK', sub_self]), hy]
        abel
  have h1 : LinearMap.det (ψ b) ∉ p.asIdeal ↔ Function.Bijective ((ψ b).baseChange κ) := by
    rw [← hker, ← LinearMap.det_baseChange, ← Module.End.isUnit_iff,
      LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [h1, key]
  have h2 : Function.Bijective ((LinearMap.mulLeft A b).baseChange κ) ↔
      IsUnit ((1 : κ) ⊗ₜ[A] b : κ ⊗[A] B) := by
    have hm : ((LinearMap.mulLeft A b).baseChange κ : κ ⊗[A] B → κ ⊗[A] B) =
        fun z => ((1 : κ) ⊗ₜ[A] b) * z := by
      funext z
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
          simp only [LinearMap.baseChange_tmul, LinearMap.mulLeft_apply,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
    rw [hm]
    exact IsUnit.isUnit_iff_mulLeft_bijective.symm
  rw [h2]
  constructor
  · intro hu q hq hbq
    let Q : PrimeSpectrum (p.asIdeal.Fiber B) := PrimeSpectrum.preimageEquivFiber A B p ⟨q, hq⟩
    have hq' : (PrimeSpectrum.preimageEquivFiber A B p).symm Q = ⟨q, hq⟩ := Equiv.symm_apply_apply _
      _
    have hmem : ((1 : κ) ⊗ₜ[A] b : κ ⊗[A] B) ∈ Q.asIdeal := by
      have : q = Q.comap Algebra.TensorProduct.includeRight.toRingHom := by
        have := congrArg Subtype.val hq'
        exact this.symm
      rw [this] at hbq
      exact hbq
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · intro hall
    by_contra hnu
    obtain ⟨M, hM, hbM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hnu)
    let Q : PrimeSpectrum (p.asIdeal.Fiber B) := ⟨M, hM.isPrime⟩
    let q := (PrimeSpectrum.preimageEquivFiber A B p).symm Q
    apply hall q.1 q.2
    change b ∈ (Q.comap Algebra.TensorProduct.includeRight.toRingHom).asIdeal
    exact hbM

end S4

theorem exists_basicOpen_of_finite {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (F : Set X) (hF : F.Finite) (V : X.Opens) (hFV : F ⊆ (V : Set X)) (hFU : F ⊆ (U : Set X)) :
    ∃ f : Γ(X, U), F ⊆ (X.basicOpen f : Set X) ∧ X.basicOpen f ≤ V := by
  classical
  by_cases hne : F.Nonempty
  swap
  · refine ⟨0, ?_, ?_⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact Set.empty_subset _
    · rw [Scheme.basicOpen_zero]
      exact bot_le
  obtain ⟨w₀, hw₀⟩ := hne
  set φ := hU.fromSpec with hφ
  let C : Set (PrimeSpectrum Γ(X, U)) := φ.base ⁻¹' ((V : Set X)ᶜ)
  let I : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal C
  let P : F → PrimeSpectrum Γ(X, U) := fun w => hU.primeIdealOf ⟨w.1, hFU w.2⟩
  have hPφ : ∀ w : F, φ (P w) = w.1 := fun w => hU.fromSpec_primeIdealOf ⟨w.1, hFU w.2⟩
  have hC : IsClosed C := IsClosed.preimage φ.base.hom.continuous V.isOpen.isClosed_compl
  have hPI : ∀ w : F, ¬ I ≤ (P w).asIdeal := fun w hle => by
    have hmem : P w ∈ PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) := by
      rwa [PrimeSpectrum.mem_zeroLocus]
    have hmem' : P w ∈ C := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hC.closure_eq] at hmem
      exact hmem
    apply hmem'
    rw [hPφ w]
    exact hFV w.2
  let : Fintype F := hF.fintype
  have havoid : ¬ ((I : Set Γ(X, U)) ⊆ ⋃ w ∈ (↑(Finset.univ : Finset F) : Set F),
      ((fun w : F => (P w).asIdeal) w : Set Γ(X, U))) := by
    rw [Ideal.subset_union_prime (⟨w₀, hw₀⟩ : F) ⟨w₀, hw₀⟩ (fun w _ _ _ => (P w).isPrime)]
    rintro ⟨w, -, hw⟩
    exact hPI w hw
  rw [Set.not_subset] at havoid
  obtain ⟨g, hgI, hg⟩ := havoid
  have hg' : ∀ w : F, g ∉ (P w).asIdeal := fun w h => hg (Set.mem_biUnion (Finset.mem_coe.mpr
    (Finset.mem_univ w)) h)
  refine ⟨g, ?_, ?_⟩
  · intro w hw
    have h1 : P ⟨w, hw⟩ ∈ (PrimeSpectrum.basicOpen g : Set _) :=
      (PrimeSpectrum.mem_basicOpen g (P ⟨w, hw⟩)).mpr (hg' ⟨w, hw⟩)
    have h2 : P ⟨w, hw⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]; exact h1
    have h3 : φ (P ⟨w, hw⟩) ∈ X.basicOpen g := h2
    rw [hPφ ⟨w, hw⟩] at h3
    exact h3
  · intro w hw
    have hwU : w ∈ U := X.basicOpen_le g hw
    by_contra hwV
    let p := hU.primeIdealOf ⟨w, hwU⟩
    have hp : φ p = w := hU.fromSpec_primeIdealOf ⟨w, hwU⟩
    have hpC : p ∈ C := by
      change φ.base p ∈ (V : Set X)ᶜ
      rw [Set.mem_compl_iff]; exact fun h => hwV (hp ▸ h)
    have hgp : g ∈ p.asIdeal := (PrimeSpectrum.subset_zeroLocus_vanishingIdeal C hpC) hgI
    have hpg : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      change φ p ∈ X.basicOpen g
      rw [hp]; exact hw
    rw [hU.fromSpec_preimage_basicOpen] at hpg
    exact (PrimeSpectrum.mem_basicOpen g p).mp hpg hgp

section core

variable {X R : Scheme.{u}} (s t : R ⟶ X) [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]

theorem mem_basicOpen_iff_notMem {U : X.Opens} (hU : IsAffineOpen U) (g : Γ(X, U)) {w : X}
    (hw : w ∈ U) : w ∈ X.basicOpen g ↔ g ∉ (hU.primeIdealOf ⟨w, hw⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen]
  have key : hU.primeIdealOf ⟨w, hw⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g ↔ w ∈ X.basicOpen g := by
    change hU.fromSpec (hU.primeIdealOf ⟨w, hw⟩) ∈ X.basicOpen g ↔ _
    rw [hU.fromSpec_primeIdealOf]
  rw [← key, hU.fromSpec_preimage_basicOpen]
  rfl

theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec p ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨p, rfl⟩

theorem primeIdealOf_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    hU.primeIdealOf ⟨hU.fromSpec p, fromSpec_mem hU p⟩ = p := by
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf]

theorem exists_basicOpen_forall {U : X.Opens} (f : Γ(X, U)) (hD : IsAffineOpen (X.basicOpen f))
    (hVU : s ⁻¹ᵁ X.basicOpen f ≤ t ⁻¹ᵁ U) :
    ∃ g : Γ(X, X.basicOpen f), ∀ w : X, w ∈ X.basicOpen f →
      (w ∈ X.basicOpen g ↔ ∀ r : R, s r = w → t r ∈ X.basicOpen f) := by
  set D := X.basicOpen f with hDdef
  have hV : IsAffineOpen (s ⁻¹ᵁ D) := hD.preimage s
  let inst : Algebra Γ(X, D) Γ(R, s ⁻¹ᵁ D) := (s.app D).hom.toAlgebra
  have : Module.Finite Γ(X, D) Γ(R, s ⁻¹ᵁ D) := IsFinite.finite_app s D hD
  have hflat : (s.app D).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Flat) s inferInstance ⟨D, hD⟩ ⟨_, hV⟩ le_rfl
  have hfp : (s.app D).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) s inferInstance ⟨D, hD⟩
      ⟨_, hV⟩ le_rfl
  have : Module.Flat Γ(X, D) Γ(R, s ⁻¹ᵁ D) := hflat
  have : Algebra.FinitePresentation Γ(X, D) Γ(R, s ⁻¹ᵁ D) := hfp
  have : Module.FinitePresentation Γ(X, D) Γ(R, s ⁻¹ᵁ D) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  have : Module.Projective Γ(X, D) Γ(R, s ⁻¹ᵁ D) := Module.Flat.projective_of_finitePresentation
  obtain ⟨N, hN⟩ := exists_norm Γ(X, D) Γ(R, s ⁻¹ᵁ D)
  let b : Γ(R, s ⁻¹ᵁ D) := R.presheaf.map (homOfLE hVU).op (t.app U f)
  refine ⟨N b, fun w hw => ?_⟩
  rw [mem_basicOpen_iff_notMem hD (N b) hw, hN]
  have hb : ∀ (r : R) (hr : r ∈ s ⁻¹ᵁ D), b ∉ (hV.primeIdealOf ⟨r, hr⟩).asIdeal ↔ t r ∈ D :=
    fun r hr => by
      rw [← mem_basicOpen_iff_notMem hV b hr]
      change r ∈ R.basicOpen (R.presheaf.map (homOfLE hVU).op (t.app U f)) ↔ _
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      change r ∈ (s ⁻¹ᵁ D) ⊓ t ⁻¹ᵁ D ↔ t r ∈ D
      simp only [Opens.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩
  have hcomap : ∀ (r : R) (hr : r ∈ s ⁻¹ᵁ D),
      (hV.primeIdealOf ⟨r, hr⟩).comap (algebraMap Γ(X, D) Γ(R, s ⁻¹ᵁ D)) =
        hD.primeIdealOf ⟨s r, hr⟩ := fun r hr => by
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := s) D hD (s ⁻¹ᵁ D) hV le_rfl hr
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this
  constructor
  · intro hall r hsr
    have hr : r ∈ s ⁻¹ᵁ D := by change s r ∈ D; rw [hsr]; exact hw
    refine (hb r hr).mp (hall _ ?_)
    rw [hcomap]
    congr 1
    exact Subtype.ext hsr
  · intro hall 𝔮 h𝔮
    let r : R := hV.fromSpec 𝔮
    have hr : r ∈ s ⁻¹ᵁ D := fromSpec_mem hV 𝔮
    have h𝔮r : hV.primeIdealOf ⟨r, hr⟩ = 𝔮 := primeIdealOf_fromSpec hV 𝔮
    have hsr : s r = w := by
      have h1 := hcomap r hr
      rw [h𝔮r, h𝔮] at h1
      have h2 := congrArg hD.fromSpec h1
      rw [hD.fromSpec_primeIdealOf, hD.fromSpec_primeIdealOf] at h2
      exact h2.symm
    rw [← h𝔮r]
    exact (hb r hr).mpr (hall r hsr)

end core

theorem main_finite [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    {S : Set X} (hS : S.Finite) {U : X.Opens} (hU : IsAffineOpen U)
    (hSU : ∀ x ∈ S, ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ S ⊆ (W : Set X) ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W := by
  have hcls : ∀ x ∈ S, cls s t x ⊆ (U : Set X) := by
    rintro x hxS _ ⟨r, hr, rfl⟩; exact hSU x hxS r hr
  set C : Set X := ⋃ x ∈ S, cls s t x with hCdef
  have hCU : C ⊆ (U : Set X) := by
    intro w hw
    obtain ⟨x, hxS, hw'⟩ := Set.mem_iUnion₂.mp hw
    exact hcls x hxS hw'
  have hfin : C.Finite := by
    refine hS.biUnion fun x _ => ?_
    have : cls s t x = t.base '' (s.base ⁻¹' {x}) := by
      ext w; simp only [cls, Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage,
        Set.mem_singleton_iff]
    rw [this]
    exact (s.finite_preimage_singleton x).image _
  have hCW' : C ⊆ (W' s t U : Set X) := by
    intro w hw
    obtain ⟨x, hxS, hw'⟩ := Set.mem_iUnion₂.mp hw
    exact cls_subset_W' s t U hequiv (hcls x hxS) hw'
  obtain ⟨f, hfC, hfW'⟩ := exists_basicOpen_of_finite hU C hfin (W' s t U) hCW' hCU
  have hD : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hVU : s ⁻¹ᵁ X.basicOpen f ≤ t ⁻¹ᵁ U :=
    le_trans (Scheme.Hom.preimage_mono s hfW') (preimage_W'_le s t U hequiv)
  obtain ⟨g, hg⟩ := exists_basicOpen_forall s t f hD hVU
  refine ⟨X.basicOpen g, hD.basicOpen g, ?_, ?_, ?_⟩
  · intro x hxS
    have hsub : cls s t x ⊆ (X.basicOpen f : Set X) := fun w hw =>
      hfC (Set.mem_iUnion₂.mpr ⟨x, hxS, hw⟩)
    have hxD : x ∈ X.basicOpen f := hsub (mem_cls_self s t hequiv x)
    change x ∈ X.basicOpen g
    rw [hg x hxD]
    intro r hr
    exact hsub ⟨r, hr, rfl⟩
  · exact le_trans (X.basicOpen_le g) (le_trans (X.basicOpen_le f) le_rfl)
  · have hW : ∀ w : X, w ∈ X.basicOpen g ↔ cls s t w ⊆ (X.basicOpen f : Set X) := fun w => by
      constructor
      · intro hw
        have hwD : w ∈ X.basicOpen f := X.basicOpen_le g hw
        rw [hg w hwD] at hw
        rintro _ ⟨r, hr, rfl⟩
        exact hw r hr
      · intro hsub
        have hwD : w ∈ X.basicOpen f := hsub (mem_cls_self s t hequiv w)
        rw [hg w hwD]
        intro r hr
        exact hsub ⟨r, hr, rfl⟩
    ext r
    change s r ∈ X.basicOpen g ↔ t r ∈ X.basicOpen g
    rw [hW, hW, cls_eq_of_mem s t hequiv (⟨r, rfl, rfl⟩ : t r ∈ cls s t (s r))]

end InvariantNeighborhoods

end SchemeTheory.Descent.InvariantAffineNeighborhoods

open SchemeTheory.Descent.InvariantAffineNeighborhoods

namespace AlgebraicGeometry.Scheme

theorem exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    {S : Set X} (hS : S.Finite) {U : X.Opens} (hU : IsAffineOpen U)
    (hSU : ∀ x ∈ S, ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ S ⊆ (W : Set X) ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W :=
  InvariantNeighborhoods.main_finite s t hequiv hS hU hSU

end AlgebraicGeometry.Scheme
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace SchemeTheory.Descent.InvariantAffineDescent

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace InvariantAffineImage

variable {X R Y : Scheme.{u}} (s t : R ⟶ X) (p : X ⟶ Y)

theorem mem_of_apply_eq (hR : IsPullback s t p p) (W : X.Opens) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W)
    {x w : X} (hw : w ∈ W) (h : p x = p w) : x ∈ W := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x w h
  set r : R := hR.isoPullback.inv z with hr
  have hs : s r = x := by
    rw [hr, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]; exact hz1
  have ht : t r = w := by
    rw [hr, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]; exact hz2
  have hrt : r ∈ t ⁻¹ᵁ W := by change t r ∈ W; rw [ht]; exact hw
  rw [← hinv] at hrt
  have : s r ∈ W := hrt
  rwa [hs] at this

/-- The quotient open complementary to the image of the closed complement. -/
def imageOpen [UniversallyClosed p] (W : X.Opens) : Y.Opens :=
  ⟨(p.base '' ((W : Set X)ᶜ))ᶜ, by
    rw [isOpen_compl_iff]
    exact p.isClosedMap _ (isClosed_compl_iff.mpr W.isOpen)⟩

theorem mem_imageOpen_iff [UniversallyClosed p] (W : X.Opens) (y : Y) :
    y ∈ imageOpen p W ↔ ∀ x : X, p x = y → x ∈ W := by
  change y ∈ (p.base '' _)ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and, SetLike.mem_coe]
  constructor
  · intro h x hx
    by_contra hc
    exact h x hc hx
  · intro h x hx hpx
    exact hx (h x hpx)

theorem preimage_imageOpen_eq [UniversallyClosed p] (hR : IsPullback s t p p) (W : X.Opens)
    (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W) : p ⁻¹ᵁ imageOpen p W = W := by
  ext x
  change p x ∈ imageOpen p W ↔ x ∈ (W : Set X)
  rw [mem_imageOpen_iff]
  constructor
  · intro h; exact h x rfl
  · intro hx x' hx'
    exact mem_of_apply_eq s t p hR W hinv hx hx'

end InvariantAffineImage

open InvariantAffineImage

theorem equivalenceRelation_restrict {X R : Scheme.{u}} (s t : R ⟶ X) (U : X.Opens) (hinv : s ⁻¹ᵁ U
    = t ⁻¹ᵁ U)
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) :
    (∀ {T : Scheme.{u}} (a b : T ⟶ (s ⁻¹ᵁ U).toScheme),
        a ≫ (s ∣_ U) = b ≫ (s ∣_ U) →
        a ≫ ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) = b ≫ ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ U.toScheme =>
        ∃ φ : T ⟶ (s ⁻¹ᵁ U).toScheme, φ ≫ (s ∣_ U) = x ∧ φ ≫ ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) = y)
          := by
  have hs' : (s ∣_ U) ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ s := morphismRestrict_ι s U
  have ht' : ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ t := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  have key : ∀ {T : Scheme.{u}} (x y : T ⟶ U.toScheme),
      (∃ φ : T ⟶ (s ⁻¹ᵁ U).toScheme, φ ≫ (s ∣_ U) = x ∧ φ ≫ ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) = y) ↔
      (∃ φ : T ⟶ R, φ ≫ s = x ≫ U.ι ∧ φ ≫ t = y ≫ U.ι) := by
    intro T x y
    constructor
    · rintro ⟨φ, h1, h2⟩
      refine ⟨φ ≫ (s ⁻¹ᵁ U).ι, ?_, ?_⟩
      · rw [Category.assoc, ← hs', ← Category.assoc, h1]
      · rw [Category.assoc, ← ht', ← Category.assoc, h2]
    · rintro ⟨φ, h1, h2⟩
      have hrange : Set.range φ.base ⊆ Set.range (s ⁻¹ᵁ U).ι.base := by
        rintro _ ⟨z, rfl⟩
        rw [Scheme.Opens.range_ι]
        change s (φ z) ∈ U
        rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
        exact (x z).2
      refine ⟨IsOpenImmersion.lift (s ⁻¹ᵁ U).ι φ hrange, ?_, ?_⟩
      · apply (cancel_mono U.ι).mp
        rw [Category.assoc, hs', ← Category.assoc, IsOpenImmersion.lift_fac, h1]
      · apply (cancel_mono U.ι).mp
        rw [Category.assoc, ht', ← Category.assoc, IsOpenImmersion.lift_fac, h2]
  refine ⟨?_, ?_⟩
  · intro T a b ha hb
    apply (cancel_mono (s ⁻¹ᵁ U).ι).mp
    apply hmono
    · have ha' := congrArg (· ≫ U.ι) ha
      simp only [Category.assoc, hs'] at ha'
      simpa only [Category.assoc] using ha'
    · have hb' := congrArg (· ≫ U.ι) hb
      simp only [Category.assoc] at hb'
      rw [← Category.assoc (R.isoOfEq hinv).hom, ht'] at hb'
      simpa only [Category.assoc] using hb'
  · intro T
    refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
    · exact (key x x).mpr ((hequiv T).refl (x ≫ U.ι))
    · exact (key y x).mpr ((hequiv T).symm ((key x y).mp hxy))
    · exact (key x z).mpr ((hequiv T).trans ((key x y).mp hxy) ((key y z).mp hyz))

end AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry
open _root_.SchemeTheory.Descent.InvariantAffineDescent.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.SchemeTheory.Descent.InvariantAffineDescent.AlgebraicGeometry.Scheme
open
    _root_.SchemeTheory.Descent.InvariantAffineDescent.AlgebraicGeometry.Scheme.InvariantAffineImage

end SchemeTheory.Descent.InvariantAffineDescent

open SchemeTheory.Descent.InvariantAffineDescent
open SchemeTheory.Descent.InvariantAffineDescent.AlgebraicGeometry.Scheme
open SchemeTheory.Descent.InvariantAffineDescent.AlgebraicGeometry.Scheme.InvariantAffineImage

namespace AlgebraicGeometry.Scheme

theorem exists_isAffineOpen_preimage_eq_of_invariant {X R Y : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (p : X ⟶ Y) (w : s ≫ p = t ≫ p)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p) (W : X.Opens) (hW : IsAffineOpen W) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ p ⁻¹ᵁ V = W := by
  let V : Y.Opens := imageOpen p W
  have hVW : p ⁻¹ᵁ V = W := preimage_imageOpen_eq s t p hR W hinv
  refine ⟨V, ?_, hVW⟩
  have hinv' : s ⁻¹ᵁ (p ⁻¹ᵁ V) = t ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    change (s ≫ p) ⁻¹ᵁ V = (t ≫ p) ⁻¹ᵁ V
    rw [w]
  let s' : (s ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme ⟶ (p ⁻¹ᵁ V).toScheme := s ∣_ (p ⁻¹ᵁ V)
  let t' : (s ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme ⟶ (p ⁻¹ᵁ V).toScheme := (R.isoOfEq hinv').hom ≫ (t ∣_ (p ⁻¹ᵁ
    V))
  let p' : (p ⁻¹ᵁ V).toScheme ⟶ V.toScheme := p ∣_ V
  have hX : IsPullback (p ⁻¹ᵁ V).ι p' p V.ι := (isPullback_morphismRestrict p V).flip
  have hsq : IsPullback (s ⁻¹ᵁ (p ⁻¹ᵁ V)).ι s' s (p ⁻¹ᵁ V).ι := (isPullback_morphismRestrict s (p
    ⁻¹ᵁ V)).flip
  have htq : (s ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ t = t' ≫ (p ⁻¹ᵁ V).ι := by
    simp only [t', Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  have hsι : s' ≫ (p ⁻¹ᵁ V).ι = (s ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ s := morphismRestrict_ι s (p ⁻¹ᵁ V)
  have hpι : p' ≫ V.ι = (p ⁻¹ᵁ V).ι ≫ p := morphismRestrict_ι p V
  have w' : s' ≫ p' = t' ≫ p' := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, Category.assoc, hpι, ← Category.assoc s', ← Category.assoc t', hsι, ← htq,
      Category.assoc, Category.assoc, w]
  obtain ⟨-, -, -, -, -, ⟨hcolim'⟩⟩ :=
    AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback hR hX hsq htq w'
  have : IsAffine (p ⁻¹ᵁ V).toScheme := by rw [hVW]; exact hW
  have : IsFinite s' := MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹IsFinite s›
  have : Flat s' := MorphismProperty.of_isPullback (P := @Flat) hsq ‹Flat s›
  have : LocallyOfFinitePresentation s' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsq
      ‹LocallyOfFinitePresentation s›
  have htsq : IsPullback (t ⁻¹ᵁ (p ⁻¹ᵁ V)).ι (t ∣_ (p ⁻¹ᵁ V)) t (p ⁻¹ᵁ V).ι :=
    (isPullback_morphismRestrict t (p ⁻¹ᵁ V)).flip
  have : IsFinite (t ∣_ (p ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @IsFinite) htsq ‹IsFinite
    t›
  have : Flat (t ∣_ (p ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @Flat) htsq ‹Flat t›
  have : LocallyOfFinitePresentation (t ∣_ (p ⁻¹ᵁ V)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) htsq
      ‹LocallyOfFinitePresentation t›
  have : IsFinite t' := inferInstance
  have : Flat t' := inferInstance
  have : LocallyOfFinitePresentation t' := inferInstance
  obtain ⟨hmono', hequiv'⟩ := equivalenceRelation_restrict s t (p ⁻¹ᵁ V) hinv' hmono hequiv
  obtain ⟨Y'', hY'', p'', w'', -, -, -, -, -, ⟨hcolim''⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation s' t'
      hmono' hequiv'
  let e : V.toScheme ≅ Y'' := IsColimit.coconePointUniqueUpToIso hcolim' hcolim''
  have : IsAffine Y'' := hY''
  exact IsAffine.of_isIso e.hom

end AlgebraicGeometry.Scheme
end
