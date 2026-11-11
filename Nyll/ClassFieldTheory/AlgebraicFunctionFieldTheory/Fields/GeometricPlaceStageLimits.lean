/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Valuation.Subring.DirectedFieldUnion
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinBoundaryStages
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.GeometricRestrictedRayTransitions
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantCurveModel
public import Nyll.AlgebraicCurves.Places.ValuationRings.BasicValuationSubringSeparable
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantTower
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Geometric places from their original finite constant stages

A compatible family of finite-stage places determines a valuation ring in
the actual geometric compositum. It contains every algebraic constant, is
proper, and is a place by the original separating parameter. Thus the family
comes from a unique geometric place. Compatible finite-stage place bijections
consequently give an actual geometric place bijection with the original
restriction squares.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors
  geometricLocalizationConstants geometricLocalizationConstantTower

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

local notation "I" => GeometricArtinIndex k K Ω
local notation "E" => geometricArtinStageField k K Ω
local notation "G" => geometricConstantExtension k K Ω
local notation "C" => separableClosure k Ω

/-- Finite-stage place restriction uses exactly the original field
inclusion on valuation-ring membership. -/
theorem geometricArtinStagePlaceRestrict_mem
    (i j : I) (hij : i ≤ j) (w : Place k (E j)) (x : E i) :
    x ∈ (geometricArtinStagePlaceRestrict k K Ω i j hij w).toValuationSubring ↔
      IntermediateField.inclusion hij x ∈ w.toValuationSubring := by
  let _ : Algebra (E i) (E j) := (IntermediateField.inclusion hij).toRingHom.toAlgebra
  have _ : IsScalarTower K (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : IsScalarTower k (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
  exact w.mem_restrict_iff

/-- Restriction between finite stages agrees with direct restriction of
the same original geometric place. -/
theorem geometricArtinStagePlaceRestrict_stage
    (i j : I) (hij : i ≤ j) (W : Place C G) :
    geometricArtinStagePlaceRestrict k K Ω i j hij
        (geometricArtinPlaceAtStage k K Ω j W) =
      geometricArtinPlaceAtStage k K Ω i W := by
  apply Place.ext
  apply SetLike.ext
  intro x
  have hx : fullConstantStageGeometricInclusion k K Ω j.degree
        (IntermediateField.inclusion hij x) =
      fullConstantStageGeometricInclusion k K Ω i.degree x :=
    FunctionField.RayClass.intermediateField_inclusion_compat
      (E i).toIntermediateField (E j).toIntermediateField G hij
      (fullConstantStageGeometricInclusion k K Ω i.degree)
      (fullConstantStageGeometricInclusion k K Ω j.degree)
      (fullConstantStageGeometricInclusion_coe k K Ω i.degree)
      (fullConstantStageGeometricInclusion_coe k K Ω j.degree) x
  exact (geometricArtinStagePlaceRestrict_mem k K Ω i j hij
    (geometricArtinPlaceAtStage k K Ω j W) x).trans
      ((geometricArtinPlaceAtStage_mem k K Ω j W
        (IntermediateField.inclusion hij x)).trans
        ((Iff.of_eq (congrArg (fun z : G => z ∈ W.toValuationSubring) hx)).trans
          (geometricArtinPlaceAtStage_mem k K Ω i W x).symm))

/-- All original finite-stage restrictions jointly determine a geometric
place. -/
theorem geometricPlace_eq_of_stage_eq (W V : Place C G)
    (h : ∀ i : I, geometricArtinPlaceAtStage k K Ω i W =
      geometricArtinPlaceAtStage k K Ω i V) : W = V := by
  by_contra hWV
  obtain ⟨j, _, hj⟩ := exists_geometricArtinStage_separating k K Ω
    ⟨1⟩ W V hWV
  exact hj (h j)

/-- Any compatible family on a surjective directed indexing of the
original constant stages is the family of restrictions of one unique
geometric place. The valuation ring and its discreteness are constructed. -/
theorem exists_unique_geometricPlace_of_stage_family
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (t : ι → I) (ht : Monotone t) (hst : Function.Surjective t)
    (w : ∀ i : ι, Place k (E (t i)))
    (hw : ∀ (i j : ι) (hij : i ≤ j),
      geometricArtinStagePlaceRestrict k K Ω (t i) (t j) (ht hij) (w j) = w i) :
    ∃! W : Place C G, ∀ i : ι, geometricArtinPlaceAtStage k K Ω (t i) W = w i := by
  let F : ι → IntermediateField K Ω := fun i => (E (t i)).toIntermediateField
  have hF : Monotone F := fun _ _ hij => ht hij
  have hFG : ∀ i, F i ≤ G := by
    intro i x hx
    exact (mem_geometricConstantExtension_iff k K Ω x).mpr ⟨(t i).degree, hx⟩
  have hex : ∀ x : G, ∃ i, (x : Ω) ∈ F i := by
    intro x
    obtain ⟨n, hn⟩ := (mem_geometricConstantExtension_iff k K Ω (x : Ω)).mp x.property
    obtain ⟨i, hi⟩ := hst ⟨n⟩
    refine ⟨i, ?_⟩
    change (x : Ω) ∈ (E (t i)).toIntermediateField
    rw [hi]
    exact hn
  let V : ∀ i, ValuationSubring (F i) := fun i => (w i).toValuationSubring
  have hV : ∀ (i j : ι) (hij : i ≤ j) (x : F i),
      IntermediateField.inclusion (hF hij) x ∈ V j ↔ x ∈ V i := by
    intro i j hij x
    rw [← geometricArtinStagePlaceRestrict_mem k K Ω (t i) (t j) (ht hij), hw i j hij]
  let A : ValuationSubring G := ValuationSubring.directedFieldUnion F hF G hex V hV
  have hA : A ≠ ⊤ := ValuationSubring.directedFieldUnion_ne_top
    F hF G hFG hex V hV (Classical.arbitrary ι) (w _).ne_top'
  have hk : ∀ a : k, algebraMap k G a ∈ A := by
    intro a
    let i : ι := Classical.arbitrary ι
    have hi : IntermediateField.inclusion (hFG i) (algebraMap k (F i) a) =
        algebraMap k G a := Subtype.ext rfl
    rw [← hi]
    exact (ValuationSubring.directedFieldUnion_mem_inclusion
      F hF G hFG hex V hV i (algebraMap k (F i) a)).mpr ((w i).algebraMap_mem' a)
  have hC : ∀ a : C, algebraMap C G a ∈ A := by
    let _ : Algebra k A := ((algebraMap k G).codRestrict A.toSubring hk).toAlgebra
    have _ : IsScalarTower k A G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    intro a
    have ha : IsIntegral k (algebraMap C G a) :=
      (Algebra.IsIntegral.isIntegral (R := k) a).map (IsScalarTower.toAlgHom k C G)
    have haA : IsIntegral A (algebraMap C G a) := ha.tower_top
    obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff G).mp inferInstance haA
    exact hb ▸ b.property
  obtain ⟨s, _, hfin, hsep⟩ :=
    geometricConstantExtension_original_separatingParameter k K Ω
  have _ : FiniteDimensional
      (IntermediateField.adjoin C ({algebraMap K G s} : Set G)) G := hfin
  have _ : Algebra.IsSeparable
      (IntermediateField.adjoin C ({algebraMap K G s} : Set G)) G := hsep
  obtain ⟨W, hW⟩ := Place.exists_of_valuationSubring_of_isSeparable
    (algebraMap K G s) A hC hA
  have hWstage : ∀ i : ι, geometricArtinPlaceAtStage k K Ω (t i) W = w i := by
    intro i
    apply Place.ext
    apply SetLike.ext
    intro x
    rw [geometricArtinPlaceAtStage_mem, hW]
    exact ValuationSubring.directedFieldUnion_mem_inclusion F hF G hFG hex V hV i x
  refine ⟨W, hWstage, ?_⟩
  intro W' hW'
  apply geometricPlace_eq_of_stage_eq k K Ω W' W
  intro j
  obtain ⟨i, rfl⟩ := hst j
  exact (hW' i).trans (hWstage i).symm

end FunctionField.RayClass

namespace FunctionField.RayClass

attribute [local instance]
  geometricLocalizationConstants geometricLocalizationConstantTower

variable (k₁ K₁ Ω₁ k₂ K₂ Ω₂ : Type*)
    [Field k₁] [Finite k₁] [Field K₁] [Field Ω₁]
    [Algebra k₁ K₁] [Algebra (RatFunc k₁) K₁]
    [IsScalarTower k₁ (RatFunc k₁) K₁] [FunctionField k₁ K₁]
    [Algebra K₁ Ω₁] [IsSepClosed Ω₁] [Algebra k₁ Ω₁] [IsScalarTower k₁ K₁ Ω₁]
    [Field k₂] [Finite k₂] [Field K₂] [Field Ω₂]
    [Algebra k₂ K₂] [Algebra (RatFunc k₂) K₂]
    [IsScalarTower k₂ (RatFunc k₂) K₂] [FunctionField k₂ K₂]
    [Algebra K₂ Ω₂] [IsSepClosed Ω₂] [Algebra k₂ Ω₂] [IsScalarTower k₂ K₂ Ω₂]

local notation "I₁" => GeometricArtinIndex k₁ K₁ Ω₁
local notation "q" => geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂
local notation "G₁" => geometricConstantExtension k₁ K₁ Ω₁
local notation "G₂" => geometricConstantExtension k₂ K₂ Ω₂
local notation "C₁" => separableClosure k₁ Ω₁
local notation "C₂" => separableClosure k₂ Ω₂

variable
    (v : ∀ i : GeometricArtinIndex k₁ K₁ Ω₁,
      Place k₁ (geometricArtinStageField k₁ K₁ Ω₁ i) ≃
        Place k₂ (geometricArtinStageField k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)))
    (hv : ∀ (i j : GeometricArtinIndex k₁ K₁ Ω₁) (hij : i ≤ j)
      (w : Place k₁ (geometricArtinStageField k₁ K₁ Ω₁ j)),
      geometricArtinStagePlaceRestrict k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)
          ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂).monotone hij) (v j w) =
        v i (geometricArtinStagePlaceRestrict k₁ K₁ Ω₁ i j hij w))

include hv in
/-- A compatible system of actual finite-stage place bijections induces
one unique bijection of the original geometric places. -/
theorem exists_unique_geometricPlaceEquiv_of_stageEquivs :
    ∃! e : Place C₁ G₁ ≃ Place C₂ G₂,
      ∀ (i : I₁) (W : Place C₁ G₁),
        geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) (e W) =
          v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) := by
  have hex : ∀ W : Place C₁ G₁, ∃! V : Place C₂ G₂,
      ∀ i : I₁, geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) V =
        v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) := by
    intro W
    apply exists_unique_geometricPlace_of_stage_family k₂ K₂ Ω₂
      q (q).monotone (q).surjective
      (fun i => v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W))
    intro i j hij
    rw [hv i j hij, geometricArtinStagePlaceRestrict_stage]
  let f : Place C₁ G₁ → Place C₂ G₂ := fun W => Classical.choose (hex W).exists
  have hf : ∀ (W : Place C₁ G₁) (i : I₁),
      geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) (f W) =
        v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) := by
    intro W
    exact Classical.choose_spec (hex W).exists
  have hfinj : Function.Injective f := by
    intro W V hWV
    apply geometricPlace_eq_of_stage_eq k₁ K₁ Ω₁ W V
    intro i
    apply (v i).injective
    rw [← hf W i, ← hf V i, hWV]
  have hfsurj : Function.Surjective f := by
    intro V
    let w : ∀ i : I₁, Place k₁ (geometricArtinStageField k₁ K₁ Ω₁ i) := fun i =>
      (v i).symm (geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) V)
    have hw : ∀ (i j : I₁) (hij : i ≤ j),
        geometricArtinStagePlaceRestrict k₁ K₁ Ω₁ i j hij (w j) = w i := by
      intro i j hij
      apply (v i).injective
      rw [← hv]
      change geometricArtinStagePlaceRestrict k₂ K₂ Ω₂ (q i) (q j)
          ((q).monotone hij) (v j ((v j).symm
            (geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q j) V))) =
        v i ((v i).symm (geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) V))
      rw [(v j).apply_symm_apply, (v i).apply_symm_apply,
        geometricArtinStagePlaceRestrict_stage]
    obtain ⟨W, hW, _⟩ := exists_unique_geometricPlace_of_stage_family k₁ K₁ Ω₁
      (id : I₁ → I₁) (fun _ _ hij => hij) (fun i => ⟨i, rfl⟩) w hw
    refine ⟨W, ?_⟩
    apply geometricPlace_eq_of_stage_eq k₂ K₂ Ω₂ (f W) V
    intro j
    obtain ⟨i, rfl⟩ := (q).surjective j
    have hWi : geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W = w i := hW i
    exact (hf W i).trans ((congrArg (v i) hWi).trans ((v i).apply_symm_apply _))
  let e : Place C₁ G₁ ≃ Place C₂ G₂ := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨e, fun i W => hf W i, ?_⟩
  intro e' he'
  apply Equiv.ext
  intro W
  apply geometricPlace_eq_of_stage_eq k₂ K₂ Ω₂ (e' W) (e W)
  intro j
  obtain ⟨i, rfl⟩ := (q).surjective j
  exact (he' i W).trans (hf W i).symm

/-- The geometric place bijection constructed from the actual compatible
finite-stage bijections. -/
def geometricPlaceEquivOfStageEquivs : Place C₁ G₁ ≃ Place C₂ G₂ :=
  Classical.choose
    (exists_unique_geometricPlaceEquiv_of_stageEquivs k₁ K₁ Ω₁ k₂ K₂ Ω₂ v hv).exists

/-- The constructed geometric bijection retains every original stage
restriction, with no additional point correspondence as an input. -/
theorem geometricPlaceEquivOfStageEquivs_stage
    (i : I₁) (W : Place C₁ G₁) :
    geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i)
        (geometricPlaceEquivOfStageEquivs k₁ K₁ Ω₁ k₂ K₂ Ω₂ v hv W) =
      v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) :=
  Classical.choose_spec
    (exists_unique_geometricPlaceEquiv_of_stageEquivs k₁ K₁ Ω₁ k₂ K₂ Ω₂ v hv).exists i W

end FunctionField.RayClass
