/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.AbsoluteTensorDiagonal
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.HasseNoether
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.TensorBrauerLocalization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.TensorDiagonalCoordinates
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FiniteIdeleLocalH2
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleLocalBrauerRestriction

/-! # The invariant-sum kernel for the actual global idèle sequence -/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ClassFieldTheory.Brauer
open ClassFieldTower.Martinet.Shafarevich
open ContinuousCohomology IsDedekindDomain NumberField
open scoped DirectSum NumberField TensorProduct

namespace GlobalClassFieldTheory.Cohomology

variable (K : Type) [Field K] [NumberField K]
  (E : Type) [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

local notation "G" => Gal(E/K)
local notation "C" => finiteIdeleShortComplex K E
local notation "H" => groupCohomology.functor ℤ G 2
local notation "BrRel" => continuousCohomology 2 (galoisUnitsRep K E)

/-- The actual diagonal map of field-unit cohomology into full relative idèle cohomology. -/
@[expose]
def relativeBrauerIdeleH2Map : BrRel →+ groupCohomology (C).X₂ 2 :=
  let m := (H).map (finiteFieldUnitsIdeleRepHom K E)
  m.hom.toAddMonoidHom.comp (discreteOriginalH2Equiv (galoisUnitsRep K E)).toAddMonoidHom

/-- Quotient the original idèles by principal idèles, then use the standard idèle class group. -/
@[expose]
def fullIdeleClassH2Map :
    groupCohomology (C).X₂ 2 →+ groupCohomology (standardIdeleClassRep K E) 2 :=
  ((H).map ((C).g ≫ (relativeToStandardIdeleClassRepIso K E).hom)).hom.toAddMonoidHom

private def fullIdeleBrauerCoordinate :
    (w : Place K) → groupCohomology (C).X₂ 2 →+ Br (placeCompletion K w)
  | .inl v => fullIdeleFiniteBrauerCoordinate (E := E) v
  | .inr v => fullIdeleInfiniteBrauerCoordinate (E := E) v

private theorem exists_fullIdeleBrauerSupport (x : groupCohomology (C).X₂ 2) :
    ∃ S : Finset (Place K), ∀ w, w ∉ S → fullIdeleBrauerCoordinate K E w x = 0 := by
  classical
  obtain ⟨S, hS, y, hy⟩ := exists_supportedIdeleH2_preimage K E x
  refine ⟨S.disjSum Finset.univ, fun w hw => ?_⟩
  cases w with
  | inr v => exact (hw (Finset.inr_mem_disjSum.mpr (Finset.mem_univ v))).elim
  | inl v =>
    have hv : v ∉ S := fun h => hw (Finset.inl_mem_disjSum.mpr h)
    have hu := chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
      (K := K) (L := E) v (fun h => hv (hS h))
    have hcoeff : supportedIdeleInclusionRepHom K E S ≫ finiteIdeleFiniteTensorRepHom K E v =
        supportedSPlaceOutsideTensorRepHom K E S ⟨v, hv⟩ := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro a
      rfl
    let p := finiteIdeleFiniteTensorRepHom K E v
    let j := supportedIdeleInclusionRepHom K E S
    have hz : (H).map p x = 0 := by
      calc
        _ = (H).map p ((H).map j y) := congrArg ((H).map p) hy.symm
        _ = (H).map (j ≫ p) y := ConcreteCategory.congr_hom ((H).map_comp j p).symm y
        _ = (H).map (supportedSPlaceOutsideTensorRepHom K E S ⟨v, hv⟩) y :=
          ConcreteCategory.congr_hom (congrArg (H).map hcoeff) y
        _ = 0 := supportedSPlaceOutsideTensorH2_eq_zero K E S ⟨v, hv⟩ hu y
    change finiteTensorH2ToBrauerOfExtension E v
      ((H).map (finiteIdeleFiniteTensorRepHom K E v) x) = 0
    exact (congrArg (finiteTensorH2ToBrauerOfExtension E v) hz).trans
      (map_zero (finiteTensorH2ToBrauerOfExtension E v))

private def fullIdeleBrauerTupleRaw (x : groupCohomology (C).X₂ 2) :
    ⨁ w : Place K, Br (placeCompletion K w) := by
  classical
  exact DFinsupp.mk (exists_fullIdeleBrauerSupport K E x).choose
    (fun w => fullIdeleBrauerCoordinate K E w.val x)

private theorem fullIdeleBrauerTupleRaw_apply (x : groupCohomology (C).X₂ 2) (w : Place K) :
    fullIdeleBrauerTupleRaw K E x w = fullIdeleBrauerCoordinate K E w x := by
  classical
  by_cases hw : w ∈ (exists_fullIdeleBrauerSupport K E x).choose
  · exact DFinsupp.mk_of_mem hw
  · exact (DFinsupp.mk_of_notMem hw).trans
      ((exists_fullIdeleBrauerSupport K E x).choose_spec w hw).symm

/-- The actual finite-support tuple of tensor Brauer classes of a full idèle cohomology class. -/
def fullIdeleBrauerTuple :
    groupCohomology (C).X₂ 2 →+ (⨁ w : Place K, Br (placeCompletion K w)) where
  toFun := fullIdeleBrauerTupleRaw K E
  map_zero' := DFinsupp.ext fun w => by
    rw [fullIdeleBrauerTupleRaw_apply, map_zero, DFinsupp.zero_apply]
  map_add' x y := DFinsupp.ext fun w => by
    change fullIdeleBrauerTupleRaw K E (x + y) w =
      fullIdeleBrauerTupleRaw K E x w + fullIdeleBrauerTupleRaw K E y w
    simp only [fullIdeleBrauerTupleRaw_apply, map_add]

private theorem fullIdeleBrauerTuple_apply (x : groupCohomology (C).X₂ 2) (w : Place K) :
    fullIdeleBrauerTuple K E x w = fullIdeleBrauerCoordinate K E w x :=
  fullIdeleBrauerTupleRaw_apply K E x w

/-- The finite coordinate is the actual finite tensor cohomology projection. -/
theorem fullIdeleBrauerTuple_finite_apply
    (x : groupCohomology (C).X₂ 2) (v : HeightOneSpectrum (𝓞 K)) :
    fullIdeleBrauerTuple K E x (Sum.inl v) =
      finiteTensorH2ToBrauerOfExtension E v ((H).map (finiteIdeleFiniteTensorRepHom K E v) x) :=
  fullIdeleBrauerTupleRaw_apply K E x (Sum.inl v)

/-- The infinite coordinate is the actual infinite tensor cohomology projection. -/
theorem fullIdeleBrauerTuple_infinite_apply
    (x : groupCohomology (C).X₂ 2) (v : InfinitePlace K) :
    fullIdeleBrauerTuple K E x (Sum.inr v) =
      infiniteTensorH2ToBrauerOfExtension E v ((H).map (finiteIdeleInfiniteTensorRepHom K E v) x) :=
  fullIdeleBrauerTupleRaw_apply K E x (Sum.inr v)

omit [NumberField E] [FiniteDimensional K E] [IsGalois K E] in
private theorem finite_diagonal_comp (v : HeightOneSpectrum (𝓞 K)) :
    finiteFieldUnitsIdeleRepHom K E ≫ finiteIdeleFiniteTensorRepHom K E v =
      tensorDiagonalRepHom (v.adicCompletion K) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  exact finitePlaceTensorDiagonal_principal v (a.toMul : Eˣ)

omit [NumberField E] [FiniteDimensional K E] [IsGalois K E] in
private theorem infinite_diagonal_comp (v : InfinitePlace K) :
    finiteFieldUnitsIdeleRepHom K E ≫ finiteIdeleInfiniteTensorRepHom K E v =
      tensorDiagonalRepHom v.Completion := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  exact infinitePlaceTensorDiagonal_principal v (a.toMul : Eˣ)

omit [NumberField E] in
private theorem finite_diagonal_localization (i : E →ₐ[K] SeparableClosure K)
    (v : HeightOneSpectrum (𝓞 K)) (a : BrRel) :
    finiteTensorH2ToBrauerOfExtension E v
      ((H).map (finiteIdeleFiniteTensorRepHom K E v) (relativeBrauerIdeleH2Map K E a)) =
      finitePlaceRestriction K v (relativeInflationOfEmbedding i a) := by
  let p := finiteFieldUnitsIdeleRepHom K E
  let q := finiteIdeleFiniteTensorRepHom K E v
  let x := discreteOriginalH2Equiv (galoisUnitsRep K E) a
  have hcomp : (H).map q ((H).map p x) = (H).map (tensorDiagonalRepHom (v.adicCompletion K)) x :=
    (ConcreteCategory.congr_hom ((H).map_comp p q).symm x).trans
      (ConcreteCategory.congr_hom (congrArg (H).map (finite_diagonal_comp K E v)) x)
  exact (congrArg (finiteTensorH2ToBrauerOfExtension E v) hcomp).trans
    (finiteTensorH2ToBrauerOfExtension_diagonal i v a)

omit [NumberField E] in
private theorem infinite_diagonal_localization (i : E →ₐ[K] SeparableClosure K)
    (v : InfinitePlace K) (a : BrRel) :
    infiniteTensorH2ToBrauerOfExtension E v
      ((H).map (finiteIdeleInfiniteTensorRepHom K E v) (relativeBrauerIdeleH2Map K E a)) =
      infinitePlaceRestriction K v (relativeInflationOfEmbedding i a) := by
  let p := finiteFieldUnitsIdeleRepHom K E
  let q := finiteIdeleInfiniteTensorRepHom K E v
  let x := discreteOriginalH2Equiv (galoisUnitsRep K E) a
  have hcomp : (H).map q ((H).map p x) = (H).map (tensorDiagonalRepHom v.Completion) x :=
    (ConcreteCategory.congr_hom ((H).map_comp p q).symm x).trans
      (ConcreteCategory.congr_hom (congrArg (H).map (infinite_diagonal_comp K E v)) x)
  exact (congrArg (infiniteTensorH2ToBrauerOfExtension E v) hcomp).trans
    (infiniteTensorH2ToBrauerOfExtension_diagonal i v a)

omit [IsGalois K E] in
/-- The standard idèle class image of an actual diagonal field-unit class vanishes. -/
theorem fullIdeleClassH2Map_relativeBrauerIdeleH2Map (a : BrRel) :
    fullIdeleClassH2Map K E (relativeBrauerIdeleH2Map K E a) = 0 := by
  let p := finiteFieldUnitsIdeleRepHom K E
  have hp : p ≫ (C).g = 0 := by
    change finiteFieldUnitsIdeleRepHom K E ≫ (C).g = 0
    rw [finiteFieldUnitsIdeleRepHom_factor, Category.assoc, (C).zero, comp_zero]
  let e : (C).X₃ ⟶ standardIdeleClassRep K E := (relativeToStandardIdeleClassRepIso K E).hom
  let x := discreteOriginalH2Equiv (galoisUnitsRep K E) a
  have hz : p ≫ ((C).g ≫ e) = 0 :=
    (Category.assoc p (C).g e).symm.trans
      ((congrArg (· ≫ e) hp).trans zero_comp)
  have hm : (H).map p ≫ (H).map ((C).g ≫ e) = 0 :=
    (((H).map_comp p ((C).g ≫ e)).symm.trans (congrArg (H).map hz)).trans ((H).map_zero _ _)
  exact ConcreteCategory.congr_hom hm x

omit [IsGalois K E] in
private theorem exists_principal_diagonal_of_class_eq_zero (x : groupCohomology (C).X₂ 2)
    (hx : fullIdeleClassH2Map K E x = 0) :
    ∃ a : BrRel, relativeBrauerIdeleH2Map K E a = x := by
  let e := relativeToStandardIdeleClassRepIso K E
  have hz : ((H).map (C).g) x = 0 := by
    apply ((H).mapIso e).toLinearEquiv.injective
    change (H).map e.hom ((H).map (C).g x) = (H).map e.hom 0
    calc
      _ = (H).map ((C).g ≫ e.hom) x :=
        ConcreteCategory.congr_hom ((H).map_comp (C).g e.hom).symm x
      _ = 0 := hx
      _ = _ := (map_zero ((H).map e.hom).hom).symm
  have hex := groupCohomology.mapShortComplex₂_exact (finiteIdeleShortComplex_shortExact K E) 2
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex x hz
  let p := fieldUnitsPrincipalIdeleRepIso K E
  let f := ((H).mapIso p).toLinearEquiv
  let e₂ := discreteOriginalH2Equiv (galoisUnitsRep K E)
  let a := e₂.symm (f.symm y)
  have ha : e₂ a = f.symm y := e₂.apply_symm_apply _
  have hf : ((H).map p.hom) (f.symm y) = y := f.apply_symm_apply y
  refine ⟨a, ?_⟩
  have hcomp : (H).map (finiteFieldUnitsIdeleRepHom K E) =
      (H).map p.hom ≫ (H).map (C).f :=
    (congrArg (H).map (finiteFieldUnitsIdeleRepHom_factor K E)).trans ((H).map_comp p.hom (C).f)
  change (H).map (finiteFieldUnitsIdeleRepHom K E) (e₂ a) = x
  exact (ConcreteCategory.congr_hom hcomp (e₂ a)).trans
    ((congrArg (fun t => (H).map (C).f ((H).map p.hom t)) ha).trans
      ((congrArg ((H).map (C).f) hf).trans hy))

/-- The canonical tuple of a principal diagonal is the actual global Brauer localization. -/
theorem fullIdeleBrauerTuple_relativeBrauerIdeleH2Map (i : E →ₐ[K] SeparableClosure K) (a : BrRel) :
    fullIdeleBrauerTuple K E (relativeBrauerIdeleH2Map K E a) =
      localization K (relativeInflationOfEmbedding i a) := by
  apply DirectSum.ext
  intro w
  rw [localization_apply]
  cases w with
  | inl v =>
    exact (fullIdeleBrauerTuple_finite_apply K E _ v).trans
      (finite_diagonal_localization K E i v a)
  | inr v =>
    exact (fullIdeleBrauerTuple_infinite_apply K E _ v).trans
      (infinite_diagonal_localization K E i v a)

/-- The sum of the arithmetic invariants of the actual full idèle class's coordinates. -/
@[expose]
def fullIdeleBrauerInvariantSum : groupCohomology (C).X₂ 2 →+ AddCircle (1 : ℚ) :=
  (sumLocalInv K).comp (fullIdeleBrauerTuple K E)

/-- A full idèle class with zero standard class has zero invariant sum. -/
theorem fullIdeleBrauerInvariantSum_eq_zero_of_class_eq_zero (x : groupCohomology (C).X₂ 2)
    (hx : fullIdeleClassH2Map K E x = 0) :
    fullIdeleBrauerInvariantSum K E x = 0 := by
  obtain ⟨a, rfl⟩ := exists_principal_diagonal_of_class_eq_zero K E x hx
  let i : E →ₐ[K] SeparableClosure K := IsSepClosed.lift
  change sumLocalInv K (fullIdeleBrauerTuple K E (relativeBrauerIdeleH2Map K E a)) = 0
  rw [fullIdeleBrauerTuple_relativeBrauerIdeleH2Map K E i]
  exact sumLocalInv_localization_eq_zero K _

/-- The actual invariant on the image of the standard idèle class map. -/
def fullIdeleClassRangeInvariant :
    (fullIdeleClassH2Map K E).range →+ AddCircle (1 : ℚ) :=
  let f := fullIdeleClassH2Map K E
  (QuotientAddGroup.lift f.ker (fullIdeleBrauerInvariantSum K E)
    (fun x hx => fullIdeleBrauerInvariantSum_eq_zero_of_class_eq_zero K E x hx)).comp
      (QuotientAddGroup.quotientKerEquivRange f).symm.toAddMonoidHom

/-- On the original idèle representative the induced invariant is the actual sum. -/
theorem fullIdeleClassRangeInvariant_apply (x : groupCohomology (C).X₂ 2) :
    fullIdeleClassRangeInvariant K E ⟨fullIdeleClassH2Map K E x, ⟨x, rfl⟩⟩ =
      fullIdeleBrauerInvariantSum K E x := by
  let f := fullIdeleClassH2Map K E
  let e := QuotientAddGroup.quotientKerEquivRange f
  have h : e.symm ⟨f x, ⟨x, rfl⟩⟩ = QuotientAddGroup.mk x := by
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  have hker : f.ker ≤ (fullIdeleBrauerInvariantSum K E).ker :=
    fun y hy => fullIdeleBrauerInvariantSum_eq_zero_of_class_eq_zero K E y hy
  change QuotientAddGroup.lift f.ker (fullIdeleBrauerInvariantSum K E) hker
    (e.symm ⟨f x, ⟨x, rfl⟩⟩) = _
  rw [h]
  rfl

/-- A finitely supported tuple with zero sum that splits over the actual
upper completions gives a principal diagonal for the original idèle class. -/
theorem exists_relativeBrauerIdeleH2Map_eq_of_invariantSum_eq_zero
    (x : groupCohomology (C).X₂ 2) (t : ⨁ w : Place K, Br (placeCompletion K w))
    (hfinite : ∀ v : HeightOneSpectrum (𝓞 K), t (Sum.inl v) =
      finiteTensorH2ToBrauerOfExtension E v ((H).map (finiteIdeleFiniteTensorRepHom K E v) x))
    (hinfinite : ∀ v : InfinitePlace K, t (Sum.inr v) =
      infiniteTensorH2ToBrauerOfExtension E v ((H).map (finiteIdeleInfiniteTensorRepHom K E v) x))
    (hsum : sumLocalInv K t = 0)
    (hsplitFinite : ∀ w : HeightOneSpectrum (𝓞 E),
      let v := finitePlaceBelow (K := K) w
      restrict (finitePlaceAdicCompletionMap K E v ⟨w, rfl⟩) (t (Sum.inl v)) = 0)
    (hsplitInfinite : ∀ w : InfinitePlace E,
      let v := infinitePlaceBelow (K := K) w
      restrict (infinitePlaceBrauerCompletionMap v w rfl) (t (Sum.inr v)) = 0) :
    ∃ a : BrRel, relativeBrauerIdeleH2Map K E a = x := by
  obtain ⟨b, hb, _⟩ := (existsUnique_localization_iff K t).mpr hsum
  have hbf (v : HeightOneSpectrum (𝓞 K)) : finitePlaceRestriction K v b = t (Sum.inl v) :=
    (localization_apply K b (Sum.inl v)).symm.trans (DFunLike.congr_fun hb (Sum.inl v))
  have hbi (v : InfinitePlace K) : infinitePlaceRestriction K v b = t (Sum.inr v) :=
    (localization_apply K b (Sum.inr v)).symm.trans (DFunLike.congr_fun hb (Sum.inr v))
  have hrestrict : restrict (algebraMap K E) b = 0 := by
    apply restrict_eq_zero_of_localCompletionRestrictions E b
    · intro w
      let v := finitePlaceBelow (K := K) w
      change restrict (finitePlaceAdicCompletionMap K E v ⟨w, rfl⟩)
        (finitePlaceRestriction K v b) = 0
      rw [hbf]
      exact hsplitFinite w
    · intro w
      let v := infinitePlaceBelow (K := K) w
      change restrict (infinitePlaceBrauerCompletionMap v w rfl)
        (infinitePlaceRestriction K v b) = 0
      rw [hbi]
      exact hsplitInfinite w
  let i : E →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨a, ha⟩ := exists_relativeInflationOfEmbedding_eq_of_restrict_eq_zero i b hrestrict
  refine ⟨a, sub_eq_zero.mp ?_⟩
  apply finiteIdeleH2_eq_zero_of_localizations K E
  · intro v
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply finiteTensorH2ToBrauerOfExtension_injective E v
    exact (finite_diagonal_localization K E i v a).trans
      ((congrArg (finitePlaceRestriction K v) ha).trans ((hbf v).trans (hfinite v)))
  · intro v
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply infiniteTensorH2ToBrauerOfExtension_injective E v
    exact (infinite_diagonal_localization K E i v a).trans
      ((congrArg (infinitePlaceRestriction K v) ha).trans ((hbi v).trans (hinfinite v)))

/-- The same zero-sum criterion kills the image in the original standard idèle class group. -/
theorem fullIdeleClassH2Map_eq_zero_of_invariantSum_eq_zero
    (x : groupCohomology (C).X₂ 2) (t : ⨁ w : Place K, Br (placeCompletion K w))
    (hfinite : ∀ v : HeightOneSpectrum (𝓞 K), t (Sum.inl v) =
      finiteTensorH2ToBrauerOfExtension E v ((H).map (finiteIdeleFiniteTensorRepHom K E v) x))
    (hinfinite : ∀ v : InfinitePlace K, t (Sum.inr v) =
      infiniteTensorH2ToBrauerOfExtension E v ((H).map (finiteIdeleInfiniteTensorRepHom K E v) x))
    (hsum : sumLocalInv K t = 0)
    (hsplitFinite : ∀ w : HeightOneSpectrum (𝓞 E),
      let v := finitePlaceBelow (K := K) w
      restrict (finitePlaceAdicCompletionMap K E v ⟨w, rfl⟩) (t (Sum.inl v)) = 0)
    (hsplitInfinite : ∀ w : InfinitePlace E,
      let v := infinitePlaceBelow (K := K) w
      restrict (infinitePlaceBrauerCompletionMap v w rfl) (t (Sum.inr v)) = 0) :
    fullIdeleClassH2Map K E x = 0 := by
  obtain ⟨a, rfl⟩ := exists_relativeBrauerIdeleH2Map_eq_of_invariantSum_eq_zero K E x t
    hfinite hinfinite hsum hsplitFinite hsplitInfinite
  exact fullIdeleClassH2Map_relativeBrauerIdeleH2Map K E a

/-- Zero sum on the canonical tuple kills the standard class once the
actual restrictions at the upper completions vanish. -/
theorem fullIdeleClassH2Map_eq_zero_of_sumLocalInv_eq_zero
    (x : groupCohomology (C).X₂ 2) (hsum : sumLocalInv K (fullIdeleBrauerTuple K E x) = 0)
    (hsplitFinite : ∀ w : HeightOneSpectrum (𝓞 E),
      let v := finitePlaceBelow (K := K) w
      restrict (finitePlaceAdicCompletionMap K E v ⟨w, rfl⟩)
        (fullIdeleBrauerTuple K E x (Sum.inl v)) = 0)
    (hsplitInfinite : ∀ w : InfinitePlace E,
      let v := infinitePlaceBelow (K := K) w
      restrict (infinitePlaceBrauerCompletionMap v w rfl)
        (fullIdeleBrauerTuple K E x (Sum.inr v)) = 0) :
    fullIdeleClassH2Map K E x = 0 :=
  fullIdeleClassH2Map_eq_zero_of_invariantSum_eq_zero K E x (fullIdeleBrauerTuple K E x)
    (fullIdeleBrauerTuple_finite_apply K E x) (fullIdeleBrauerTuple_infinite_apply K E x)
    hsum hsplitFinite hsplitInfinite

/-- A class of full idèle cohomology vanishes in class cohomology when the
invariant sum vanishes. The coordinate maps already split at all upper places. -/
theorem fullIdeleClassH2Map_eq_zero_of_invariantSum
    (x : groupCohomology (C).X₂ 2) (hx : fullIdeleBrauerInvariantSum K E x = 0) :
    fullIdeleClassH2Map K E x = 0 := by
  refine fullIdeleClassH2Map_eq_zero_of_sumLocalInv_eq_zero K E x hx ?_ ?_
  · intro W
    have h := fullIdeleFiniteBrauerCoordinate_restrict_top (K := K) (E := E) W x
    with_reducible_and_instances
      simpa only [fullIdeleBrauerTuple_apply, fullIdeleBrauerCoordinate] using h
  · intro W
    have h := fullIdeleInfiniteBrauerCoordinate_restrict_top (K := K) (E := E) W x
    with_reducible_and_instances
      simpa only [fullIdeleBrauerTuple_apply, fullIdeleBrauerCoordinate] using h

/-- Once the actual upper-completion restrictions vanish, the arithmetic invariant
is injective on the actual image of full idèle cohomology in standard class cohomology. -/
theorem fullIdeleClassRangeInvariant_injective
    (hsplitFinite : ∀ (x : groupCohomology (C).X₂ 2) (w : HeightOneSpectrum (𝓞 E)),
      let v := finitePlaceBelow (K := K) w
      restrict (finitePlaceAdicCompletionMap K E v ⟨w, rfl⟩)
        (fullIdeleBrauerTuple K E x (Sum.inl v)) = 0)
    (hsplitInfinite : ∀ (x : groupCohomology (C).X₂ 2) (w : InfinitePlace E),
      let v := infinitePlaceBelow (K := K) w
      restrict (infinitePlaceBrauerCompletionMap v w rfl)
        (fullIdeleBrauerTuple K E x (Sum.inr v)) = 0) :
    Function.Injective (fullIdeleClassRangeInvariant K E) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨y, ⟨x, rfl⟩⟩ hy
  have hsum : sumLocalInv K (fullIdeleBrauerTuple K E x) = 0 :=
    (fullIdeleClassRangeInvariant_apply K E x).symm.trans hy
  apply Subtype.ext
  exact fullIdeleClassH2Map_eq_zero_of_sumLocalInv_eq_zero K E x hsum
    (hsplitFinite x) (hsplitInfinite x)

end GlobalClassFieldTheory.Cohomology
