/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteTensorInvariantRange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.TensorBrauerLocalization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleH2KernelByInvariantSum

/-! # The sum of the actual local invariants of supported idèle classes -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Martinet.Shafarevich
open ContinuousCohomology IsDedekindDomain NumberField
open scoped DirectSum NumberField TensorProduct

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

variable (K : Type) [Field K] [NumberField K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K))
  (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "finiteBrauerMap" =>
  finiteTensorH2ToBrauerOfExtension (K := K) (E : Type)
local notation "infiniteBrauerMap" =>
  infiniteTensorH2ToBrauerOfExtension (K := K) (E : Type)

open scoped Classical in
/-- The finite or archimedean component supplied by the supported tensor class. -/
def supportedBrauerValue (x : SupportedLocalH2 K E S) :
    (w : Place K) → Br (placeCompletion K w)
  | .inl v => if hv : v ∈ S then finiteBrauerMap v (x.1 ⟨v, hv⟩) else 0
  | .inr v => infiniteBrauerMap v (x.2 v)

/-- A supported finite coordinate is mapped by its finite tensor Brauer map. -/
theorem supportedBrauerValue_finite_of_mem
    (x : SupportedLocalH2 K E S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    supportedBrauerValue K E S x (Sum.inl v) = finiteBrauerMap v (x.1 ⟨v, hv⟩) := by
  simp only [supportedBrauerValue, dite_eq_left hv]

/-- A finite coordinate outside the specified support vanishes. -/
theorem supportedBrauerValue_finite_of_notMem
    (x : SupportedLocalH2 K E S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    supportedBrauerValue K E S x (Sum.inl v) = 0 := by
  simp only [supportedBrauerValue, dite_eq_right hv]

/-- An archimedean coordinate is mapped by its archimedean tensor Brauer map. -/
theorem supportedBrauerValue_infinite
    (x : SupportedLocalH2 K E S) (v : InfinitePlace K) :
    supportedBrauerValue K E S x (Sum.inr v) = infiniteBrauerMap v (x.2 v) := by
  simp only [supportedBrauerValue]

/-- Build the tuple on the finite support consisting of the specified places
and all archimedean places. -/
def supportedBrauerTupleRaw (x : SupportedLocalH2 K E S) :
    ⨁ w : Place K, Br (placeCompletion K w) := by
  classical
  exact DFinsupp.mk (S.disjSum Finset.univ) (fun w => supportedBrauerValue K E S x w.val)

private theorem supportedBrauerTupleRaw_apply (x : SupportedLocalH2 K E S) (w : Place K) :
    supportedBrauerTupleRaw K E S x w = supportedBrauerValue K E S x w := by
  classical
  cases w with
  | inl v =>
    by_cases h : v ∈ S
    · have hm : Sum.inl v ∈ S.disjSum (Finset.univ : Finset (InfinitePlace K)) :=
        Finset.inl_mem_disjSum.mpr h
      exact DFinsupp.mk_of_mem hm
    · have hn : Sum.inl v ∉ S.disjSum (Finset.univ : Finset (InfinitePlace K)) :=
        fun hv => h (Finset.inl_mem_disjSum.mp hv)
      exact (DFinsupp.mk_of_notMem hn).trans
        (supportedBrauerValue_finite_of_notMem K E S x v h).symm
  | inr v =>
    have hm : Sum.inr v ∈ S.disjSum (Finset.univ : Finset (InfinitePlace K)) :=
      Finset.inr_mem_disjSum.mpr (Finset.mem_univ v)
    exact DFinsupp.mk_of_mem hm

/-- A supported tensor class gives the original finite and archimedean Brauer classes. -/
def supportedBrauerTuple : SupportedLocalH2 K E S →+ (⨁ w : Place K, Br (placeCompletion K w)) where
  toFun := supportedBrauerTupleRaw K E S
  map_zero' := by
    classical
    apply DFinsupp.ext
    intro w
    rw [supportedBrauerTupleRaw_apply, DFinsupp.zero_apply]
    cases w with
    | inl v =>
      by_cases h : v ∈ S
      · simp only [supportedBrauerValue_finite_of_mem K E S _ v h, Prod.fst_zero,
          Pi.zero_apply, map_zero]
      · exact supportedBrauerValue_finite_of_notMem K E S _ v h
    | inr v => simp only [supportedBrauerValue_infinite, Prod.snd_zero, Pi.zero_apply, map_zero]
  map_add' x y := by
    classical
    apply DFinsupp.ext
    intro w
    rw [DFinsupp.add_apply, supportedBrauerTupleRaw_apply,
      supportedBrauerTupleRaw_apply, supportedBrauerTupleRaw_apply]
    cases w with
    | inl v =>
      by_cases h : v ∈ S
      · simp only [supportedBrauerValue_finite_of_mem K E S _ v h, Prod.fst_add,
          Pi.add_apply, map_add]
      · simp only [supportedBrauerValue_finite_of_notMem K E S _ v h, add_zero]
    | inr v => simp only [supportedBrauerValue_infinite, Prod.snd_add, Pi.add_apply, map_add]

/-- The supported Brauer tuple evaluates at its original component. -/
theorem supportedBrauerTuple_apply (x : SupportedLocalH2 K E S) (w : Place K) :
    supportedBrauerTuple K E S x w = supportedBrauerValue K E S x w :=
  supportedBrauerTupleRaw_apply K E S x w

/-- The supported invariant sum is the arithmetic sum on the actual direct sum of places. -/
def supportedBrauerInvariantSum : SupportedLocalH2 K E S →+ AddCircle (1 : ℚ) :=
  (sumLocalInv K).comp (supportedBrauerTuple K E S)

local notation "S₀" => ideleClassHerbrandSupport (K := K) (L := E)

section FullIdeleComparison

variable [NumberField E]

local notation "H" => groupCohomology.functor ℤ Gal(E/K) 2
local notation "I" => ShortComplex.X₂ (finiteIdeleShortComplex K E)

/-- Include the supported class with the specified local tensor coordinates
into the original full idèle cohomology. -/
def supportedFullIdeleH2
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v) :
    SupportedLocalH2 K E S →+ groupCohomology I 2 :=
  let f := (H).map (supportedIdeleInclusionRepHom K E S)
  let e := supportedSPlaceH2LocalizationsEquiv K E S hfin
  f.hom.toAddMonoidHom.comp e.symm.toAddMonoidHom

private theorem supportedFullIdeleH2_finite_apply
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (x : SupportedLocalH2 K E S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    (H).map (finiteIdeleFiniteTensorRepHom K E v) (supportedFullIdeleH2 K E S hfin x) =
      x.1 ⟨v, hv⟩ := by
  let e := supportedSPlaceH2LocalizationsEquiv K E S hfin
  let y := e.symm x
  let i := supportedIdeleInclusionRepHom K E S
  let q := finiteIdeleFiniteTensorRepHom K E v
  let r := supportedSPlaceFiniteRepHom K E S ⟨v, hv⟩
  have hcoeff : i ≫ q = r := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl
  have hmap : (H).map q (supportedFullIdeleH2 K E S hfin x) = (H).map r y :=
    ConcreteCategory.congr_hom
      (((H).map_comp i q).symm.trans (congrArg (H).map hcoeff)) y
  have hx : (H).map r y = x.1 ⟨v, hv⟩ :=
    (supportedSPlaceH2Localization_apply K E S y ⟨v, hv⟩).symm.trans
      (congrArg (fun z : SupportedLocalH2 K E S => z.1 ⟨v, hv⟩) (e.apply_symm_apply x))
  exact hmap.trans hx

private theorem supportedFullIdeleH2_outside_eq_zero
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (x : SupportedLocalH2 K E S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    (H).map (finiteIdeleFiniteTensorRepHom K E v) (supportedFullIdeleH2 K E S hfin x) = 0 := by
  let e := supportedSPlaceH2LocalizationsEquiv K E S hfin
  let y := e.symm x
  let i := supportedIdeleInclusionRepHom K E S
  let q := finiteIdeleFiniteTensorRepHom K E v
  let r := supportedSPlaceOutsideTensorRepHom K E S ⟨v, hv⟩
  have hcoeff : i ≫ q = r := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl
  have hmap : (H).map q (supportedFullIdeleH2 K E S hfin x) = (H).map r y :=
    ConcreteCategory.congr_hom
      (((H).map_comp i q).symm.trans (congrArg (H).map hcoeff)) y
  exact hmap.trans (supportedSPlaceOutsideTensorH2_eq_zero K E S ⟨v, hv⟩ (hfin v hv) y)

private theorem supportedFullIdeleH2_infinite_apply
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (x : SupportedLocalH2 K E S) (v : InfinitePlace K) :
    (H).map (finiteIdeleInfiniteTensorRepHom K E v) (supportedFullIdeleH2 K E S hfin x) =
      x.2 v := by
  let e := supportedSPlaceH2LocalizationsEquiv K E S hfin
  let y := e.symm x
  let i := supportedIdeleInclusionRepHom K E S
  let q := finiteIdeleInfiniteTensorRepHom K E v
  let r := supportedSPlaceInfiniteRepHom K E S v
  have hcoeff : i ≫ q = r := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl
  have hmap : (H).map q (supportedFullIdeleH2 K E S hfin x) = (H).map r y :=
    ConcreteCategory.congr_hom
      (((H).map_comp i q).symm.trans (congrArg (H).map hcoeff)) y
  have hx : (H).map r y = x.2 v :=
    (supportedSPlaceInfiniteH2Localization_apply K E S y v).symm.trans
      (congrArg (fun z : SupportedLocalH2 K E S => z.2 v) (e.apply_symm_apply x))
  exact hmap.trans hx

private theorem fullIdeleBrauerTuple_supported_finite_of_mem
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (x : SupportedLocalH2 K E S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    fullIdeleBrauerTuple K E (supportedFullIdeleH2 K E S hfin x) (Sum.inl v) =
      supportedBrauerTuple K E S x (Sum.inl v) := by
  rw [fullIdeleBrauerTuple_finite_apply, supportedFullIdeleH2_finite_apply K E S hfin x v hv,
    supportedBrauerTuple_apply, supportedBrauerValue_finite_of_mem K E S x v hv]

private theorem fullIdeleBrauerTuple_supported_finite_of_notMem
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (x : SupportedLocalH2 K E S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    fullIdeleBrauerTuple K E (supportedFullIdeleH2 K E S hfin x) (Sum.inl v) =
      supportedBrauerTuple K E S x (Sum.inl v) := by
  rw [fullIdeleBrauerTuple_finite_apply, supportedFullIdeleH2_outside_eq_zero K E S hfin x v hv]
  have ht : supportedBrauerTuple K E S x (Sum.inl v) = 0 :=
    (supportedBrauerTuple_apply K E S x (Sum.inl v)).trans
      (supportedBrauerValue_finite_of_notMem K E S x v hv)
  exact (map_zero (finiteTensorH2ToBrauerOfExtension (E : Type) v)).trans ht.symm

private theorem fullIdeleBrauerTuple_supported_infinite
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (x : SupportedLocalH2 K E S) (v : InfinitePlace K) :
    fullIdeleBrauerTuple K E (supportedFullIdeleH2 K E S hfin x) (Sum.inr v) =
      supportedBrauerTuple K E S x (Sum.inr v) := by
  rw [fullIdeleBrauerTuple_infinite_apply, supportedFullIdeleH2_infinite_apply K E S hfin x v,
    supportedBrauerTuple_apply, supportedBrauerValue_infinite]

/-- Including the actual supported idèles preserves their full Brauer tuple. -/
theorem fullIdeleBrauerTuple_supportedFullIdeleH2
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (x : SupportedLocalH2 K E S) :
    fullIdeleBrauerTuple K E (supportedFullIdeleH2 K E S hfin x) =
      supportedBrauerTuple K E S x := by
  classical
  apply DFinsupp.ext
  intro w
  cases w with
  | inl v =>
    by_cases hv : v ∈ S
    · exact fullIdeleBrauerTuple_supported_finite_of_mem K E S hfin x v hv
    · exact fullIdeleBrauerTuple_supported_finite_of_notMem K E S hfin x v hv
  | inr v => exact fullIdeleBrauerTuple_supported_infinite K E S hfin x v

/-- Quotienting a supported class after inclusion gives its prescribed standard class. -/
theorem fullIdeleClassH2Map_supportedFullIdeleH2
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v) (x : SupportedLocalH2 K E S) :
    fullIdeleClassH2Map K E (supportedFullIdeleH2 K E S hfin x) =
      prescribedSupportedIdeleClassH2 K E S hfin x := by
  let p := supportedIdeleInclusionRepHom K E S
  let q := (finiteIdeleShortComplex K E).g
  let g := (supportedIdeleClassShortComplex K E S).g
  let i := (relativeToStandardIdeleClassRepIso K E).hom
  let y := (supportedSPlaceH2LocalizationsEquiv K E S hfin).symm x
  have h : p ≫ q = g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl
  have hcomp : p ≫ (q ≫ i) = g ≫ i :=
    (Category.assoc p q i).symm.trans (congrArg (· ≫ i) h)
  exact ConcreteCategory.congr_hom
    (((H).map_comp p (q ≫ i)).symm.trans (congrArg (H).map hcomp)) y

/-- Two supported representatives of the same standard class have the same sum of invariants. -/
theorem prescribedSupportedIdeleClassH2_ker_le_invariantSum_ker
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v) :
    (prescribedSupportedIdeleClassH2 K E S hfin).ker ≤ (supportedBrauerInvariantSum K E S).ker := by
  intro x hx
  let y := supportedFullIdeleH2 K E S hfin x
  have hy : fullIdeleClassH2Map K E y = 0 :=
    (fullIdeleClassH2Map_supportedFullIdeleH2 K E S hfin x).trans hx
  have hsum : fullIdeleBrauerInvariantSum K E y = 0 :=
    fullIdeleBrauerInvariantSum_eq_zero_of_class_eq_zero K E y hy
  change sumLocalInv K (fullIdeleBrauerTuple K E y) = 0 at hsum
  change sumLocalInv K (supportedBrauerTuple K E S x) = 0
  have h := congrArg (sumLocalInv K) (fullIdeleBrauerTuple_supportedFullIdeleH2 K E S hfin x)
  exact h.symm.trans hsum

/-- On the canonical support, the invariant sum vanishes on the kernel of the class map. -/
theorem prescribedHerbrandSupportIdeleClassH2_ker_le_invariantSum_ker :
    (prescribedHerbrandSupportIdeleClassH2 K E).ker ≤ (supportedBrauerInvariantSum K E S₀).ker :=
  prescribedSupportedIdeleClassH2_ker_le_invariantSum_ker K E S₀
    (fun v hv => chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
      (K := K) (L := E) v hv)

/-- The arithmetic invariant on the actual subgroup of idèle-class `H²`
represented by supported idèles. -/
def supportedIdeleClassRangeInvariant :
    (prescribedHerbrandSupportIdeleClassH2 K E).range →+ AddCircle (1 : ℚ) :=
  let f := prescribedHerbrandSupportIdeleClassH2 K E
  (QuotientAddGroup.lift f.ker (supportedBrauerInvariantSum K E S₀)
    (prescribedHerbrandSupportIdeleClassH2_ker_le_invariantSum_ker K E)).comp
      (QuotientAddGroup.quotientKerEquivRange f).symm.toAddMonoidHom

/-- The invariant evaluates by the arithmetic sum on the original supported representative. -/
theorem supportedIdeleClassRangeInvariant_apply (x : SupportedLocalH2 K E S₀) :
    supportedIdeleClassRangeInvariant K E
      ⟨prescribedHerbrandSupportIdeleClassH2 K E x, ⟨x, rfl⟩⟩ =
      supportedBrauerInvariantSum K E S₀ x := by
  let f := prescribedHerbrandSupportIdeleClassH2 K E
  let e := QuotientAddGroup.quotientKerEquivRange f
  have h : e.symm ⟨f x, ⟨x, rfl⟩⟩ = QuotientAddGroup.mk x := by
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  let g := supportedBrauerInvariantSum K E S₀
  let d := QuotientAddGroup.lift f.ker g
    (prescribedHerbrandSupportIdeleClassH2_ker_le_invariantSum_ker K E)
  change d (e.symm ⟨f x, ⟨x, rfl⟩⟩) = d (QuotientAddGroup.mk x)
  exact congrArg d h

end FullIdeleComparison

private def singleSupportedLocalH2
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (a : finiteTensorH2OfExtension E v) : SupportedLocalH2 K E S := by
  classical
  exact (Pi.single ⟨v, hv⟩ a, 0)

open scoped Classical in
private theorem supportedBrauerTuple_single (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (a : finiteTensorH2OfExtension E v) :
    supportedBrauerTuple K E S (singleSupportedLocalH2 K E S v hv a) =
      DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v)
        (finiteBrauerMap v a) := by
  classical
  let w : {u : HeightOneSpectrum (𝓞 K) // u ∈ S} := ⟨v, hv⟩
  let F : {u : HeightOneSpectrum (𝓞 K) // u ∈ S} → Type :=
    fun u => finiteTensorH2OfExtension E u.val
  let x := singleSupportedLocalH2 K E S v hv a
  let b := finiteBrauerMap v a
  let t := DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b
  change supportedBrauerTuple K E S x = t
  apply DFinsupp.ext
  intro p
  refine (supportedBrauerTuple_apply K E S x p).trans ?_
  cases p with
  | inl p =>
    by_cases h : p = v
    · subst p
      have hx : x.1 ⟨v, hv⟩ = a := Pi.single_eq_same (M := F) w a
      have ht : t (Sum.inl v) = b := DirectSum.of_eq_same _ _
      exact (supportedBrauerValue_finite_of_mem K E S x v hv).trans
        ((congrArg (finiteBrauerMap v) hx).trans ht.symm)
    · have ht : t (Sum.inl p) = 0 := DirectSum.of_eq_of_ne _ _ _ (fun h' => h (Sum.inl.inj h'))
      have hx : supportedBrauerValue K E S x (Sum.inl p) = 0 := by
        by_cases hp : p ∈ S
        · have hpw : (⟨p, hp⟩ : {u : HeightOneSpectrum (𝓞 K) // u ∈ S}) ≠ w :=
            fun h' => h (congrArg Subtype.val h')
          have hc : x.1 ⟨p, hp⟩ = 0 := Pi.single_eq_of_ne (M := F) hpw a
          exact (supportedBrauerValue_finite_of_mem K E S x p hp).trans
            ((congrArg (finiteBrauerMap p) hc).trans
              (map_zero (finiteBrauerMap p)))
        · exact supportedBrauerValue_finite_of_notMem K E S x p hp
      exact hx.trans ht.symm
  | inr p =>
    have ht : t (Sum.inr p) = 0 := DirectSum.of_eq_of_ne _ _ _ (by intro h; cases h)
    exact (supportedBrauerValue_infinite K E S x p).trans
      ((map_zero (infiniteBrauerMap p)).trans ht.symm)

open scoped Classical in
/-- A coordinate at a finite place in `S` realizes each invariant killed
by its completed local degree, with its actual tuple supported at that place. -/
theorem exists_supportedBrauerTuple_single_of_nsmul_eq_zero
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) (z : AddCircle (1 : ℚ))
    (hz : finiteTensorCompletedDegree E v • z = 0) :
    ∃ (x : SupportedLocalH2 K E S) (b : Br (v.adicCompletion K)),
      supportedBrauerTuple K E S x =
        DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b ∧
      finitePlaceBrauerInvariantEquiv K v b = z := by
  obtain ⟨a, ha⟩ := exists_finiteTensorInvariant_eq_of_nsmul_eq_zero (K := K) E v z hz
  refine ⟨singleSupportedLocalH2 K E S v hv a, finiteBrauerMap v a, ?_, ?_⟩
  · exact supportedBrauerTuple_single K E S v hv a
  · with_reducible_and_instances exact ha

open scoped Classical in
/-- When the supported tuple is concentrated at a finite place, its sum is that local invariant. -/
theorem supportedBrauerInvariantSum_eq_of_tuple_single
    (v : HeightOneSpectrum (𝓞 K)) (x : SupportedLocalH2 K E S)
    (b : Br (v.adicCompletion K))
    (hx : supportedBrauerTuple K E S x =
      DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b) :
    supportedBrauerInvariantSum K E S x = finitePlaceBrauerInvariantEquiv K v b := by
  calc
    supportedBrauerInvariantSum K E S x = sumLocalInv K (supportedBrauerTuple K E S x) :=
      AddMonoidHom.comp_apply (sumLocalInv K) (supportedBrauerTuple K E S) x
    _ = sumLocalInv K (DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b) :=
      congrArg (sumLocalInv K) hx
    _ = finitePlaceBrauerInvariantEquiv K v b := sumLocalInv_single K (Sum.inl v) b

/-- A single finite coordinate realizes the requested sum of invariants. -/
theorem exists_supportedBrauerInvariantSum_eq_of_nsmul_eq_zero
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) (z : AddCircle (1 : ℚ))
    (hz : finiteTensorCompletedDegree E v • z = 0) :
    ∃ x : SupportedLocalH2 K E S, supportedBrauerInvariantSum K E S x = z := by
  obtain ⟨x, b, htuple, hb⟩ := exists_supportedBrauerTuple_single_of_nsmul_eq_zero K E S v hv z hz
  exact ⟨x, (supportedBrauerInvariantSum_eq_of_tuple_single K E S v x b htuple).trans hb⟩

variable [NumberField E]

/-- The arithmetic invariant of the actual supported class image realizes
each value permitted by any one finite place in the canonical support. -/
theorem exists_supportedIdeleClassRangeInvariant_eq_of_nsmul_eq_zero
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S₀) (z : AddCircle (1 : ℚ))
    (hz : finiteTensorCompletedDegree E v • z = 0) :
    ∃ y : (prescribedHerbrandSupportIdeleClassH2 K E).range,
      supportedIdeleClassRangeInvariant K E y = z := by
  obtain ⟨x, hx⟩ := exists_supportedBrauerInvariantSum_eq_of_nsmul_eq_zero K E S₀ v hv z hz
  exact ⟨⟨prescribedHerbrandSupportIdeleClassH2 K E x, ⟨x, rfl⟩⟩,
    (supportedIdeleClassRangeInvariant_apply K E x).trans hx⟩

end GlobalClassFieldTheory.Cohomology
