/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilReciprocityDegree
public import Nyll.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ProfiniteUnits

/-!
# Local reciprocity with the ordinary topology

The absolute Artin map identifies the unit group with the full zero-degree
subgroup. Retaining the discrete integral degree on the absolute
abelianization gives the quotient topology of the Weil abelianization.
-/

@[expose] public section

open scoped Topology ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation LocalFieldTheory ProCGroups.Abelian
open LocalFieldTheory.IsNonarchimedeanLocalField

universe u v

/-- A bijective continuous homomorphism preserving a discrete degree is an
isomorphism of topological groups when the source degree has compact kernel. -/
noncomputable def continuousMulEquivOfCompactDegreeKernel
    {A : Type u} {B : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (f : A →ₜ* B) (hf : Function.Bijective f)
    (dA : A →ₜ* Multiplicative ℤ) (dB : B →ₜ* Multiplicative ℤ)
    (hd : ∀ a, dB (f a) = dA a)
    (hcompact : IsCompact (dA.toMonoidHom.ker : Set A)) : A ≃ₜ* B := by
  let e : A ≃* B := MulEquiv.ofBijective f.toMonoidHom hf
  let S := dA.toMonoidHom.ker
  let T := dB.toMonoidHom.ker
  let r : S →* T :=
    { toFun a := ⟨f a.1, (hd a.1).trans a.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' a b := Subtype.ext (map_mul f a.1 b.1) }
  have hr : Function.Bijective r := by
    constructor
    · intro a b h
      apply Subtype.ext
      exact hf.1 (congrArg Subtype.val h)
    · intro b
      obtain ⟨a, ha⟩ := hf.2 b.1
      have ha' : dA a = 1 := (hd a).symm.trans (by rw [ha]; exact b.2)
      exact ⟨⟨a, ha'⟩, Subtype.ext ha⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  let er : S ≃ₜ* T :=
    { Continuous.homeoOfEquivCompactToT2
        (f := (MulEquiv.ofBijective r hr).toEquiv)
        ((f.continuous.comp continuous_subtype_val).subtype_mk _) with
      map_mul' := r.map_mul }
  have hTopen : IsOpen (T : Set B) := by
    change IsOpen (dB ⁻¹' ({1} : Set (Multiplicative ℤ)))
    exact (isOpen_discrete _).preimage dB.continuous
  have hrestricted : Continuous (fun b : T => e.symm b.1) := by
    apply (continuous_subtype_val.comp er.symm.continuous).congr
    intro b
    apply e.injective
    exact (congrArg Subtype.val (er.apply_symm_apply b)).trans (e.apply_symm_apply b.1).symm
  refine { toMulEquiv := e, continuous_toFun := f.continuous, continuous_invFun := ?_ }
  apply continuous_of_continuousAt_one e.symm.toMonoidHom (continuousAt_def.mpr ?_)
  intro V hV
  have hV' : V ∈ 𝓝 (e.symm ((1 : T) : B)) := hV
  have hAt : ContinuousAt (fun b : T => e.symm b.1) (1 : T) :=
    hrestricted.continuousAt
  obtain ⟨W, hWV, hWopen, hWone⟩ := mem_nhds_iff.mp (hAt hV')
  refine mem_nhds_iff.mpr
    ⟨Subtype.val '' W, ?_, hTopen.isOpenMap_subtype_val _ hWopen, ⟨1, hWone, rfl⟩⟩
  rintro _ ⟨b, hb, rfl⟩
  exact hWV hb

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Absolute abelian classes with a discrete integral arithmetic degree. -/
noncomputable def localAbsoluteAbelianWithIntegerDegree :
    Subgroup (TopologicalAbelianization Gal(SeparableClosure K / K) × Multiplicative ℤ) :=
  ((localAbsoluteAbelianResidueDegree K).toMonoidHom.comp (MonoidHom.fst _ _)).eqLocus
    (localWeilIntegerInclusion.comp (MonoidHom.snd _ _))

/-- Integral degree on the absolute abelian classes equipped with one. -/
noncomputable def integerDegreeOnAbsolute :
    localAbsoluteAbelianWithIntegerDegree K →ₜ* Multiplicative ℤ where
  toMonoidHom := (MonoidHom.snd _ _).comp (localAbsoluteAbelianWithIntegerDegree K).subtype
  continuous_toFun := continuous_snd.comp continuous_subtype_val

/-- Passing to the absolute quotient embeds the Weil degree into the profinite integers. -/
theorem localWeilAbelianization_degree_comparison
    (x : TopologicalAbelianization (localWeilGroup K)) :
    localAbsoluteAbelianResidueDegree K (localWeilAbelianizationToAbsolute K x) =
      localWeilIntegerInclusion (localWeilAbelianizationDegree K x) := by
  obtain ⟨w, rfl⟩ := TopologicalAbelianization.surjective_mk (localWeilGroup K) x
  exact localResidueDegree_localWeilToAbsolute K w

/-- The absolute class and its integral degree as a single continuous homomorphism. -/
noncomputable def localWeilAbelianizationToIntegerDegree :
    TopologicalAbelianization (localWeilGroup K) →ₜ* localAbsoluteAbelianWithIntegerDegree K where
  toMonoidHom :=
    { toFun x := ⟨(localWeilAbelianizationToAbsolute K x, localWeilAbelianizationDegree K x),
        localWeilAbelianization_degree_comparison K x⟩
      map_one' := Subtype.ext (Prod.ext (map_one _) (map_one _))
      map_mul' x y := Subtype.ext (Prod.ext (map_mul _ x y) (map_mul _ x y)) }
  continuous_toFun :=
    ((localWeilAbelianizationToAbsolute K).continuous.prodMk
      (localWeilAbelianizationDegree K).continuous).subtype_mk _

/-- An absolute abelian class with integral degree has a unique Weil abelian class. -/
theorem localWeilAbelianizationToIntegerDegree_bijective :
    Function.Bijective (localWeilAbelianizationToIntegerDegree K) := by
  constructor
  · intro x y h
    exact localWeilAbelianizationToAbsolute_injective K
      (congrArg (fun a : localAbsoluteAbelianWithIntegerDegree K => a.1.1) h)
  · intro a
    have ha : a.1.1 ∈ (localWeilAbelianizationToAbsolute K).toMonoidHom.range :=
      (mem_range_localWeilAbelianizationToAbsolute_iff K a.1.1).mpr ⟨a.1.2, a.2.symm⟩
    obtain ⟨x, hx⟩ := ha
    refine ⟨x, Subtype.ext (Prod.ext hx ?_)⟩
    apply localWeilIntegerInclusion_injective
    exact (localWeilAbelianization_degree_comparison K x).symm.trans
      ((congrArg (localAbsoluteAbelianResidueDegree K) hx).trans a.2)

/-- The kernel of Weil abelian degree is the compact image of Weil inertia. -/
theorem localWeilAbelianizationDegree_isCompact_ker :
    IsCompact ((localWeilAbelianizationDegree K).toMonoidHom.ker :
      Set (TopologicalAbelianization (localWeilGroup K))) := by
  let q := TopologicalAbelianization.mkₜ (localWeilGroup K)
  have heq :
      q '' ((localWeilDegree K).toMonoidHom.ker : Set (localWeilGroup K)) =
        ((localWeilAbelianizationDegree K).toMonoidHom.ker :
          Set (TopologicalAbelianization (localWeilGroup K))) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hx
      obtain ⟨w, rfl⟩ := TopologicalAbelianization.surjective_mk (localWeilGroup K) x
      exact ⟨w, hx, rfl⟩
  rw [← heq]
  exact (localWeilInertia_isCompact K).image q.continuous

/-- The topology of the Weil abelianization is the pullback topology with
discrete integral degree. -/
noncomputable def localWeilAbelianizationEquivIntegerDegree :
    TopologicalAbelianization (localWeilGroup K) ≃ₜ* localAbsoluteAbelianWithIntegerDegree K :=
  continuousMulEquivOfCompactDegreeKernel
    (localWeilAbelianizationToIntegerDegree K)
    (localWeilAbelianizationToIntegerDegree_bijective K)
    (localWeilAbelianizationDegree K) (integerDegreeOnAbsolute K)
    (fun _ => rfl) (localWeilAbelianizationDegree_isCompact_ker K)

private noncomputable def localUnitAbsoluteArtin :
    𝒪[K]ˣ →ₜ* localAbsoluteAbelianProfinite K where
  toMonoidHom := (separableAbsoluteLocalArtinMap K).toMonoidHom.comp (integerUnitsToFieldUnits K)
  continuous_toFun := (separableAbsoluteLocalArtinMap K).continuous.comp
    (integerUnitsToFieldUnits_continuous K)

private theorem exists_of_dense_unit_uniformizer_image
    {A X U : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    [TopologicalSpace U] [CompactSpace U]
    (art : X → A) (hdense : DenseRange art) (u : U → A) (hu : Continuous u)
    (d : A →ₜ* ZHatMul) (p : A)
    (hdecomp : ∀ x, ∃ (z : U) (n : ℤ), art x = u z * p ^ n)
    (hp : d p = Multiplicative.ofAdd (1 : ZHat)) (hunit : ∀ z, d (u z) = 1)
    (a : A) (ha : d a = 1) : ∃ z, u z = a := by
  let S : ClosedSubgroup A := closedSubgroupGenerated (Set.range (fun _ : Unit => p))
  let gen : S.toSubgroup := closedSubgroupGeneratedMap (fun _ : Unit => p) ()
  let : CompactSpace S.toSubgroup := S.isClosed'.isClosedEmbedding_subtypeVal.compactSpace
  let m : U × S.toSubgroup → A := fun x => u x.1 * x.2.1
  have hclosed : IsClosed (Set.range m) :=
    (isCompact_range ((hu.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))).isClosed
  have hcontains (x : X) : art x ∈ Set.range m := by
    obtain ⟨z, n, hx⟩ := hdecomp x
    refine ⟨(z, gen ^ n), ?_⟩
    exact (congrArg (fun w : A => u z * w) (map_zpow S.toSubgroup.subtype gen n)).trans hx.symm
  obtain ⟨⟨z, w⟩, hw⟩ := DenseRange.induction_on hdense
    (p := fun b => b ∈ Set.range m) a hclosed hcontains
  have hgen : TopologicallyGenerates ({gen} : Set S.toSubgroup) := by
    have h := closedSubgroupGeneratedMap_topologicallyGenerates (fun _ : Unit => p)
    convert h using 1
    ext y
    constructor
    · intro hy
      exact ⟨(), (Set.mem_singleton_iff.mp hy).symm⟩
    · rintro ⟨⟨⟩, rfl⟩
      exact Set.mem_singleton _
  let ds : S.toSubgroup →ₜ* ZHatMul :=
    { toMonoidHom := d.toMonoidHom.comp S.toSubgroup.subtype
      continuous_toFun := d.continuous.comp continuous_subtype_val }
  have hinj := injective_of_topologicallyGenerates_zHat_one ds gen hgen
    (show ds gen = Multiplicative.ofAdd (1 : ZHat) from hp)
  change u z * w.1 = a at hw
  have hw₁ : w = 1 := by
    apply hinj
    rw [map_one]
    change d w.1 = 1
    rw [← hw, map_mul, hunit, one_mul] at ha
    exact ha
  refine ⟨z, ?_⟩
  rwa [hw₁, Subgroup.coe_one, mul_one] at hw

/-- Every absolute abelian class of profinite degree zero is the Artin
image of an actual valuation-ring unit. -/
theorem exists_unit_separableAbsoluteLocalArtinMap_of_degree_one
    (a : localAbsoluteAbelianProfinite K) (ha : localAbsoluteAbelianResidueDegree K a = 1) :
    ∃ x : 𝒪[K]ˣ, separableAbsoluteLocalArtinMap K (integerUnitsToFieldUnits K x) = a := by
  let A := localAbsoluteAbelianProfinite K
  let groupA : CommGroup A := localAbsoluteAbelianProfiniteCommGroup K
  let topologyA : TopologicalSpace A := inferInstance
  have topologicalA : @IsTopologicalGroup A topologyA groupA.toGroup := by
    change IsTopologicalGroup (TopologicalAbelianization Gal(SeparableClosure K/K))
    infer_instance
  let : CompactSpace 𝒪[K]ˣ := inferInstanceAs (CompactSpace (localUnits_profinite K))
  let art : Kˣ →ₜ* A := separableAbsoluteLocalArtinMap K
  let d : A →ₜ* ZHatMul := localAbsoluteAbelianResidueDegree K
  let pi := chosenLocalUniformizer K
  let u : 𝒪[K]ˣ →ₜ* A := localUnitAbsoluteArtin K
  have hdecomp (x : Kˣ) : ∃ (z : 𝒪[K]ˣ) (n : ℤ), art x = u z * art pi ^ n := by
    let z := uniformizerUnitFactor K pi (chosenLocalUniformizer_spec K) x
    let n := valuationMap K (Additive.ofMul x)
    refine ⟨z, n, ?_⟩
    calc
      art x = art ((integerUnitsToFieldUnits K z) * pi ^ n) :=
        congrArg art (uniformizerUnitFactor_mul_uniformizer_zpow K pi
          (chosenLocalUniformizer_spec K) x).symm
      _ = u z * art pi ^ n :=
        (map_mul art (integerUnitsToFieldUnits K z) (pi ^ n)).trans
          (congrArg (fun w : A => u z * w) (map_zpow art pi n))
  have hp : d (art pi) = Multiplicative.ofAdd (1 : ZHat) := by
    rw [show d (art pi) = localAbsoluteAbelianResidueDegree K (separableAbsoluteLocalArtinMap K pi)
          from rfl, localAbsoluteAbelianResidueDegree_separableAbsoluteLocalArtinMap K]
    change Multiplicative.ofAdd (valuationMap K (Additive.ofMul pi) : ZHat) = _
    rw [chosenLocalUniformizer_spec K, Int.cast_one]
  have hunit (z : 𝒪[K]ˣ) : d (u z) = 1 := by
    change localAbsoluteAbelianResidueDegree K (separableAbsoluteLocalArtinMap K
      (integerUnitsToFieldUnits K z)) = 1
    rw [localAbsoluteAbelianResidueDegree_separableAbsoluteLocalArtinMap K]
    change Multiplicative.ofAdd
      (valuationMap K (Additive.ofMul (integerUnitsToFieldUnits K z)) : ZHat) = 1
    rw [valuationMap_apply, v_integerUnitsToFieldUnits, Int.cast_zero]
    rfl
  exact @exists_of_dense_unit_uniformizer_image A Kˣ 𝒪[K]ˣ groupA topologyA
    topologicalA inferInstance inferInstance inferInstance inferInstance inferInstance
    art (separableAbsoluteLocalArtinMap_denseRange K) u u.continuous d (art pi)
    hdecomp hp hunit a ha

/-- The absolute Artin map together with the normalized integral valuation. -/
noncomputable def localArtinWithIntegerDegree :
    Kˣ →ₜ* localAbsoluteAbelianWithIntegerDegree K where
  toMonoidHom :=
    { toFun x := ⟨(separableAbsoluteLocalArtinMap K x, valuationUnitsMulHom K x),
        localAbsoluteAbelianResidueDegree_separableAbsoluteLocalArtinMap K x⟩
      map_one' := Subtype.ext (Prod.ext (map_one _) (map_one _))
      map_mul' x y := Subtype.ext (Prod.ext (map_mul _ x y) (map_mul _ x y)) }
  continuous_toFun := ((separableAbsoluteLocalArtinMap K).continuous.prodMk
    (valuationUnitsMulHom_continuous K)).subtype_mk _

/-- The absolute Artin map with its integral valuation is bijective. -/
theorem localArtinWithIntegerDegree_bijective :
    Function.Bijective (localArtinWithIntegerDegree K) := by
  constructor
  · intro a b h
    apply topologicalProfiniteCompletionMap_injective_localField K
    apply (separableProfiniteLocalReciprocity K).injective
    rw [separableProfiniteLocalReciprocity_apply, separableProfiniteLocalReciprocity_apply,
      separableProfiniteLocalReciprocityHom_map, separableProfiniteLocalReciprocityHom_map]
    exact congrArg (fun x : localAbsoluteAbelianWithIntegerDegree K => x.1.1) h
  · intro a
    let art := separableAbsoluteLocalArtinMap K
    let d : localAbsoluteAbelianProfinite K →ₜ* ZHatMul := localAbsoluteAbelianResidueDegree K
    let pi := chosenLocalUniformizer K
    let y := pi ^ a.1.2.toAdd
    let a₀ : localAbsoluteAbelianProfinite K := a.1.1
    have hy : valuationUnitsMulHom K y = a.1.2 := by
      apply Multiplicative.ext
      change valuationMap K (Additive.ofMul (pi ^ a.1.2.toAdd)) = a.1.2.toAdd
      rw [valuationMap_ofMul_zpow, chosenLocalUniformizer_spec K, mul_one]
    have hdy : d (art y) = d a₀ :=
      (localAbsoluteAbelianResidueDegree_separableAbsoluteLocalArtinMap K y).trans
        ((congrArg localWeilIntegerInclusion hy).trans a.2.symm)
    have hzero : d (a₀ / art y) = 1 :=
      (map_div d a₀ (art y)).trans
        ((congrArg (fun b => d a₀ / b) hdy).trans (div_self' _))
    obtain ⟨u, hu⟩ := exists_unit_separableAbsoluteLocalArtinMap_of_degree_one K _ hzero
    let x := integerUnitsToFieldUnits K u * y
    have hx : art x = a₀ :=
      (map_mul art (integerUnitsToFieldUnits K u) y).trans
        ((congrArg (fun b : localAbsoluteAbelianProfinite K => b * art y) hu).trans
          (div_mul_cancel _ _))
    have hd : valuationUnitsMulHom K x = a.1.2 := by
      apply localWeilIntegerInclusion_injective
      exact (localAbsoluteAbelianResidueDegree_separableAbsoluteLocalArtinMap K x).symm.trans
        ((congrArg d hx).trans a.2)
    exact ⟨x, Subtype.ext (Prod.ext hx hd)⟩

/-- The kernel of the normalized valuation is compact, being the image of integer units. -/
theorem localValuation_isCompact_ker :
    IsCompact ((valuationUnitsMulHom K).ker : Set Kˣ) := by
  let : CompactSpace 𝒪[K]ˣ := inferInstanceAs (CompactSpace (localUnits_profinite K))
  have h := isCompact_range (integerUnitsToFieldUnits_continuous K)
  have heq : Set.range (integerUnitsToFieldUnits K) = ((valuationUnitsMulHom K).ker : Set Kˣ) := by
    ext x
    change x ∈ (integerUnitsToFieldUnits K).range ↔ (valuationUnitsMulHom K) x = 1
    exact (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero K x)
  rwa [heq] at h

/-- Local reciprocity as an isomorphism for the ordinary topology on the
multiplicative group and the Weil topology on its Galois-side quotient. -/
noncomputable def localWeilReciprocity :
    Kˣ ≃ₜ* TopologicalAbelianization (localWeilGroup K) :=
  (continuousMulEquivOfCompactDegreeKernel
    (localArtinWithIntegerDegree K) (localArtinWithIntegerDegree_bijective K)
    (valuationUnitsContinuousMonoidHom K) (integerDegreeOnAbsolute K)
    (fun _ => rfl) (localValuation_isCompact_ker K)).trans
    (localWeilAbelianizationEquivIntegerDegree K).symm

/-- Forgetting the discrete integer degree recovers the original absolute
Artin map, on every field unit. -/
theorem localWeilAbelianizationToAbsolute_localWeilReciprocity (x : Kˣ) :
    localWeilAbelianizationToAbsolute K (localWeilReciprocity K x) =
      separableAbsoluteLocalArtinMap K x := by
  have h := (localWeilAbelianizationEquivIntegerDegree K).apply_symm_apply
    (localArtinWithIntegerDegree K x)
  exact congrArg (fun a : localAbsoluteAbelianWithIntegerDegree K => a.1.1) h

/-- The degree of the Artin element is the existing normalized geometric
valuation, which is minus one on a DVR uniformizer. -/
theorem localWeilAbelianizationDegree_localWeilReciprocity (x : Kˣ) :
    localWeilAbelianizationDegree K (localWeilReciprocity K x) =
      valuationUnitsMulHom K x := by
  have h := (localWeilAbelianizationEquivIntegerDegree K).apply_symm_apply
    (localArtinWithIntegerDegree K x)
  exact congrArg (fun a : localAbsoluteAbelianWithIntegerDegree K => a.1.2) h


/-- A valuation-ring uniformizer has degree minus one under the geometric
normalization of the existing local Artin map. -/
theorem localWeilAbelianizationDegree_localWeilReciprocity_uniformizer :
    (localWeilAbelianizationDegree K
      (localWeilReciprocity K (integerRingUniformizerFieldUnit K))).toAdd = -1 := by
  rw [localWeilAbelianizationDegree_localWeilReciprocity]
  change valuationMap K (Additive.ofMul (integerRingUniformizerFieldUnit K)) = -1
  rw [valuationMap_apply]
  exact v_integerRingUniformizerFieldUnit K

end LocalClassFieldTheory
