/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FullIdeleInflation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FullIdelePrescribedInvariant
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.OnePlaceInvariantRestriction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.StandardIdeleClassInflation

/-! # Existence of the arithmetic-normalized global fundamental class -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Martinet.Shafarevich
open IsDedekindDomain NumberField
open scoped DirectSum NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

section IsomorphicField

variable (K : Type) [Field K] [NumberField K] {L M : Type}
  [Field L] [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M]

/-- Transport of the actual standard idèle class group and its Galois action
along an isomorphic top field. -/
def standardIdeleClassH2CongrIso (e : L ≃ₐ[K] M) :
    groupCohomology (standardIdeleClassRep K L) 2 ≅
      groupCohomology (standardIdeleClassRep K M) 2 := by
  let g := AlgEquiv.autCongr e
  let c := NumberField.IdeleClassGroup.congr (e.restrictScalars ℚ)
  refine groupCohomology.mapIso g c.toAdditive.toIntLinearEquiv ?_ 2
  intro σ
  apply LinearMap.ext
  intro a
  let a₀ : Additive (NumberField.IdeleClassGroup (𝓞 L) L) := a
  let a₁ := Additive.toMul a₀
  apply Additive.toMul.injective
  let s := σ.restrictScalars ℚ
  let t := (g σ).restrictScalars ℚ
  let f := e.restrictScalars ℚ
  change NumberField.IdeleClassGroup.congr f (NumberField.IdeleClassGroup.congr s a₁) =
    NumberField.IdeleClassGroup.congr t (NumberField.IdeleClassGroup.congr f a₁)
  have h : s.trans f = f.trans t := by
    apply AlgEquiv.ext
    intro x
    change e (σ x) = e (σ (e.symm (e x)))
    rw [e.symm_apply_apply]
  calc
    _ = NumberField.IdeleClassGroup.congr (s.trans f) a₁ :=
      NumberField.IdeleClassGroup.congr_trans s f a₁
    _ = NumberField.IdeleClassGroup.congr (f.trans t) a₁ :=
      congrArg (fun j : L ≃ₐ[ℚ] M => NumberField.IdeleClassGroup.congr j a₁) h
    _ = _ := (NumberField.IdeleClassGroup.congr_trans f t a₁).symm

/-- The same transport as an additive equivalence on the original cohomology. -/
def standardIdeleClassH2Congr (e : L ≃ₐ[K] M) :
    groupCohomology (standardIdeleClassRep K L) 2 ≃+
      groupCohomology (standardIdeleClassRep K M) 2 :=
  (standardIdeleClassH2CongrIso K e).toLinearEquiv.toAddEquiv

end IsomorphicField

section EmbeddedField

variable (K : Type) [Field K] [NumberField K] {L E : Type}
  [Field L] [NumberField L] [Field E] [NumberField E] [Algebra K L] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [Normal K L]
  (i : L →ₐ[K] E) [NumberField i.fieldRange]

/-- Inflation through an explicit embedding is the canonical transport to
its actual image followed by quotient inflation. -/
theorem standardIdeleClassH2InflateOfEmbedding_eq_via_fieldRange
    (x : groupCohomology (standardIdeleClassRep K L) 2) :
    let _ : Normal K i.fieldRange := Normal.of_algEquiv i.equivFieldRange
    standardIdeleClassH2InflateOfEmbedding i x =
      standardIdeleClassH2Inflate K E i.fieldRange
        (standardIdeleClassH2Congr K i.equivFieldRange x) := by
  intro normalOwner
  rw [standardIdeleClassH2Inflate_eq_inflateOfEmbedding]
  let j := i.fieldRange.val
  let e := i.equivFieldRange
  let g := AlgEquiv.autCongr e
  have hg (σ : Gal(E/K)) :
      embeddedGaloisRestriction (B := K) i σ =
        g.symm (embeddedGaloisRestriction (B := K) j σ) := by
    apply AlgEquiv.ext
    intro d
    apply i.injective
    let a := embeddedGaloisRestriction (B := K) j σ (e d)
    change i (embeddedGaloisRestriction (B := K) i σ d) = j (e (e.symm a))
    calc
      _ = σ (i d) := embeddedGaloisRestriction_commutes (B := K) i σ d
      _ = j a := (embeddedGaloisRestriction_commutes (B := K) j σ (e d)).symm
      _ = _ := congrArg j (e.apply_symm_apply a).symm
  change standardIdeleClassH2InflateOfEmbedding i x =
    standardIdeleClassH2InflateOfEmbedding j ((standardIdeleClassH2CongrIso K e).hom x)
  suffices hm : standardIdeleClassH2InflateOfEmbedding i =
      (standardIdeleClassH2CongrIso K e).hom ≫
        standardIdeleClassH2InflateOfEmbedding j from ConcreteCategory.congr_hom hm x
  rw [standardIdeleClassH2InflateOfEmbedding, standardIdeleClassH2InflateOfEmbedding,
    standardIdeleClassH2CongrIso, groupCohomology.mapIso_hom, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr (MonoidHom.ext hg)
  apply LinearMap.ext
  intro a
  apply Additive.toMul.injective
  let _ : Algebra L E := i.toRingHom.toAlgebra
  let _ : Algebra i.fieldRange E := j.toRingHom.toAlgebra
  have h := NumberField.IdeleClassGroup.congr_fieldInclusion
    (e.restrictScalars ℚ) (AlgEquiv.refl : E ≃ₐ[ℚ] E) (fun _ => rfl) a.toMul
  rw [NumberField.IdeleClassGroup.congr_refl] at h
  exact h

end EmbeddedField

section InflationInjectivity

variable (K : Type) [Field K] [NumberField K] {L M : Type}
  [Field L] [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M] [Normal K L]

/-- Inflation along the actual embedding of the lower normal extension is injective. -/
theorem standardIdeleClassH2InflateOfEmbedding_injective (i : L →ₐ[K] M) :
    Function.Injective (standardIdeleClassH2InflateOfEmbedding i) := by
  let : NumberField i.fieldRange := NumberField.of_module_finite K i.fieldRange
  let : Normal K i.fieldRange := Normal.of_algEquiv i.equivFieldRange
  intro a b hab
  rw [standardIdeleClassH2InflateOfEmbedding_eq_via_fieldRange,
    standardIdeleClassH2InflateOfEmbedding_eq_via_fieldRange] at hab
  exact (standardIdeleClassH2Congr K i.equivFieldRange).injective
    (standardIdeleClassH2Inflate_injective K M i.fieldRange hab)

end InflationInjectivity

variable (K : Type) [Field K] [NumberField K]
  (L : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField L]

local notation "H₂" F => groupCohomology (standardIdeleClassRep K F) 2

/-- The arithmetic normalization is witnessed by a full idèle lift on an
actual finite Galois refinement whose invariant sum is the reciprocal degree. -/
def IsNormalizedGlobalFundamentalClass (u : H₂ L) : Prop :=
  ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (hLE : L ≤ E),
    let _ : NumberField E := NumberField.of_module_finite K E
    let i : L →ₐ[K] E :=
      IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L E).mp hLE)
    ∃ x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2,
      standardIdeleClassH2InflateOfEmbedding i u = fullIdeleClassH2Map K E x ∧
      fullIdeleBrauerInvariantSum K E x =
        ((1 / (Module.finrank K L : ℚ) : ℚ) : AddCircle (1 : ℚ))

open scoped Classical in
/-- A finite-place witness retains its original idèle cocycle and local Brauer class. -/
def HasOnePlaceGlobalFundamentalWitness (v : HeightOneSpectrum (𝓞 K)) (u : H₂ L) : Prop :=
  ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (hLE : L ≤ E),
    let _ : NumberField E := NumberField.of_module_finite K E
    let i : L →ₐ[K] E :=
      IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L E).mp hLE)
    ∃ (x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2) (b : Br (v.adicCompletion K)),
      standardIdeleClassH2InflateOfEmbedding i u = fullIdeleClassH2Map K E x ∧
      fullIdeleBrauerTuple K E x =
        DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b ∧
      finitePlaceBrauerInvariantEquiv K v b =
        ((1 / (Module.finrank K L : ℚ) : ℚ) : AddCircle (1 : ℚ))

/-- The arithmetic global class exists on the original standard idèle
class carrier and has exact order `[L:K]`, with a literal finite-place witness. -/
theorem exists_onePlaceNormalizedGlobalFundamentalClass (v : HeightOneSpectrum (𝓞 K)) :
    ∃ u : H₂ L, IsNormalizedGlobalFundamentalClass K L u ∧
      addOrderOf u = Module.finrank K L ∧ HasOnePlaceGlobalFundamentalWitness K L v u := by
  let n : ℕ+ := ⟨Module.finrank K L, Module.finrank_pos⟩
  let q : AddCircle (1 : ℚ) := ((1 / (n : ℕ) : ℚ) : AddCircle (1 : ℚ))
  have hqo : addOrderOf q = (n : ℕ) :=
    AddCircle.addOrderOf_period_div (p := (1 : ℚ)) n.pos
  have hq : (n : ℕ) • q = 0 := by rw [← hqo, addOrderOf_nsmul_eq_zero]
  obtain ⟨E, hLE, x, b, hx, hb⟩ := exists_refinement_fullIdele_onePlace K L v n q hq
  let : NumberField E := NumberField.of_module_finite K E
  let i : L →ₐ[K] E :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L E).mp hLE)
  let M := i.fieldRange
  let : NumberField M := NumberField.of_module_finite K M
  let : Normal K M := Normal.of_algEquiv i.equivFieldRange
  let : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  let : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  have hd : Module.finrank K M = (n : ℕ) := i.equivFieldRange.toLinearEquiv.finrank_eq.symm
  let y := fullIdeleH2BaseRestriction (M := M) x
  have hy : fullIdeleBrauerInvariantSum M E y = 0 := by
    rw [fullIdeleBrauerInvariantSum_baseRestriction_single v b x hx, hd, hb, hq]
  have hy0 : fullIdeleClassH2Map M E y = 0 :=
    fullIdeleClassH2Map_eq_zero_of_invariantSum M E y hy
  have hker : fullIdeleClassH2Map K E x ∈ (standardIdeleClassH2Restrict K E M).hom.ker := by
    change standardIdeleClassH2Restrict K E M (fullIdeleClassH2Map K E x) = 0
    rw [fullIdeleClassH2Map_baseRestriction]
    exact hy0
  obtain ⟨z, hz⟩ := standardIdeleClassH2Restrict_ker_le_inflate_range K E M hker
  let c := standardIdeleClassH2Congr K i.equivFieldRange
  let u := c.symm z
  let f := (standardIdeleClassH2Inflate K E M).hom.toAddMonoidHom.comp c.toAddMonoidHom
  have hf : Function.Injective f :=
    (standardIdeleClassH2Inflate_injective K E M).comp c.injective
  have hu : f u = fullIdeleClassH2Map K E x := by
    change standardIdeleClassH2Inflate K E M (c (c.symm z)) = _
    rw [c.apply_symm_apply]
    exact hz
  have hxq : fullIdeleBrauerInvariantSum K E x = q := by
    change sumLocalInv K (fullIdeleBrauerTuple K E x) = q
    rw [hx, sumLocalInv_single]
    exact hb
  have hInfl : standardIdeleClassH2InflateOfEmbedding i u = fullIdeleClassH2Map K E x :=
    (standardIdeleClassH2InflateOfEmbedding_eq_via_fieldRange K i u).trans hu
  refine ⟨u, ⟨E, hLE, x, hInfl, hxq⟩, ?_, ⟨E, hLE, x, b, hInfl, hx, hb⟩⟩
  change addOrderOf u = (n : ℕ)
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    apply hf
    rw [map_nsmul, map_zero, hu, ← map_nsmul]
    apply fullIdeleClassH2Map_eq_zero_of_invariantSum
    rw [map_nsmul, hxq, hq]
  · rw [← hqo, addOrderOf_dvd_iff_nsmul_eq_zero]
    have hw : fullIdeleClassH2Map K E (addOrderOf u • x) = 0 := by
      rw [map_nsmul, ← hu, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
    have hs := fullIdeleBrauerInvariantSum_eq_zero_of_class_eq_zero K E _ hw
    rwa [map_nsmul, hxq] at hs

/-- The arithmetic global class exists on the standard idèle class carrier. -/
theorem exists_normalizedGlobalFundamentalClass (v : HeightOneSpectrum (𝓞 K)) :
    ∃ u : H₂ L, IsNormalizedGlobalFundamentalClass K L u ∧
      addOrderOf u = Module.finrank K L := by
  obtain ⟨u, hu, horder, _⟩ := exists_onePlaceNormalizedGlobalFundamentalClass K L v
  exact ⟨u, hu, horder⟩

/-- The original standard idèle-class group has an arithmetic-normalized
fundamental class for the specified finite-place realization. -/
def normalizedGlobalFundamentalClass (v : HeightOneSpectrum (𝓞 K)) : H₂ L :=
  (exists_normalizedGlobalFundamentalClass K L v).choose

theorem normalizedGlobalFundamentalClass_spec (v : HeightOneSpectrum (𝓞 K)) :
    IsNormalizedGlobalFundamentalClass K L (normalizedGlobalFundamentalClass K L v) :=
  (exists_normalizedGlobalFundamentalClass K L v).choose_spec.1

theorem addOrderOf_normalizedGlobalFundamentalClass (v : HeightOneSpectrum (𝓞 K)) :
    addOrderOf (normalizedGlobalFundamentalClass K L v) = Module.finrank K L :=
  (exists_normalizedGlobalFundamentalClass K L v).choose_spec.2

/-- Two arithmetic-normalized classes agree, by comparing their actual
idèle lifts after inflating to the compositum of the two refinements. -/
theorem IsNormalizedGlobalFundamentalClass.eq {u v : H₂ L}
    (hu : IsNormalizedGlobalFundamentalClass K L u)
    (hv : IsNormalizedGlobalFundamentalClass K L v) : u = v := by
  obtain ⟨E, hLE, x, hx, hxq⟩ := hu
  obtain ⟨F, hLF, y, hy, hyq⟩ := hv
  let T := E ⊔ F
  let : NumberField E := NumberField.of_module_finite K E
  let : NumberField F := NumberField.of_module_finite K F
  let : NumberField T := NumberField.of_module_finite K T
  let i₁ : L →ₐ[K] E :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L E).mp hLE)
  let i₂ : L →ₐ[K] F :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L F).mp hLF)
  let j₁ : E →ₐ[K] T :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff E T).mp le_sup_left)
  let j₂ : F →ₐ[K] T :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff F T).mp le_sup_right)
  let hLT : L ≤ T := hLE.trans le_sup_left
  let i : L →ₐ[K] T :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L T).mp hLT)
  have hi₁ : j₁.comp i₁ = i := AlgHom.ext (fun _ => rfl)
  have hi₂ : j₂.comp i₂ = i := AlgHom.ext (fun _ => rfl)
  let a := fullIdeleH2InflateOfEmbedding j₁ x
  let b := fullIdeleH2InflateOfEmbedding j₂ y
  have h₁ : standardIdeleClassH2InflateOfEmbedding i u = fullIdeleClassH2Map K T a := by
    rw [← hi₁, standardIdeleClassH2InflateOfEmbedding_comp]
    change standardIdeleClassH2InflateOfEmbedding j₁
      (standardIdeleClassH2InflateOfEmbedding i₁ u) = _
    rw [hx, fullIdeleClassH2Map_inflateOfEmbedding]
  have h₂ : standardIdeleClassH2InflateOfEmbedding i v = fullIdeleClassH2Map K T b := by
    rw [← hi₂, standardIdeleClassH2InflateOfEmbedding_comp]
    change standardIdeleClassH2InflateOfEmbedding j₂
      (standardIdeleClassH2InflateOfEmbedding i₂ v) = _
    rw [hy, fullIdeleClassH2Map_inflateOfEmbedding]
  have hab : fullIdeleClassH2Map K T a = fullIdeleClassH2Map K T b := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply fullIdeleClassH2Map_eq_zero_of_invariantSum
    rw [map_sub]
    change sumLocalInv K (fullIdeleBrauerTuple K T a) -
      sumLocalInv K (fullIdeleBrauerTuple K T b) = 0
    rw [fullIdeleBrauerTuple_inflateOfEmbedding, fullIdeleBrauerTuple_inflateOfEmbedding]
    change fullIdeleBrauerInvariantSum K E x - fullIdeleBrauerInvariantSum K F y = 0
    rw [hxq, hyq, sub_self]
  let : NumberField i.fieldRange := NumberField.of_module_finite K i.fieldRange
  let : Normal K i.fieldRange := Normal.of_algEquiv i.equivFieldRange
  have h := h₁.trans (hab.trans h₂.symm)
  rw [standardIdeleClassH2InflateOfEmbedding_eq_via_fieldRange,
    standardIdeleClassH2InflateOfEmbedding_eq_via_fieldRange] at h
  exact (standardIdeleClassH2Congr K i.equivFieldRange).injective
    (standardIdeleClassH2Inflate_injective K T i.fieldRange h)

/-- The original class has a unique arithmetic normalization, independent of
the auxiliary place and finite refinement. -/
theorem existsUnique_normalizedGlobalFundamentalClass :
    ∃! u : H₂ L, IsNormalizedGlobalFundamentalClass K L u := by
  obtain ⟨v⟩ := finitePlace_nonempty K
  obtain ⟨u, hu, _⟩ := exists_normalizedGlobalFundamentalClass K L v
  exact ⟨u, hu, fun w hw => IsNormalizedGlobalFundamentalClass.eq K L hw hu⟩

/-- The canonical global fundamental class on the original standard idèle classes. -/
def canonicalGlobalFundamentalClass : H₂ L :=
  (existsUnique_normalizedGlobalFundamentalClass K L).exists.choose

theorem canonicalGlobalFundamentalClass_spec :
    IsNormalizedGlobalFundamentalClass K L (canonicalGlobalFundamentalClass K L) :=
  (existsUnique_normalizedGlobalFundamentalClass K L).exists.choose_spec

/-- The canonical class can be realized at any chosen finite place on a refinement. -/
theorem canonicalGlobalFundamentalClass_onePlaceWitness (v : HeightOneSpectrum (𝓞 K)) :
    HasOnePlaceGlobalFundamentalWitness K L v (canonicalGlobalFundamentalClass K L) := by
  obtain ⟨u, hu, _, hw⟩ := exists_onePlaceNormalizedGlobalFundamentalClass K L v
  have h := IsNormalizedGlobalFundamentalClass.eq K L hu (canonicalGlobalFundamentalClass_spec K L)
  exact h ▸ hw

theorem addOrderOf_canonicalGlobalFundamentalClass :
    addOrderOf (canonicalGlobalFundamentalClass K L) = Module.finrank K L := by
  obtain ⟨v⟩ := finitePlace_nonempty K
  have h := IsNormalizedGlobalFundamentalClass.eq K L (canonicalGlobalFundamentalClass_spec K L)
    (normalizedGlobalFundamentalClass_spec K L v)
  rw [h, addOrderOf_normalizedGlobalFundamentalClass]

end GlobalClassFieldTheory.Cohomology
