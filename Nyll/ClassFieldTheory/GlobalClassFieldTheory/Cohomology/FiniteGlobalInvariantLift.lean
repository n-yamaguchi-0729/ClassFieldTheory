/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.StandardIdeleClassIsomorphicInflation

/-! # Arithmetic lifts for any realization of a finite normal top field -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Martinet.Shafarevich
open IsDedekindDomain NumberField
open scoped DirectSum NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "H₂" => groupCohomology (standardIdeleClassRep K L) 2

/-- A finite standard class has a specified invariant if a genuine
higher idèle class represents its inflation and has that invariant sum. -/
def HasFiniteGlobalInvariant (x : H₂) (q : AddCircle (1 : ℚ)) : Prop :=
  ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
    let _ : NumberField E := NumberField.of_module_finite K E
    ∃ (i : L →ₐ[K] E) (z : groupCohomology (finiteIdeleShortComplex K E).X₂ 2),
      standardIdeleClassH2InflateOfEmbedding i x = fullIdeleClassH2Map K E z ∧
      fullIdeleBrauerInvariantSum K E z = q

/-- Comparing the full idèle lifts in one common refinement compares both
the original cohomology classes and their invariant sums. -/
private theorem finiteGlobalInvariant_compare {x y : H₂} {q r : AddCircle (1 : ℚ)}
    (hx : HasFiniteGlobalInvariant K L x q) (hy : HasFiniteGlobalInvariant K L y r) :
    x = y ↔ q = r := by
  obtain ⟨E, iE, a, ha, haq⟩ := hx
  obtain ⟨F, iF, b, hb, hbq⟩ := hy
  let T := E ⊔ F
  let : NumberField E := NumberField.of_module_finite K E
  let : NumberField F := NumberField.of_module_finite K F
  let : NumberField T := NumberField.of_module_finite K T
  let jE : E →ₐ[K] T :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff E T).mp le_sup_left)
  let jF : F →ₐ[K] T :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff F T).mp le_sup_right)
  let i := jE.comp iE
  let j := jF.comp iF
  have hmaps : standardIdeleClassH2InflateOfEmbedding i =
      standardIdeleClassH2InflateOfEmbedding j :=
    standardIdeleClassH2InflateOfEmbedding_eq_of_embeddings K L i j
  let a' := fullIdeleH2InflateOfEmbedding jE a
  let b' := fullIdeleH2InflateOfEmbedding jF b
  have ha' : standardIdeleClassH2InflateOfEmbedding i x = fullIdeleClassH2Map K T a' := by
    change standardIdeleClassH2InflateOfEmbedding (jE.comp iE) x = _
    rw [standardIdeleClassH2InflateOfEmbedding_comp]
    change standardIdeleClassH2InflateOfEmbedding jE
      (standardIdeleClassH2InflateOfEmbedding iE x) = _
    rw [ha, fullIdeleClassH2Map_inflateOfEmbedding]
  have hb' : standardIdeleClassH2InflateOfEmbedding i y = fullIdeleClassH2Map K T b' := by
    rw [hmaps]
    change standardIdeleClassH2InflateOfEmbedding (jF.comp iF) y = _
    rw [standardIdeleClassH2InflateOfEmbedding_comp]
    change standardIdeleClassH2InflateOfEmbedding jF
      (standardIdeleClassH2InflateOfEmbedding iF y) = _
    rw [hb, fullIdeleClassH2Map_inflateOfEmbedding]
  have hs : fullIdeleBrauerInvariantSum K T (a' - b') = q - r := by
    rw [map_sub]
    change sumLocalInv K (fullIdeleBrauerTuple K T a') -
      sumLocalInv K (fullIdeleBrauerTuple K T b') = q - r
    rw [fullIdeleBrauerTuple_inflateOfEmbedding, fullIdeleBrauerTuple_inflateOfEmbedding]
    change fullIdeleBrauerInvariantSum K E a - fullIdeleBrauerInvariantSum K F b = q - r
    rw [haq, hbq]
  constructor
  · intro hxy
    have hab : fullIdeleClassH2Map K T (a' - b') = 0 := by
      rw [map_sub, ← ha', ← hb', hxy, sub_self]
    exact sub_eq_zero.mp
      (hs.symm.trans (fullIdeleBrauerInvariantSum_eq_zero_of_class_eq_zero K T _ hab))
  · intro hqr
    have hab : fullIdeleClassH2Map K T (a' - b') = 0 := by
      apply fullIdeleClassH2Map_eq_zero_of_invariantSum K T
      rw [hs, hqr, sub_self]
    rw [map_sub] at hab
    exact standardIdeleClassH2InflateOfEmbedding_injective K i
      (ha'.trans ((sub_eq_zero.mp hab).trans hb'.symm))

/-- A specified invariant determines the original class, independently of
the chosen finite Galois refinement and embedding. -/
theorem HasFiniteGlobalInvariant.eq {x y : H₂} {q : AddCircle (1 : ℚ)}
    (hx : HasFiniteGlobalInvariant K L x q) (hy : HasFiniteGlobalInvariant K L y q) : x = y :=
  (finiteGlobalInvariant_compare K L hx hy).mpr rfl

/-- All higher full idèle lifts of the same original class have the same
invariant sum, including lifts through different embeddings. -/
theorem HasFiniteGlobalInvariant.invariant_eq {x : H₂} {q r : AddCircle (1 : ℚ)}
    (hq : HasFiniteGlobalInvariant K L x q) (hr : HasFiniteGlobalInvariant K L x r) : q = r :=
  (finiteGlobalInvariant_compare K L hq hr).mp rfl

omit [FiniteDimensional K L] in
/-- Transport through an isomorphism of the actual top fields preserves
the arithmetic invariant, using the same full idèle representative. -/
theorem HasFiniteGlobalInvariant.congr {M : Type} [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M] (e : L ≃ₐ[K] M)
    {x : H₂} {q : AddCircle (1 : ℚ)} (hx : HasFiniteGlobalInvariant K L x q) :
    HasFiniteGlobalInvariant K M (standardIdeleClassH2Congr K e x) q := by
  obtain ⟨E, i, z, hz, hzq⟩ := hx
  let : NumberField E := NumberField.of_module_finite K E
  let j := i.comp e.symm.toAlgHom
  refine ⟨E, j, z, ?_, hzq⟩
  have hi : j.comp e.toAlgHom = i :=
    AlgHom.ext fun a => congrArg i (e.symm_apply_apply a)
  have h := ConcreteCategory.congr_hom
    (standardIdeleClassH2InflateOfEmbedding_comp e.toAlgHom j) x
  rw [hi, standardIdeleClassH2InflateOfEmbedding_eq_congrIso] at h
  exact h.symm.trans hz

/-- Realize the actual top field in the chosen separable closure of the base. -/
def finiteGlobalInvariantStage : FiniteGaloisIntermediateField K (SeparableClosure K) :=
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  i.finiteGaloisFieldRange

/-- The top-field equivalence for this actual realization, over the same base. -/
def finiteGlobalInvariantStageEquiv : L ≃ₐ[K] finiteGlobalInvariantStage K L :=
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  i.equivFieldRange

/-- The prescribed reciprocal class in ordinary standard cohomology for an
arbitrary finite top field over a fixed small base. -/
def finiteGlobalFundamentalClass : H₂ :=
  let E := finiteGlobalInvariantStage K L
  let _ : NumberField E := NumberField.of_module_finite K E
  (standardIdeleClassH2Congr K (finiteGlobalInvariantStageEquiv K L)).symm
    (canonicalGlobalFundamentalClass K E)

open scoped Classical in
/-- Over an arbitrary original top field, an actual idèle lift of the
fundamental class can be supported at any prescribed finite place. -/
theorem finiteGlobalFundamentalClass_onePlaceWitness (v : HeightOneSpectrum (𝓞 K)) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      let _ : NumberField E := NumberField.of_module_finite K E
      ∃ (j : L →ₐ[K] E) (x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2)
        (b : Br (v.adicCompletion K)),
        standardIdeleClassH2InflateOfEmbedding j (finiteGlobalFundamentalClass K L) =
            fullIdeleClassH2Map K E x ∧
          fullIdeleBrauerTuple K E x =
            DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b ∧
          finitePlaceBrauerInvariantEquiv K v b =
            ((1 / (Module.finrank K L : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  let E := finiteGlobalInvariantStage K L
  let : NumberField E := NumberField.of_module_finite K E
  let e := finiteGlobalInvariantStageEquiv K L
  obtain ⟨F, hEF, x, b, hx, htuple, hb⟩ :=
    canonicalGlobalFundamentalClass_onePlaceWitness K E v
  let : NumberField F := NumberField.of_module_finite K F
  let i : E →ₐ[K] F :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff E F).mp hEF)
  refine ⟨F, i.comp e.toAlgHom, x, b, ?_, htuple, ?_⟩
  · rw [standardIdeleClassH2InflateOfEmbedding_comp,
      standardIdeleClassH2InflateOfEmbedding_eq_congrIso]
    change standardIdeleClassH2InflateOfEmbedding i
      (standardIdeleClassH2Congr K e ((standardIdeleClassH2Congr K e).symm _)) = _
    rw [AddEquiv.apply_symm_apply]
    exact hx
  · rw [e.toLinearEquiv.finrank_eq]
    exact hb

/-- The chosen realization gives the same arithmetic class on the original top field. -/
theorem finiteGlobalFundamentalClass_spec :
    HasFiniteGlobalInvariant K L (finiteGlobalFundamentalClass K L)
      ((1 / (Module.finrank K L : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  obtain ⟨v⟩ := finitePlace_nonempty K
  obtain ⟨E, j, x, b, hx, htuple, hb⟩ := finiteGlobalFundamentalClass_onePlaceWitness K L v
  let : NumberField E := NumberField.of_module_finite K E
  refine ⟨E, j, x, hx, ?_⟩
  have h := congrArg (sumLocalInv K) htuple
  exact h.trans ((sumLocalInv_single K (Sum.inl v) b).trans hb)

/-- The arithmetic-normalized class is natural in the actual top field
with the base fixed. -/
theorem finiteGlobalFundamentalClass_congr {M : Type} [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M] (e : L ≃ₐ[K] M) :
    standardIdeleClassH2Congr K e (finiteGlobalFundamentalClass K L) =
      finiteGlobalFundamentalClass K M := by
  apply HasFiniteGlobalInvariant.eq K M
  · exact HasFiniteGlobalInvariant.congr K L e (finiteGlobalFundamentalClass_spec K L)
  · rw [e.toLinearEquiv.finrank_eq]
    exact finiteGlobalFundamentalClass_spec K M

/-- For an already embedded top field, the canonical arithmetic realization
gives the same class as the construction using that given field. -/
theorem finiteGlobalFundamentalClass_eq_canonical (E : FiniteGaloisIntermediateField
    K (SeparableClosure K)) [NumberField E] :
    finiteGlobalFundamentalClass K E = canonicalGlobalFundamentalClass K E := by
  apply HasFiniteGlobalInvariant.eq K E (finiteGlobalFundamentalClass_spec K E)
  obtain ⟨F, hEF, x, hx, hq⟩ := canonicalGlobalFundamentalClass_spec K E
  let : NumberField F := NumberField.of_module_finite K F
  let i : E →ₐ[K] F :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff E F).mp hEF)
  exact ⟨F, i, x, hx, hq⟩

end GlobalClassFieldTheory.Cohomology
