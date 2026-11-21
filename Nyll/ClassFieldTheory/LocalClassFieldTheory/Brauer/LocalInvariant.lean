/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteBaseChange
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteRepresentative
public import Nyll.ClassFieldTheory.Algebra.Brauer.RelativeRestrictionKernel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FiniteDegreeBound
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.UnramifiedAbsolute
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.UnramifiedRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient
public import Nyll.GaloisCohomology.Kummer.LiftedCyclicUnitsH2BaseChange
public import Nyll.GaloisCohomology.Topology.FiniteExtensionGalois
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramifiedEquiv
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction

/-! # The local cohomological Brauer invariant -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory ClassFormation ClassFieldTower.Cohomology
open LocalClassFieldTheory TopRep ContinuousCohomology
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField Module RamificationTheory

noncomputable section

namespace ClassFieldTheory.Brauer

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]


noncomputable local instance embeddedStageSpectralNormedField
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] :
    NontriviallyNormedField E :=
  finiteExtensionSpectralNormedField K E

noncomputable local instance embeddedStageSpectralValuativeRel
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] :
    ValuativeRel E :=
  finiteExtensionSpectralValuativeRel K E

noncomputable local instance embeddedStageSpectralLocalField
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] :
    IsNonarchimedeanLocalField E :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K E

noncomputable local instance stageValuationHasExtension
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] :
    Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
  finiteExtensionSpectralValuation_hasExtension K E

private def stageResidueFinrank (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] : ℕ :=
  @Module.finrank 𝓀[K] 𝓀[E] _ _
    (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[E]))

private theorem stageResidueFinrank_pos (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] : 0 < stageResidueFinrank K E := by
  let : Module 𝓀[K] 𝓀[E] := IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[E])
  exact Module.finrank_pos (R := 𝓀[K]) (M := 𝓀[E])

private def stageAbstractField (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] :
    FiniteAbstractField Gal((SeparableClosure K)/K) where
  field := closedFixingSubgroup K (SeparableClosure K) E
  finite := by
    apply Nat.finite_of_card_ne_zero
    change (E.fixingSubgroup.subgroupOf (⊤ : Subgroup _)).index ≠ 0
    rw [show (E.fixingSubgroup.subgroupOf (⊤ : Subgroup _)).index =
        E.fixingSubgroup.index from Subgroup.relIndex_top_right _,
      ← IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K) E]
    exact (Module.finrank_pos : 0 < finrank K E).ne'

private theorem stageResidueFinrank_congr
    {E F : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K E] [FiniteDimensional K F] (h : E = F) :
    stageResidueFinrank K E = stageResidueFinrank K F := by
  subst F
  rfl

private theorem stageAbstractField_residueDegree
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] :
    ((stageAbstractField K E).residueDegree (localResidueDatum K) : ℕ) =
      stageResidueFinrank K E := by
  let H := stageAbstractField K E
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
  have hF : F = E := InfiniteGalois.fixedField_fixingSubgroup E
  have hf : (H.residueDegree (localResidueDatum K) : ℕ) = stageResidueFinrank K F :=
    localResidueDatum_residueDegree_eq_residueFinrank K H
  exact hf.trans (stageResidueFinrank_congr K hF)

private theorem residueDegree_multiple_of_fixes (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] (σ : Gal((SeparableClosure K)/K))
    (hσ : σ ∈ E.fixingSubgroup) :
    ∃ z : ZHat, (localResidueDegree K σ).toAdd = stageResidueFinrank K E • z := by
  let D := localResidueDatum K
  let H := stageAbstractField K E
  let F := H.toFiniteResidueAbstractField D
  let s : F.field.toSubgroup := ⟨σ, hσ⟩
  have h := D.residueDegree_nsmul_normalizedDegree F s
  change ((H.residueDegree D : ℕ) • (D.normalizedDegree F s).toAdd) =
    (localResidueDegree K σ).toAdd at h
  rw [stageAbstractField_residueDegree K E] at h
  exact ⟨(D.normalizedDegree F s).toAdd, h.symm⟩

/-- An actual finite unramified field in the chosen closure is the canonical
unramified layer of the same degree. -/
theorem stage_eq_unramifiedBrauerStage (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [IsUnramifiedValuedExtension K E]
    (d : ℕ+) (hd : finrank K E = (d : ℕ)) : E = unramifiedBrauerStage K d := by
  apply FiniteGaloisIntermediateField.val_injective
  symm
  apply IntermediateField.eq_of_le_of_finrank_eq
  · rw [← InfiniteGalois.fixedField_fixingSubgroup (unramifiedBrauerStage K d).toIntermediateField,
      ← InfiniteGalois.fixedField_fixingSubgroup E.toIntermediateField]
    apply IntermediateField.fixedField_le
    intro σ hσ
    obtain ⟨z, hz⟩ := residueDegree_multiple_of_fixes K E σ hσ
    have hf : stageResidueFinrank K E = (d : ℕ) :=
      (unramifiedValuation_residue_finrank_eq_finrank K E).trans hd
    apply (localFiniteUnramifiedField_mem_fixingSubgroup_iff K d d.pos σ).mpr
    apply Multiplicative.ext
    change zHatReduction d d.pos (localResidueDegree K σ).toAdd = 0
    rw [hz, hf, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · exact (localFiniteUnramifiedField_finrank K d d.pos).trans hd.symm

private theorem stage_ramification_mul_residue (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] :
    (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[K] * stageResidueFinrank K E = finrank K E := by
  let : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]) (IsDiscreteValuationRing.not_isField 𝒪[K])
  simpa only [stageResidueFinrank, Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp] using
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank K E

private theorem stage_valuation_mapBaseUnits (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] (a : Kˣ) :
    v E (Additive.ofMul (mapBaseUnitsToExtensionUnits K E a)) =
      ((𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[K] : ℤ) * v K (Additive.ofMul a) := by
  let hc := localCompleteDVF_integerRing_isIntegralClosure K (↥E)
  exact @v_mapBaseUnitsToExtensionUnits_eq_ramificationIdx_mul K (↥E)
    _ _ _ _ _ _ _ _ _ _ _ _ hc a

/-- Two equivariant transports of field-unit cohomology compose along
their original coefficient maps and Galois homomorphisms. -/
theorem transportCohomology_comp_apply
    {A B C P Q R : Type u} [Field A] [Field B] [Field C] [Field P] [Field Q] [Field R]
    [algebraAP : Algebra A P] [algebraBQ : Algebra B Q] [algebraCR : Algebra C R]
    (r : Gal(Q/B) →ₜ* Gal(P/A)) (s : Gal(R/C) →ₜ* Gal(Q/B)) (t : Gal(R/C) →ₜ* Gal(P/A))
    (j : P →+* Q) (i : Q →+* R) (d : P →+* R)
    (hr : ∀ (σ : Gal(Q/B)) (x : P), j (r σ x) = σ (j x))
    (hs : ∀ (σ : Gal(R/C)) (x : Q), i (s σ x) = σ (i x))
    (ht : ∀ (σ : Gal(R/C)) (x : P), d (t σ x) = σ (d x))
    (hg : ∀ σ, r (s σ) = t σ) (hf : ∀ x, i (j x) = d x)
    (x : continuousCohomology 2 (galoisUnitsRep A P)) :
    transportCohomology 2 s i hs (transportCohomology 2 r j hr x) =
      transportCohomology 2 t d ht x := by
  have h := galoisUnitsCohomologyMap_comp r s t j i d hr hs ht hg hf
  have hx := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply] at hx
  exact hx.symm

private theorem relativeInflationOfEmbedding_factor
    {B N : Type u} [Field B] [Field N] [Algebra B N] [FiniteDimensional B N] [IsGalois B N]
    (F : FiniteGaloisIntermediateField B (SeparableClosure B))
    [Algebra N (↥F.toIntermediateField)] [IsScalarTower B N (↥F.toIntermediateField)]
    (i : N →ₐ[B] SeparableClosure B)
    (h : ∀ x : N, (algebraMap N (↥F.toIntermediateField) x).val = i x)
    (x : continuousCohomology 2 (galoisUnitsRep B N)) :
    relativeInflationOfEmbedding i x =
      finiteInflation F (relativeInflation B N (↥F.toIntermediateField) x) := by
  let t := finiteRelativeRestriction B N (↥F.toIntermediateField)
  let r := embeddedGaloisRestriction (B := B) i
  let g := finiteGaloisRestriction F
  have hg (σ : Gal(SeparableClosure B/B)) : t (g σ) = r σ := by
    apply AlgEquiv.ext
    intro a
    apply i.injective
    calc
      i (t (g σ) a) = F.toIntermediateField.val
          (algebraMap N (↥F.toIntermediateField) (t (g σ) a)) := (h _).symm
      _ = F.toIntermediateField.val (g σ (algebraMap N (↥F.toIntermediateField) a)) :=
        congrArg F.toIntermediateField.val ((g σ).restrictNormal_commutes N a)
      _ = σ (i a) := (finiteGaloisRestriction_commutes F σ _).trans (congrArg σ (h a))
      _ = i (r σ a) := (embeddedGaloisRestriction_commutes i σ a).symm
  have hc := transportCohomology_comp_apply t g r
    (algebraMap N (↥F.toIntermediateField)) F.toIntermediateField.val.toRingHom i.toRingHom
    (fun σ a => σ.restrictNormal_commutes N a) (finiteGaloisRestriction_commutes F)
    (embeddedGaloisRestriction_commutes i) hg h x
  exact hc.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem restrictOfEmbedding_finiteInflation_eq_transport
    {B : Type u} [Field B] (M : FiniteGaloisIntermediateField K (SeparableClosure K))
    (r : Gal(SeparableClosure B/B) →ₜ* Gal(SeparableClosure K/K))
    (i : SeparableClosure K →+* SeparableClosure B)
    (hi : ∀ (σ : Gal(SeparableClosure B/B)) (x : SeparableClosure K), i (r σ x) = σ (i x))
    (t : Gal(SeparableClosure B/B) →ₜ* Gal(M/K)) (f : M →+* SeparableClosure B)
    (hf : ∀ (σ : Gal(SeparableClosure B/B)) (x : M), f (t σ x) = σ (f x))
    (hg : ∀ σ, finiteGaloisRestriction M (r σ) = t σ)
    (hc : ∀ x : M, i x.val = f x) (x : relativeBr M) :
    restrictOfEmbedding r i hi (finiteInflation M x) = transportCohomology 2 t f hf x :=
  transportCohomology_comp_apply (finiteGaloisRestriction M) r t
    M.toIntermediateField.val.toRingHom i f (finiteGaloisRestriction_commutes M) hi hf hg hc x

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem transport_eq_finiteTowerInflation
    {B : Type u} [Field B] [Algebra K B]
    (M : FiniteGaloisIntermediateField K (SeparableClosure K))
    (N : Type u) [Field N] [Algebra K N] [Algebra B N] [Algebra (↥M.toIntermediateField) N]
    [IsScalarTower K B N] [IsScalarTower K (↥M.toIntermediateField) N]
    [FiniteDimensional K N] [FiniteDimensional B N] [IsGalois B N]
    (i : N →ₐ[B] SeparableClosure B)
    (r : Gal(SeparableClosure B/B) →ₜ* Gal(M/K)) (f : M →+* SeparableClosure B)
    (hf : ∀ (σ : Gal(SeparableClosure B/B)) (x : M), f (r σ x) = σ (f x))
    (hg : ∀ σ : Gal(SeparableClosure B/B),
      finiteRelativeRestriction K M N (relativeBaseRestrictionHom K B N
        (embeddedGaloisRestriction (B := B) i σ)) = r σ)
    (hc : ∀ x : M, i (algebraMap (↥M.toIntermediateField) N x) = f x)
    (x : relativeBr M) :
    transportCohomology 2 r f hf x = relativeInflationOfEmbedding i
      (relativeBaseRestriction K B N (relativeInflation K M N x)) := by
  let q := finiteRelativeRestriction K M N
  let s := relativeBaseRestrictionHom K B N
  let t := embeddedGaloisRestriction (B := B) i
  let qs := q.comp s
  let k := algebraMap (↥M.toIntermediateField) N
  have hq (σ : Gal(N/K)) (a : M) : k (q σ a) = σ (k a) :=
    σ.restrictNormal_commutes (↥M.toIntermediateField) a
  have hqs (σ : Gal(N/B)) (a : M) : k (qs σ a) = σ (k a) := hq (s σ) a
  have hMid := transportCohomology_comp_apply q s qs k (RingHom.id N) k
    hq (fun _ _ => rfl) hqs (fun _ => rfl) (fun _ => rfl) x
  have hRight := transportCohomology_comp_apply qs t r
    k i.toRingHom f hqs (embeddedGaloisRestriction_commutes i) hf hg hc x
  exact hRight.symm.trans (congrArg (relativeInflationOfEmbedding i) hMid.symm)


section Compositum

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (M : FiniteGaloisIntermediateField K (SeparableClosure K))

/-- The actual compositum of a finite intermediate field and a finite Galois layer. -/
def compositumStage (E : IntermediateField K (SeparableClosure K))
    (M : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    IntermediateField K (SeparableClosure K) :=
  E ⊔ M.toIntermediateField

local instance compositumStageFiniteDimensional :
    FiniteDimensional K (compositumStage K E M) :=
  inferInstanceAs (FiniteDimensional K ↥(E ⊔ M.toIntermediateField))

noncomputable local instance leftStageAlgebra : Algebra E (compositumStage K E M) :=
  (IntermediateField.inclusion
    (show E ≤ (compositumStage K E M) from le_sup_left)).toRingHom.toAlgebra

noncomputable local instance rightStageAlgebra : Algebra M (compositumStage K E M) :=
  (IntermediateField.inclusion
    (show M.toIntermediateField ≤ (compositumStage K E M) from le_sup_right)).toRingHom.toAlgebra

local instance leftStageScalarTower : IsScalarTower K E (compositumStage K E M) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance rightStageScalarTower : IsScalarTower K M (compositumStage K E M) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance leftStageFiniteDimensional : FiniteDimensional E (compositumStage K E M) :=
  FiniteDimensional.right K E (compositumStage K E M)

local instance rightStageFiniteDimensional : FiniteDimensional M (compositumStage K E M) :=
  FiniteDimensional.right K M (compositumStage K E M)

local instance leftStageIsGalois : IsGalois E (compositumStage K E M) := by
  let A : IntermediateField K (compositumStage K E M) :=
    E.restrict (show E ≤ (compositumStage K E M) from le_sup_left)
  let B : IntermediateField K (compositumStage K E M) :=
    M.toIntermediateField.restrict
      (show M.toIntermediateField ≤ (compositumStage K E M) from le_sup_right)
  let eA : E ≃ₐ[K] A := IntermediateField.restrictAlgEquiv le_sup_left
  let eB : M ≃ₐ[K] B := IntermediateField.restrictAlgEquiv le_sup_right
  let : FiniteDimensional K B := eB.toLinearEquiv.finiteDimensional
  let : IsGalois K B := eB.transfer_galois.mp inferInstance
  have hsup : B ⊔ A = ⊤ := by
    apply IntermediateField.lift_injective (compositumStage K E M)
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top, compositumStage]
    exact sup_comm _ _
  let : IsGalois A (compositumStage K E M) := IsGalois.sup_right B A hsup
  apply IsGalois.of_equiv_equiv (f := eA.symm.toRingEquiv)
    (g := RingEquiv.refl (compositumStage K E M))
  apply RingHom.ext
  intro a
  exact congrArg (fun b : A => (b : (compositumStage K E M))) (eA.apply_symm_apply a)

noncomputable local instance leftStageValuationHasExtension :
    Valuation.HasExtension (ValuativeRel.valuation E)
      (ValuativeRel.valuation (compositumStage K E M)) :=
  finiteExtensionSpectralValuation_hasExtension_of_tower K E (compositumStage K E M)

noncomputable local instance rightStageValuationHasExtension :
    Valuation.HasExtension (ValuativeRel.valuation M)
      (ValuativeRel.valuation (compositumStage K E M)) :=
  finiteExtensionSpectralValuation_hasExtension_of_tower K M (compositumStage K E M)

private def compositumRestriction : Gal((compositumStage K E M)/E) →* Gal(M/K) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := (compositumStage K E M)) M).comp
    (AlgEquiv.restrictScalarsHom K)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] in
private theorem compositumRestriction_lift (σ : Gal((compositumStage K E M)/E)) :
    ∃ τ : Gal((SeparableClosure K)/K),
      (∀ x : compositumStage K E M, τ ((compositumStage K E M).val x) =
        (compositumStage K E M).val (σ x)) ∧
      τ ∈ E.fixingSubgroup ∧ finiteGaloisRestriction M τ = compositumRestriction K E M σ := by
  obtain ⟨τ, hτ⟩ := AlgebraicNumberTheory.exists_separableClosureEmbeddingComparisonAutomorphism
    (compositumStage K E M).val ((compositumStage K E M).val.comp (σ.restrictScalars K).toAlgHom)
  refine ⟨τ, hτ, ?_, ?_⟩
  · apply (IntermediateField.mem_fixingSubgroup_iff E τ).mpr
    intro x hx
    let y : E := ⟨x, hx⟩
    exact (hτ (algebraMap E (compositumStage K E M) y)).trans
      (congrArg (compositumStage K E M).val (σ.commutes y))
  · apply AlgEquiv.ext
    intro y
    apply M.toIntermediateField.val.injective
    let N := compositumStage K E M
    let a : N := algebraMap M N y
    change M.toIntermediateField.val (finiteGaloisRestriction M τ y) =
      M.toIntermediateField.val (compositumRestriction K E M σ y)
    calc
      _ = τ (M.toIntermediateField.val y) := finiteGaloisRestriction_commutes M τ y
      _ = N.val (σ a) := hτ a
      _ = _ := (congrArg N.val ((σ.restrictScalars K).restrictNormal_commutes M y)).symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] in
private theorem compositumRestriction_injective :
    Function.Injective (compositumRestriction K E M) := by
  apply (injective_iff_map_eq_one (compositumRestriction K E M)).mpr
  intro σ hσ
  obtain ⟨τ, hτ, hE, hM⟩ := compositumRestriction_lift K E M σ
  have hfixM : τ ∈ M.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]
    exact hM.trans hσ
  have hfix : τ ∈ (compositumStage K E M).fixingSubgroup := by
    rw [compositumStage, IntermediateField.fixingSubgroup_sup]
    exact ⟨hE, hfixM⟩
  apply AlgEquiv.ext
  intro x
  apply (compositumStage K E M).val.injective
  exact (hτ x).symm.trans
    ((IntermediateField.mem_fixingSubgroup_iff (compositumStage K E M) τ).mp hfix _ x.property)

private theorem compositum_finrank_dvd_of_stage_degree (d : ℕ+) (m : ℕ)
    (hdegree : m * stageResidueFinrank K E = (d : ℕ)) :
    finrank E (compositumStage K E (unramifiedBrauerStage K d)) ∣ m := by
  let M := unramifiedBrauerStage K d
  let N : IntermediateField K (SeparableClosure K) := compositumStage K E M
  let r := compositumRestriction K E M
  let : IsCyclic Gal(M/K) := isCyclic_galoisGroup_of_unramifiedValuation K M
  let : IsCyclic Gal(N/E) := isCyclic_of_injective r (compositumRestriction_injective K E M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(N/E))
  obtain ⟨τ, _, hE, hM⟩ := compositumRestriction_lift K E M σ
  obtain ⟨z, hz⟩ := residueDegree_multiple_of_fixes K E τ hE
  have hfix : τ ^ m ∈ M.fixingSubgroup := by
    apply (localFiniteUnramifiedField_mem_fixingSubgroup_iff K d d.pos (τ ^ m)).mpr
    apply Multiplicative.ext
    change zHatReduction d d.pos (localResidueDegree K (τ ^ m)).toAdd = 0
    rw [map_pow]
    change zHatReduction d d.pos (m • (localResidueDegree K τ).toAdd) = 0
    rw [hz, smul_smul, hdegree, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  change τ ^ m ∈ M.toIntermediateField.fixingSubgroup at hfix
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker] at hfix
  change finiteGaloisRestriction M (τ ^ m) = 1 at hfix
  rw [map_pow, hM] at hfix
  have hpow : σ ^ m = 1 :=
    (compositumRestriction_injective K E M) (by rw [map_pow, map_one]; exact hfix)
  rw [← IsGalois.card_aut_eq_finrank E N, ← orderOf_eq_card_of_forall_mem_zpowers hσ]
  exact orderOf_dvd_of_pow_eq_one hpow

private noncomputable def valuationExtensionResidueFinrank (P Q : Type*)
    [Field P] [Field Q] [ValuativeRel P] [ValuativeRel Q] [Algebra P Q]
    [Valuation.HasExtension (ValuativeRel.valuation P) (ValuativeRel.valuation Q)] : ℕ :=
  @Module.finrank 𝓀[P] 𝓀[Q] _ _
    (IsLocalRing.ResidueField.instModule (R := 𝒪[P]) (S := 𝒪[Q]))

private theorem valuationExtensionResidueFinrank_pos (P Q : Type*)
    [Field P] [Field Q] [ValuativeRel P] [ValuativeRel Q] [Algebra P Q] [Finite 𝓀[Q]]
    [Valuation.HasExtension (ValuativeRel.valuation P) (ValuativeRel.valuation Q)] :
    0 < valuationExtensionResidueFinrank P Q :=
  Module.finrank_pos (R := 𝓀[P]) (M := 𝓀[Q])

private theorem residueFinrank_dvd_of_two_towers (P Q R S : Type*)
    [Field P] [Field Q] [Field R] [Field S]
    [ValuativeRel P] [ValuativeRel Q] [ValuativeRel R] [ValuativeRel S]
    [Algebra P Q] [Algebra P R] [Algebra P S] [Algebra Q S] [Algebra R S]
    [IsScalarTower P Q S] [IsScalarTower P R S]
    [Valuation.HasExtension (ValuativeRel.valuation P) (ValuativeRel.valuation Q)]
    [Valuation.HasExtension (ValuativeRel.valuation P) (ValuativeRel.valuation R)]
    [Valuation.HasExtension (ValuativeRel.valuation P) (ValuativeRel.valuation S)]
    [Valuation.HasExtension (ValuativeRel.valuation Q) (ValuativeRel.valuation S)]
    [Valuation.HasExtension (ValuativeRel.valuation R) (ValuativeRel.valuation S)]
    (m d : ℕ) (hq : 0 < valuationExtensionResidueFinrank P Q)
    (hd : m * valuationExtensionResidueFinrank P Q = d)
    (hR : valuationExtensionResidueFinrank P R = d) :
    m ∣ valuationExtensionResidueFinrank Q S := by
  let : IsScalarTower 𝓀[P] 𝓀[Q] 𝓀[S] := residueField_isScalarTower_of_valuationExtension P Q S
  let : IsScalarTower 𝓀[P] 𝓀[R] 𝓀[S] := residueField_isScalarTower_of_valuationExtension P R S
  have hdiv : valuationExtensionResidueFinrank P R ∣ valuationExtensionResidueFinrank P S :=
    Module.finrank_dvd_finrank_right 𝓀[P] 𝓀[R] 𝓀[S]
  have hmul : valuationExtensionResidueFinrank P Q * valuationExtensionResidueFinrank Q S =
      valuationExtensionResidueFinrank P S := Module.finrank_mul_finrank 𝓀[P] 𝓀[Q] 𝓀[S]
  rw [hR, ← hmul, ← hd, mul_comm m] at hdiv
  exact Nat.dvd_of_mul_dvd_mul_left hq hdiv

private theorem eq_one_and_degree_of_bounds {r t n m : ℕ}
    (hr : 0 < r) (hn : 0 < n) (hmin : m ≤ r) (hmax : n ≤ m) (htr : t * r = n) :
    t = 1 ∧ n = m := by
  have hle : r ≤ n := Nat.le_of_dvd hn ⟨t, htr.symm.trans (mul_comm t r)⟩
  have heq : n = r := le_antisymm (hmax.trans hmin) hle
  refine ⟨Nat.eq_of_mul_eq_mul_right hr ?_, le_antisymm hmax (hmin.trans hle)⟩
  exact htr.trans (heq.trans (one_mul r).symm)

private theorem valuationExtension_unramified_of_degree_bounds (P Q : Type*)
    [Field P] [Field Q] [ValuativeRel P] [ValuativeRel Q] [Algebra P Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [IsNonarchimedeanLocalField P] [IsNonarchimedeanLocalField Q]
    [FiniteDimensional P Q]
    [Valuation.HasExtension (ValuativeRel.valuation P) (ValuativeRel.valuation Q)]
    [Module.Finite 𝒪[P] 𝒪[Q]]
    (m : ℕ) (hmin : m ≤ valuationExtensionResidueFinrank P Q)
    (hmax : finrank P Q ≤ m) :
    IsUnramifiedValuedExtension P Q ∧ finrank P Q = m := by
  let r := valuationExtensionResidueFinrank P Q
  let t := (𝓂[Q] : Ideal 𝒪[Q]).ramificationIdx 𝒪[P]
  have hp : (𝓂[P] : Ideal 𝒪[P]) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[P]) (IsDiscreteValuationRing.not_isField 𝒪[P])
  have he : Ideal.ramificationIdx' (𝓂[P] : Ideal 𝒪[P]) (𝓂[Q] : Ideal 𝒪[Q]) = t :=
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp
  have htr : t * r = finrank P Q :=
    (congrArg (· * r) he).symm.trans
      (maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank P Q)
  have hr : 0 < r := Module.finrank_pos (R := 𝓀[P]) (M := 𝓀[Q])
  obtain ⟨ht, hf⟩ := eq_one_and_degree_of_bounds hr Module.finrank_pos hmin hmax htr
  exact ⟨⟨ht⟩, hf⟩

private theorem compositum_integerRingData :
    let N : IntermediateField K (SeparableClosure K) := compositumStage K E M
    IsIntegralClosure 𝒪[N] 𝒪[E] N ∧ Module.Finite 𝒪[E] 𝒪[N] := by
  intro N
  exact ⟨localCompleteDVF_integerRing_isIntegralClosure E N,
    localCompleteDVF_integerRing_moduleFinite E N⟩

private theorem compositum_isUnramified_and_finrank (d : ℕ+) (m : ℕ)
    (hdegree : m * stageResidueFinrank K E = (d : ℕ)) :
    IsUnramifiedValuedExtension E (compositumStage K E (unramifiedBrauerStage K d)) ∧
      finrank E (compositumStage K E (unramifiedBrauerStage K d)) = m := by
  let M := unramifiedBrauerStage K d
  let N : IntermediateField K (SeparableClosure K) := compositumStage K E M
  let : Algebra E N := leftStageAlgebra K E M
  let : Algebra M N := rightStageAlgebra K E M
  let : IsScalarTower K E N := leftStageScalarTower K E M
  let : IsScalarTower K M N := rightStageScalarTower K E M
  let : Valuation.HasExtension (ValuativeRel.valuation E) (ValuativeRel.valuation N) :=
    leftStageValuationHasExtension K E M
  let : Valuation.HasExtension (ValuativeRel.valuation M) (ValuativeRel.valuation N) :=
    rightStageValuationHasExtension K E M
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation N) :=
    finiteExtensionSpectralValuation_hasExtension K N
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension K M
  let r := valuationExtensionResidueFinrank E N
  have hm : valuationExtensionResidueFinrank K M = (d : ℕ) :=
    localFiniteUnramifiedField_residue_finrank K d d.pos
  have hres' : m ∣ r := residueFinrank_dvd_of_two_towers K E M N m d
    (stageResidueFinrank_pos K E) hdegree hm
  let : Module.Finite 𝒪[E] 𝒪[N] := (compositum_integerRingData K E M).2
  have hmin : m ≤ r := Nat.le_of_dvd (valuationExtensionResidueFinrank_pos E N) hres'
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun hm0 => by
    rw [hm0, zero_mul] at hdegree
    exact d.pos.ne' hdegree.symm
  have hmax : finrank E N ≤ m :=
    Nat.le_of_dvd hmpos (compositum_finrank_dvd_of_stage_degree K E d m hdegree)
  exact valuationExtension_unramified_of_degree_bounds E N m hmin hmax

private theorem compositum_base_unit_mem_norm (d : ℕ+)
    (hd : (d : ℕ) = finrank K E) (a : Kˣ) :
    mapBaseUnitsToExtensionUnits K E a ∈
      localNormSubgroup E (compositumStage K E (unramifiedBrauerStage K d)) := by
  let M := unramifiedBrauerStage K d
  let N : IntermediateField K (SeparableClosure K) := compositumStage K E M
  let e := (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[K]
  have hdegree : e * stageResidueFinrank K E = (d : ℕ) :=
    (stage_ramification_mul_residue K E).trans hd.symm
  let : IsUnramifiedValuedExtension E N := (compositum_isUnramified_and_finrank K E d e hdegree).1
  let : IsIntegralClosure 𝒪[N] 𝒪[E] N := (compositum_integerRingData K E M).1
  change mapBaseUnitsToExtensionUnits K E a ∈ localNormSubgroup E N
  rw [mem_normSubgroup_unramifiedValuation_iff_finrank_dvd_valuation_of_isIntegralClosure E N]
  change (finrank E N : ℤ) ∣ valuationMap E (Additive.ofMul (mapBaseUnitsToExtensionUnits K E a))
  rw [valuationMap_apply, stage_valuation_mapBaseUnits K E a]
  exact dvd_mul_of_dvd_left
    (Int.natCast_dvd_natCast.mpr (compositum_finrank_dvd_of_stage_degree K E d e hdegree)) _

private theorem compositum_carry_restriction_eq_zero (d : ℕ+)
    (hd : (d : ℕ) = finrank K E) (a : Kˣ) :
    let M := unramifiedBrauerStage K d
    let N : IntermediateField K (SeparableClosure K) := compositumStage K E M
    let _ : Algebra M N := rightStageAlgebra K E M
    let _ : IsScalarTower K M N := rightStageScalarTower K E M
    liftedFiniteGaloisTowerUnitsH2Restriction K E N
      (liftedFiniteGaloisTowerUnitsH2Inflation K M N
        (unramifiedClass K M (Additive.ofMul a))) = 0 := by
  intro M N _ _
  let : IsCyclic Gal(M/K) := isCyclic_galoisGroup_of_unramifiedValuation K M
  let : IsCyclic Gal(N/E) := isCyclic_of_injective (compositumRestriction K E M)
    (compositumRestriction_injective K E M)
  obtain ⟨b, hb⟩ := compositum_base_unit_mem_norm K E d hd a
  rw [unramifiedClass_apply]
  exact liftedCyclicBaseUnitH2Class_inflation_restriction_eq_zero_of_norm K M E N
    (arithmeticFrobeniusOfUnramifiedValuation K M)
    (arithmeticFrobeniusOfUnramifiedValuation_generates K M) a (b : N) (congrArg Units.val hb)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem finiteInflation_sup_left
    (E M : FiniteGaloisIntermediateField K (SeparableClosure K)) (x : relativeBr E) :
    let N := E ⊔ M
    let _ : Algebra E N := leftStageAlgebra K E.toIntermediateField M
    let _ : IsScalarTower K E N := leftStageScalarTower K E.toIntermediateField M
    finiteInflation N (relativeInflation K E N x) = finiteInflation E x := by
  intro N aEN tKEN
  exact finiteInflation_tower E N (fun x => rfl) x

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem finiteInflation_sup_right
    (E M : FiniteGaloisIntermediateField K (SeparableClosure K)) (x : relativeBr M) :
    let N := E ⊔ M
    let _ : Algebra M N := rightStageAlgebra K E.toIntermediateField M
    let _ : IsScalarTower K M N := rightStageScalarTower K E.toIntermediateField M
    finiteInflation N (relativeInflation K M N x) = finiteInflation M x := by
  intro N aMN tKMN
  exact finiteInflation_tower M N (fun x => rfl) x

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem finiteInflation_eq_of_agree_in_compositum
    (E M : FiniteGaloisIntermediateField K (SeparableClosure K))
    (b : relativeBr E) (c : relativeBr M) :
    let N := E ⊔ M
    let _ : Algebra E N := leftStageAlgebra K E.toIntermediateField M
    let _ : Algebra M N := rightStageAlgebra K E.toIntermediateField M
    let _ : IsScalarTower K E N := leftStageScalarTower K E.toIntermediateField M
    let _ : IsScalarTower K M N := rightStageScalarTower K E.toIntermediateField M
    relativeInflation K E N b = relativeInflation K M N c →
      finiteInflation M c = finiteInflation E b := by
  intro N aEN aMN tKEN tKMN h
  exact (finiteInflation_sup_right K E M c).symm.trans
    ((congrArg (finiteInflation N) h.symm).trans (finiteInflation_sup_left K E M b))

private theorem exists_relative_generator_with_unramified_inflation
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    ∃ b : groupCohomology (liftedGaloisUnitsRep K E) 2,
      addOrderOf b = finrank K E ∧
        finiteInflation E ((continuousRelativeUnitsH2Equiv K E).symm b) ∈ unramifiedBr K := by
  let d : ℕ+ := ⟨finrank K E, Module.finrank_pos⟩
  let M := unramifiedBrauerStage K d
  let N : FiniteGaloisIntermediateField K (SeparableClosure K) := E ⊔ M
  let E₀ := E.toIntermediateField
  let : Algebra E N := leftStageAlgebra K E₀ M
  let : Algebra M N := rightStageAlgebra K E₀ M
  let : IsScalarTower K E N := leftStageScalarTower K E₀ M
  let : IsScalarTower K M N := rightStageScalarTower K E₀ M
  let a := integerRingUniformizerFieldUnit K
  let c := unramifiedClass K M (Additive.ofMul a)
  let f := liftedFiniteGaloisTowerUnitsH2Inflation K E N
  let g := liftedFiniteGaloisTowerUnitsH2Inflation K M N
  let r := liftedFiniteGaloisTowerUnitsH2Restriction K E N
  have hc : r (g c) = 0 := compositum_carry_restriction_eq_zero K E d rfl a
  obtain ⟨b, hb⟩ := liftedFiniteGaloisTowerUnitsH2Restriction_ker_le_inflation_range K E N hc
  have horderC : addOrderOf c = (d : ℕ) := by
    let : Fact (0 < (1 : ℚ)) := ⟨zero_lt_one⟩
    have hcvalue : unramifiedInvariant K M c = ((1 : ℚ) / (d : ℕ) : ℚ) := by
      rw [show c = unramifiedClass K M
        (Additive.ofMul (integerRingUniformizerFieldUnit K)) from rfl,
        unramifiedInvariant_uniformizer, localFiniteUnramifiedField_finrank K d d.pos]
    calc
      addOrderOf c = addOrderOf (unramifiedInvariant K M c) :=
        (addOrderOf_injective (unramifiedInvariant K M) (unramifiedInvariant_injective K M) c).symm
      _ = (d : ℕ) := by rw [hcvalue, AddCircle.addOrderOf_period_div d.pos]
  have horderB : addOrderOf b = (d : ℕ) := by
    calc
      addOrderOf b = addOrderOf (f.hom b) :=
        (addOrderOf_injective f.hom.toAddMonoidHom
          (liftedFiniteGaloisTowerUnitsH2Inflation_injective K E N) b).symm
      _ = addOrderOf (g.hom c) := congrArg addOrderOf hb
      _ = addOrderOf c :=
        addOrderOf_injective g.hom.toAddMonoidHom
          (liftedFiniteGaloisTowerUnitsH2Inflation_injective K M N) c
      _ = (d : ℕ) := horderC
  let eE := continuousRelativeUnitsH2Equiv K E
  let eM := continuousRelativeUnitsH2Equiv K M
  let eT := continuousRelativeUnitsH2Equiv K N
  let bE : relativeBr E := eE.symm b
  let cM : relativeBr M := eM.symm c
  have hmap : relativeInflation K E N bE = relativeInflation K M N cM := by
    have hE := (continuousRelativeUnitsH2Equiv_inflation K E N bE).trans
      (congrArg f.hom (eE.apply_symm_apply b))
    have hM := (continuousRelativeUnitsH2Equiv_inflation K M N cM).trans
      (congrArg g.hom (eM.apply_symm_apply c))
    exact eT.injective (hE.trans (hb.trans hM.symm))
  have hgen : finiteInflation E bE ∈ unramifiedBr K :=
    (mem_unramifiedBr_iff K _).mpr
      ⟨d, cM, finiteInflation_eq_of_agree_in_compositum K E M bE cM hmap⟩
  exact ⟨b, horderB, hgen⟩

private theorem finiteInflation_mem_unramifiedBr
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (x : relativeBr E) :
    finiteInflation E x ∈ unramifiedBr K := by
  let eE := continuousRelativeUnitsH2Equiv K E
  obtain ⟨b, horderB, hgen⟩ := exists_relative_generator_with_unramified_inflation K E
  obtain ⟨hFinite, hBound⟩ := finiteLocalUnitsH2_finite_card_le K E
  let : Finite (groupCohomology (liftedGaloisUnitsRep K E) 2) := hFinite
  let S := AddSubgroup.zmultiples b
  have hcard : Nat.card (groupCohomology (liftedGaloisUnitsRep K E) 2) ≤ Nat.card S := by
    rw [show Nat.card S = addOrderOf b from Nat.card_zmultiples b, horderB]
    exact hBound
  have hsurj : Function.Surjective S.subtype :=
    (S.subtype_injective.bijective_of_nat_card_le hcard).2
  obtain ⟨y, hy⟩ := hsurj (eE x)
  obtain ⟨m, hm⟩ := y.property
  have hx : x = m • eE.symm b := by
    apply eE.injective
    rw [map_zsmul, eE.apply_symm_apply]
    exact hy.symm.trans hm.symm
  rw [hx, map_zsmul]
  exact (unramifiedBr K).zsmul_mem hgen m

section ClosureComparison

@[reducible] local instance stageSeparableClosureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

variable (j : (SeparableClosure K) ≃ₐ[E] SeparableClosure E)

/-- Restriction on the actual absolute Galois groups for a specified comparison of closures. -/
def embeddedAbsoluteRestrictionHom : Gal(SeparableClosure E/E) →ₜ* Gal((SeparableClosure K)/K) where
  toMonoidHom := (AlgEquiv.restrictScalarsHom K).comp (AlgEquiv.autCongr j.symm).toMonoidHom
  continuous_toFun := by
    let : Algebra.IsAlgebraic E (SeparableClosure K) := Algebra.IsAlgebraic.tower_top (K := K) E
    exact (GaloisCohomology.continuous_galoisRestrictScalars K E (SeparableClosure K)).comp
      (AlgebraicNumberTheory.continuous_algEquiv_autCongr j.symm)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] in
theorem embeddedAbsoluteRestrictionHom_commutes
    (σ : Gal(SeparableClosure E/E)) (a : SeparableClosure K) :
    j (embeddedAbsoluteRestrictionHom K E j σ a) = σ (j a) :=
  j.apply_symm_apply (σ (j a))

/-- The actual absolute Brauer restriction for the same embedding. -/
def embeddedAbsoluteBrRestriction : Br K →+ Br E :=
  restrictOfEmbedding (embeddedAbsoluteRestrictionHom K E j) j.toRingEquiv.toRingHom
    (embeddedAbsoluteRestrictionHom_commutes K E j)

/-- The compositum mapped into the chosen separable closure of the base stage. -/
def compositumClosureEmbedding :
    (compositumStage K E M) →ₐ[E] SeparableClosure E where
  toRingHom := j.toRingEquiv.toRingHom.comp (compositumStage K E M).val.toRingHom
  commutes' := j.commutes

/-- The finite Galois image of the compositum in the chosen upper closure. -/
def compositumImage : FiniteGaloisIntermediateField E (SeparableClosure E) :=
  (compositumClosureEmbedding K E M j).finiteGaloisFieldRange

/-- The original compositum identified with its image in the upper closure. -/
def compositumImageEquiv :
    let N : IntermediateField K (SeparableClosure K) := compositumStage K E M
    let F : FiniteGaloisIntermediateField E (SeparableClosure E) := compositumImage K E M j
    let aN : Algebra (↥E) (↥N) := leftStageAlgebra K E M
    let aF : Algebra (↥E) (↥F.toIntermediateField) := F.toIntermediateField.algebra
    @AlgEquiv (↥E) (↥N) (↥F.toIntermediateField) _ _ _ aN aF := by
  intro N F aN aF
  exact (compositumClosureEmbedding K E M j).equivFieldRange

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem compositumClosureEmbedding_restriction_coincides
    (σ : Gal(SeparableClosure E/E)) :
    let N : IntermediateField K (SeparableClosure K) := compositumStage K E M
    let _ : Algebra M N := rightStageAlgebra K E M
    let _ : Algebra E N := leftStageAlgebra K E M
    let _ : IsScalarTower K M N := rightStageScalarTower K E M
    let _ : IsScalarTower K E N := leftStageScalarTower K E M
    let _ : FiniteDimensional K N := compositumStageFiniteDimensional K E M
    let _ : FiniteDimensional E N := leftStageFiniteDimensional K E M
    let _ : Normal E N := (leftStageIsGalois K E M).to_normal
    finiteGaloisRestriction M (embeddedAbsoluteRestrictionHom K E j σ) =
      finiteRelativeRestriction K M N (relativeBaseRestrictionHom K E N
        (embeddedGaloisRestriction (B := ↥E) (compositumClosureEmbedding K E M j) σ)) := by
  intro N aMN aEN tKMN tKEN finKN finEN normEN
  let r := embeddedAbsoluteRestrictionHom K E j
  let s := relativeBaseRestrictionHom K E N
  let q := finiteRelativeRestriction K M N
  let i := compositumClosureEmbedding K E M j
  let t := embeddedGaloisRestriction (B := ↥E) i
  apply AlgEquiv.ext
  intro x
  apply (j.toRingEquiv.toRingHom.comp M.toIntermediateField.val.toRingHom).injective
  let fN : Gal(N/K) := s (t σ)
  have hn := fN.restrictNormal_commutes (↥M.toIntermediateField) x
  calc
    j (M.toIntermediateField.val (finiteGaloisRestriction M (r σ) x)) =
        j (r σ (M.toIntermediateField.val x)) :=
      congrArg j (finiteGaloisRestriction_commutes M (r σ) x)
    _ = σ (j (M.toIntermediateField.val x)) :=
      embeddedAbsoluteRestrictionHom_commutes K E j σ (M.toIntermediateField.val x)
    _ = j (N.val (fN (algebraMap M N x))) :=
      (embeddedGaloisRestriction_commutes i σ (algebraMap M N x)).symm
    _ = j (M.toIntermediateField.val (q fN x)) :=
      (congrArg (fun a : N => j (N.val a)) hn).symm

private def finiteStageRestrictionInClosure : Gal(SeparableClosure E / E) →ₜ* Gal(M / K) :=
  (finiteGaloisRestriction M).comp (embeddedAbsoluteRestrictionHom K E j)

private def finiteStageInClosure : M →+* SeparableClosure E :=
  j.toRingEquiv.toRingHom.comp M.toIntermediateField.val.toRingHom

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] in
private theorem finiteStageInClosure_commutes
    (σ : Gal(SeparableClosure E/E)) (a : M) :
    finiteStageInClosure K E M j (finiteStageRestrictionInClosure K E M j σ a) =
      σ (finiteStageInClosure K E M j a) :=
  (congrArg j (finiteGaloisRestriction_commutes M (embeddedAbsoluteRestrictionHom K E j σ) a)).trans
    (embeddedAbsoluteRestrictionHom_commutes K E j σ a.val)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] in
private theorem embeddedAbsoluteBrRestriction_finiteInflation
    (N : Type u) [Field N] [Algebra K N] [Algebra E N] [Algebra (↥M.toIntermediateField) N]
    [IsScalarTower K E N] [IsScalarTower K (↥M.toIntermediateField) N]
    [FiniteDimensional K N] [FiniteDimensional E N] [IsGalois E N]
    (i : N →ₐ[E] SeparableClosure E)
    (hg : ∀ σ : Gal(SeparableClosure E/E),
      finiteGaloisRestriction M (embeddedAbsoluteRestrictionHom K E j σ) =
        finiteRelativeRestriction K M N (relativeBaseRestrictionHom K E N
          (embeddedGaloisRestriction (B := ↥E) i σ)))
    (hcoeff : ∀ x : ↥M.toIntermediateField,
      i (algebraMap (↥M.toIntermediateField) N x) = j x.val)
    (x : relativeBr M) :
    embeddedAbsoluteBrRestriction K E j (finiteInflation M x) =
      relativeInflationOfEmbedding i
        (relativeBaseRestriction K E N (relativeInflation K M N x)) := by
  let r := embeddedAbsoluteRestrictionHom K E j
  let t := finiteStageRestrictionInClosure K E M j
  let f := finiteStageInClosure K E M j
  let hf := finiteStageInClosure_commutes K E M j
  have hStage := restrictOfEmbedding_finiteInflation_eq_transport K (B := ↥E)
    M r j.toRingEquiv.toRingHom
    (embeddedAbsoluteRestrictionHom_commutes K E j) t f hf (fun _ => rfl) (fun _ => rfl) x
  have hTower := transport_eq_finiteTowerInflation K (B := ↥E) M N i t f hf
    (fun σ => (hg σ).symm) hcoeff x
  exact hStage.trans hTower

end ClosureComparison

end Compositum

/-- Every continuous local Brauer class comes from a finite unramified extension. -/
theorem unramifiedBr_eq_top : unramifiedBr K = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨E, y, hy⟩ := exists_finiteInflation_eq x
  rw [← hy]
  exact finiteInflation_mem_unramifiedBr K E y

/-- The canonical inclusion of the unramified subgroup is an isomorphism. -/
def unramifiedBrSubtypeEquiv : unramifiedBr K ≃+ Br K :=
  AddEquiv.ofBijective (unramifiedBr K).subtype
    ⟨Subtype.val_injective, fun x =>
      ⟨⟨x, (unramifiedBr_eq_top K).symm ▸ AddSubgroup.mem_top x⟩, rfl⟩⟩

/-- The arithmetic invariant identifies the full cohomological Brauer group
of a nonarchimedean local field with `ℚ/ℤ`. -/
def localBrauerInvariantEquiv : Br K ≃+ AddCircle (1 : ℚ) :=
  (unramifiedBrSubtypeEquiv K).symm.trans (unramifiedBrauerInvariantEquiv K)

/-- The arithmetic invariant as an additive homomorphism on absolute degree two. -/
def localBrauerInvariant : Br K →+ AddCircle (1 : ℚ) :=
  (localBrauerInvariantEquiv K).toAddMonoidHom

/-- The Brauer group of a local field is divisible. -/
theorem localBrauer_nsmul_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun x : Br K => n • x) := by
  let e := localBrauerInvariantEquiv K
  intro x
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective (e x)
  refine ⟨e.symm ((q / (n : ℚ) : ℚ) : AddCircle (1 : ℚ)), e.injective ?_⟩
  rw [map_nsmul, AddEquiv.apply_symm_apply, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h := show (n : ℚ) * (q / (n : ℚ)) = q from by field_simp
  exact (congrArg (fun r : ℚ => (r : AddCircle (1 : ℚ))) h).trans hq

/-- The full invariant has the original finite-layer arithmetic evaluation. -/
@[simp] theorem localBrauerInvariant_finiteInflation (d : ℕ+)
    (x : relativeBr (unramifiedBrauerStage K d)) :
    localBrauerInvariant K (finiteInflation (unramifiedBrauerStage K d) x) =
      unramifiedBrauerStageInvariant K d x := by
  let y := unramifiedBrauerInflation K d x
  have hy : (unramifiedBrSubtypeEquiv K) y = finiteInflation (unramifiedBrauerStage K d) x := rfl
  change unramifiedBrauerInvariant K ((unramifiedBrSubtypeEquiv K).symm _) = _
  rw [← hy, AddEquiv.symm_apply_apply]
  exact unramifiedBrauerInvariant_inflation K d x

/-- An arbitrary finite unramified stage in the separable closure uses its
original relative invariant under actual inflation. -/
theorem localBrauerInvariant_finiteInflation_of_unramified
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [IsUnramifiedValuedExtension K E] (x : relativeBr E) :
    localBrauerInvariant K (finiteInflation E x) = unramifiedContinuousInvariant K E x := by
  have h (d : ℕ+) (hd : finrank K E = (d : ℕ)) :
      localBrauerInvariant K (finiteInflation E x) = unramifiedContinuousInvariant K E x := by
    have hE := stage_eq_unramifiedBrauerStage K E d hd
    subst E
    exact localBrauerInvariant_finiteInflation K d x
  exact h ⟨finrank K E, Module.finrank_pos⟩ rfl

/-- Arithmetic Frobenius paired with a DVR uniformizer gives `1 / d`. -/
theorem localBrauerInvariant_uniformizer (d : ℕ+) :
    localBrauerInvariant K (finiteInflation (unramifiedBrauerStage K d)
      (unramifiedContinuousClass K (localFiniteUnramifiedField K d d.pos)
        (Additive.ofMul (integerRingUniformizerFieldUnit K)))) = ((1 : ℚ) / (d : ℕ) : ℚ) := by
  rw [localBrauerInvariant_finiteInflation]
  change unramifiedContinuousInvariant K (localFiniteUnramifiedField K d d.pos) _ = _
  rw [unramifiedContinuousInvariant_uniformizer, localFiniteUnramifiedField_finrank]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem localBrauerInvariant_inflation_of_unramified_embedding
    {B N : Type u} [Field B] [Field N] [Algebra B N]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeRel N] [UniformSpace N] [IsUniformAddGroup N] [IsNonarchimedeanLocalField N]
    [FiniteDimensional B N] [IsGalois B N]
    [Valuation.HasExtension (ValuativeRel.valuation B) (ValuativeRel.valuation N)]
    [IsUnramifiedValuedExtension B N]
    (i : N →ₐ[B] SeparableClosure B) (a : continuousCohomology 2 (galoisUnitsRep B N)) :
    localBrauerInvariant B (relativeInflationOfEmbedding i a) =
      unramifiedContinuousInvariant B N a := by
  let F := i.finiteGaloisFieldRange
  let e : N ≃ₐ[B] ↥F.toIntermediateField := i.equivFieldRange
  let aNF : Algebra N (↥F.toIntermediateField) := e.toRingHom.toAlgebra
  let : Algebra N (↥F.toIntermediateField) := aNF
  let : IsScalarTower B N (↥F.toIntermediateField) :=
    IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  let : FiniteDimensional N (↥F.toIntermediateField) :=
    Module.Finite.of_surjective (Algebra.linearMap N _) e.surjective
  let : IsUnramifiedValuedExtension B F :=
    ClassFieldTower.Martinet.Shafarevich.isUnramifiedValuedExtension_of_algEquiv B F N e.symm
  let z := relativeInflation B N (↥F.toIntermediateField) a
  have hf := relativeInflationOfEmbedding_factor F i (fun _ => rfl) a
  have hF := localBrauerInvariant_finiteInflation_of_unramified B F z
  have hN := unramifiedContinuousInvariant_inflation B N F a
  exact (congrArg (localBrauerInvariant B) hf).trans (hF.trans hN)

section RestrictionNormalization

attribute [local instance] compositumStageFiniteDimensional stageSeparableClosureAlgebra
attribute [local instance] leftStageAlgebra rightStageAlgebra
attribute [local instance] leftStageScalarTower rightStageScalarTower
attribute [local instance] leftStageFiniteDimensional rightStageFiniteDimensional leftStageIsGalois
attribute [local instance] leftStageValuationHasExtension rightStageValuationHasExtension

private theorem embeddedStage_integerRingData
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] :
    IsIntegralClosure 𝒪[E] 𝒪[K] E ∧ Module.Finite 𝒪[K] 𝒪[E] :=
  ⟨localCompleteDVF_integerRing_isIntegralClosure K E,
    localCompleteDVF_integerRing_moduleFinite K E⟩

private theorem unramifiedCompositum_degree
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (m : ℕ+) (d : ℕ) (hm : d * stageResidueFinrank K E = (m : ℕ)) :
    let M := unramifiedBrauerStage K m
    let N := compositumStage K E M
    finrank K M = stageResidueFinrank K E * finrank E N := by
  intro M N
  have hM : finrank K M = (m : ℕ) := localFiniteUnramifiedField_finrank K m m.pos
  have hN : finrank E N = d := (compositum_isUnramified_and_finrank K E m d hm).2
  exact hM.trans (hm.symm.trans ((mul_comm d (stageResidueFinrank K E)).trans
    (congrArg (stageResidueFinrank K E * ·) hN.symm)))

private theorem embeddedAbsoluteBrRestriction_unramifiedStage_compositum
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (j : (SeparableClosure K) ≃ₐ[E] SeparableClosure E)
    (m : ℕ+) (x : relativeBr (unramifiedBrauerStage K m)) :
    let M := unramifiedBrauerStage K m
    let N := compositumStage K E M
    let _ : Algebra (↥M.toIntermediateField) N := rightStageAlgebra K E M
    let _ : IsScalarTower K (↥M.toIntermediateField) N := rightStageScalarTower K E M
    embeddedAbsoluteBrRestriction K E j (finiteInflation M x) =
      relativeInflationOfEmbedding (compositumClosureEmbedding K E M j)
        (relativeBaseRestriction K E N (relativeInflation K M N x)) := by
  intro M N rightAlgebra rightTower
  exact embeddedAbsoluteBrRestriction_finiteInflation K E M j (↥N)
    (compositumClosureEmbedding K E M j)
    (compositumClosureEmbedding_restriction_coincides K E M j) (fun _ => rfl) x

private theorem unramifiedInvariant_compositum_restriction
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (m : ℕ+) (d : ℕ) (hm : d * stageResidueFinrank K E = (m : ℕ))
    (x : relativeBr (unramifiedBrauerStage K m)) :
    let M := unramifiedBrauerStage K m
    let N := compositumStage K E M
    let _ : Algebra (↥M.toIntermediateField) N := rightStageAlgebra K E M
    let _ : IsScalarTower K (↥M.toIntermediateField) N := rightStageScalarTower K E M
    let _ : IsUnramifiedValuedExtension E N := (compositum_isUnramified_and_finrank K E m d hm).1
    unramifiedContinuousInvariant E N (relativeBaseRestriction K E N (relativeInflation K M N x)) =
        finrank K E • unramifiedContinuousInvariant K M x := by
  intro M N rightAlgebra rightTower unramified
  let : Valuation.HasExtension (ValuativeRel.valuation (↥M.toIntermediateField))
      (ValuativeRel.valuation N) := rightStageValuationHasExtension K E M
  let hKE := embeddedStage_integerRingData K E
  let hEN := compositum_integerRingData K E M
  let := hKE.1
  let := hKE.2
  let := hEN.1
  let := hEN.2
  let := IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[E])
  have hdegree := unramifiedCompositum_degree K E m d hm
  exact unramifiedContinuousInvariant_tower_restriction K (↥E)
    (↥M.toIntermediateField) (↥N) hdegree x

private theorem localBrauerInvariant_compositum_restriction
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (j : (SeparableClosure K) ≃ₐ[E] SeparableClosure E)
    (m : ℕ+) (d : ℕ) (hm : d * stageResidueFinrank K E = (m : ℕ))
    (x : relativeBr (unramifiedBrauerStage K m)) :
    let M := unramifiedBrauerStage K m
    let N := compositumStage K E M
    let _ : Algebra (↥M.toIntermediateField) N := rightStageAlgebra K E M
    let _ : IsScalarTower K (↥M.toIntermediateField) N := rightStageScalarTower K E M
    localBrauerInvariant E (relativeInflationOfEmbedding (compositumClosureEmbedding K E M j)
      (relativeBaseRestriction K E N (relativeInflation K M N x))) =
        finrank K E • unramifiedContinuousInvariant K M x := by
  intro M N rightAlgebra rightTower
  let : IsUnramifiedValuedExtension E N := (compositum_isUnramified_and_finrank K E m d hm).1
  let i := compositumClosureEmbedding K E M j
  let a := relativeBaseRestriction K E N (relativeInflation K M N x)
  have hInflation := localBrauerInvariant_inflation_of_unramified_embedding i a
  have hRestriction := unramifiedInvariant_compositum_restriction K E m d hm x
  exact hInflation.trans hRestriction

private theorem localBrauerInvariant_embeddedRestriction_unramifiedStage
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (j : (SeparableClosure K) ≃ₐ[E] SeparableClosure E)
    (m : ℕ+) (d : ℕ) (hm : d * stageResidueFinrank K E = (m : ℕ))
    (x : relativeBr (unramifiedBrauerStage K m)) :
    localBrauerInvariant E (embeddedAbsoluteBrRestriction K E j
      (finiteInflation (unramifiedBrauerStage K m) x)) =
        finrank K E • localBrauerInvariant K (finiteInflation (unramifiedBrauerStage K m) x) := by
  have hsquare := embeddedAbsoluteBrRestriction_unramifiedStage_compositum K E j m x
  have hrestriction := localBrauerInvariant_compositum_restriction K E j m d hm x
  have hfinite := localBrauerInvariant_finiteInflation K m x
  exact (congrArg (localBrauerInvariant E) hsquare).trans
    (hrestriction.trans (congrArg (finrank K E • ·) hfinite.symm))

/-- The actual restriction along a chosen comparison of separable closures
for an embedded finite separable extension multiplies the arithmetic invariant
by the finite field degree. -/
theorem localBrauerInvariant_embeddedRestriction
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (j : (SeparableClosure K) ≃ₐ[E] SeparableClosure E) (x : Br K) :
    localBrauerInvariant E (embeddedAbsoluteBrRestriction K E j x) =
      finrank K E • localBrauerInvariant K x := by
  have hx : x ∈ unramifiedBr K := (unramifiedBr_eq_top K).symm ▸ AddSubgroup.mem_top x
  obtain ⟨d, y, hy⟩ := (mem_unramifiedBr_iff K x).mp hx
  let U := unramifiedBrauerStage K d
  have hU : (d : ℕ) • localBrauerInvariant K x = 0 := by
    rw [← hy, localBrauerInvariant_finiteInflation]
    have h := (mem_range_unramifiedContinuousInvariant_iff K U _).mp ⟨y, rfl⟩
    rw [localFiniteUnramifiedField_finrank K d d.pos] at h
    exact h
  let f := stageResidueFinrank K E
  let m : ℕ+ := ⟨(d : ℕ) * f, Nat.mul_pos d.pos (stageResidueFinrank_pos K E)⟩
  let M := unramifiedBrauerStage K m
  have hm : finrank K M • localBrauerInvariant K x = 0 := by
    rw [localFiniteUnramifiedField_finrank K m m.pos]
    change ((d : ℕ) * f) • localBrauerInvariant K x = 0
    calc
      ((d : ℕ) * f) • localBrauerInvariant K x =
          f • ((d : ℕ) • localBrauerInvariant K x) :=
        (congrArg (fun s : ℕ => s • localBrauerInvariant K x) (Nat.mul_comm _ _)).trans
          (mul_smul f (d : ℕ) (localBrauerInvariant K x))
      _ = 0 := (congrArg (f • ·) hU).trans (nsmul_zero f)
  obtain ⟨y', hy'⟩ := (mem_range_unramifiedContinuousInvariant_iff K M _).mpr hm
  have hM : finiteInflation M y' = x := (localBrauerInvariantEquiv K).injective
    ((localBrauerInvariant_finiteInflation K m y').trans hy')
  have h := localBrauerInvariant_embeddedRestriction_unramifiedStage K E j m (d : ℕ) rfl y'
  exact (congrArg (fun b : Br K => localBrauerInvariant E
      (embeddedAbsoluteBrRestriction K E j b)) hM).symm.trans
    (h.trans (congrArg (fun b : Br K => finrank K E • localBrauerInvariant K b) hM))

/-- On a finite embedded separable extension, the restriction kernel is exactly
the classes whose invariant is killed by the extension degree. -/
theorem embeddedAbsoluteBrRestriction_eq_zero_iff
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (j : (SeparableClosure K) ≃ₐ[E] SeparableClosure E) (x : Br K) :
    embeddedAbsoluteBrRestriction K E j x = 0 ↔ finrank K E • localBrauerInvariant K x = 0 := by
  rw [← localBrauerInvariant_embeddedRestriction]
  exact ⟨fun h => h ▸ map_zero _,
    fun h => (localBrauerInvariantEquiv E).injective (h.trans (map_zero _).symm)⟩

end RestrictionNormalization

end ClassFieldTheory.Brauer
