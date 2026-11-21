/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicRestriction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.IdeleGluing
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.InvariantSum
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicReciprocity

/-! # Finite-place localization of a cyclic carry and its arithmetic Artin value -/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField AlgebraicNumberTheory.Valuations HilbertRamification
open ClassFieldTower.Cohomology GlobalClassFieldTheory.Reciprocity
open LocalClassFieldTheory LocalFieldTheory
open scoped IsMulCommutative NumberField ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

private theorem autCongr_symm_action {F M N : Type u}
    [Field F] [Field M] [Field N] [Algebra F M] [Algebra F N]
    (c : M ≃ₐ[F] N) (σ : Gal(N/F)) (x : M) :
    c ((AlgEquiv.autCongr c.symm) σ x) = σ (c x) :=
  c.apply_symm_apply _

private theorem chosenFinitePlaceArtin_apply_local
    {K L : Type u} [Field K] [NumberField K] [Field L] [Algebra K L]
    [hKL : FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := L) v
    let F := vK.Completion
    let M := LocalizedCompletion vK w
    let : Algebra F M := finitePlaceLocalArtinLocalizedAlgebra v w
    let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField F :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let : FiniteDimensional F M := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois F M := finitePlaceLocalArtinIsAbelianGalois v w hKL
    chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v x =
      finitePlaceLocalToGlobalMonoidHom (K := K) (L := L) v w
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom F M
          (finitePlaceLocalArtinInput v x)) := by
  let w := chosenFinitePlaceExtension (L := L) v
  have hvalue :=
    finitePlaceLocalArtinMonoidHom_apply_normalized_universe (K := K) (L := L) v w x
  exact congrArg (finitePlaceLocalToGlobalMonoidHom (K := K) (L := L) v w) hvalue

private theorem arithmeticChosenFinitePlaceArtin_apply_local
    {K L : Type u} [Field K] [NumberField K] [Field L] [Algebra K L]
    [hKL : FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := L) v
    let F := vK.Completion
    let M := LocalizedCompletion vK w
    let : Algebra F M := finitePlaceLocalArtinLocalizedAlgebra v w
    let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField F :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let : FiniteDimensional F M := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois F M := finitePlaceLocalArtinIsAbelianGalois v w hKL
    arithmeticChosenFinitePlaceArtinMonoidHom K L v x =
      (finitePlaceLocalToGlobalMonoidHom (K := K) (L := L) v w
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom F M
          (finitePlaceLocalArtinInput v x)))⁻¹ :=
  (arithmeticChosenFinitePlaceArtinMonoidHom_apply K L v x).trans
    (congrArg (fun σ : Gal(L/K) => σ⁻¹) (chosenFinitePlaceArtin_apply_local v x))

private theorem inverse_localArtin_conjugate
    {F M N : Type u} [Field F] [Field M] [Field N] [Algebra F M] [Algebra F N]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [FiniteDimensional F M] [FiniteDimensional F N] [IsAbelianGalois F M] [IsAbelianGalois F N]
    {G : Type u} [Group G] (f : Gal(M/F) →* G) (c : M ≃ₐ[F] N) (a : Fˣ) :
    (f (LocalClassFieldTheory.abelianLocalArtinMonoidHom F M a))⁻¹ =
      (f.comp (AlgEquiv.autCongr c.symm).toMonoidHom)
        ((LocalClassFieldTheory.abelianLocalArtinMap F N a)⁻¹) := by
  let s := AlgEquiv.autCongr c.symm
  let σ : Gal(N/F) := LocalClassFieldTheory.abelianLocalArtinMap F N a
  have hσ : σ = LocalClassFieldTheory.abelianLocalArtinMonoidHom F N a :=
    DFunLike.congr_fun (LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom F N) a
  have hM : s σ = LocalClassFieldTheory.abelianLocalArtinMonoidHom F M a :=
    (congrArg s hσ).trans (DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_autCongr F N M c.symm) a)
  exact (congrArg (fun τ : Gal(M/F) => (f τ)⁻¹) hM.symm).trans
    (map_inv (f.comp s.toMonoidHom) σ).symm

private theorem arithmeticChosenFinitePlaceArtin_apply_conjugate
    {K L : Type u} [Field K] [NumberField K] [Field L] [Algebra K L]
    [hKL : FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := L) v
    let F := vK.Completion
    let M := LocalizedCompletion vK w
    let : Algebra F M := finitePlaceLocalArtinLocalizedAlgebra v w
    let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField F :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let : FiniteDimensional F M := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois F M := finitePlaceLocalArtinIsAbelianGalois v w hKL
    ∀ (N : Type u) [Field N] [Algebra F N] [FiniteDimensional F N] [IsAbelianGalois F N]
      (c : M ≃ₐ[F] N),
      arithmeticChosenFinitePlaceArtinMonoidHom K L v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a) =
        ((finitePlaceLocalToGlobalMonoidHom (K := K) (L := L) v w).comp
          (AlgEquiv.autCongr c.symm).toMonoidHom)
            ((LocalClassFieldTheory.abelianLocalArtinMap F N
              (Units.map (algebraMap K F).toMonoidHom a))⁻¹) := by
  intro vK w F M algM valF localF finM abM N fieldN algN finN abN c
  let x := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a
  let aF := Units.map (algebraMap K F).toMonoidHom a
  let f := finitePlaceLocalToGlobalMonoidHom (K := K) (L := L) v w
  have ha : finitePlaceLocalArtinInput v x = aF := by
    apply Units.ext
    exact (finitePlaceCompletionAlgEquiv v).symm.commutes (a : K)
  have hlocal := arithmeticChosenFinitePlaceArtin_apply_local (K := K) (L := L) v x
  have hinput := congrArg (fun y : Fˣ =>
    (f (LocalClassFieldTheory.abelianLocalArtinMonoidHom F M y))⁻¹) ha
  have hconjugate := inverse_localArtin_conjugate f c aF
  dsimp (config := { instances := true, zetaDelta := true }) only
    [vK, w, F, M, algM, valF, localF, finM, abM, x, aF, f] at hinput hconjugate ⊢
  exact hlocal.trans (hinput.trans hconjugate)


private theorem embeddedGaloisRestriction_comp_of_localization
    {K F M N : Type u} [Field K] [Field F] [Field M] [Field N]
    [Algebra K F] [Algebra K M] [Algebra K N] [Algebra F M] [Algebra F N]
    [IsScalarTower K F M] [IsScalarTower K F N]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (j₀ : E →ₐ[K] M) (c : M ≃ₐ[F] N)
    (D : Subgroup Gal(E/K)) (eD : D ≃* Gal(M/F))
    (hD : ∀ (δ : D) (x : E),
      eD δ (j₀ x) = j₀ ((δ : Gal(E/K)) x))
    (σ : Gal(N/F)) :
    let j := (c.toAlgHom.restrictScalars K).comp j₀
    embeddedGaloisRestriction (B := F) j σ =
      D.subtype (eD.symm ((AlgEquiv.autCongr c.symm) σ)) := by
  intro j
  apply AlgEquiv.ext
  intro x
  apply j.injective
  change j (embeddedGaloisRestriction (B := F) j σ x) =
    j ((eD.symm ((AlgEquiv.autCongr c.symm) σ) : Gal(E/K)) x)
  rw [embeddedGaloisRestriction_commutes (B := F) j]
  let τ := (AlgEquiv.autCongr c.symm) σ
  let δ := eD.symm τ
  have hδ : eD δ = τ := eD.apply_symm_apply τ
  change σ (c (j₀ x)) = c (j₀ ((δ : Gal(E/K)) x))
  calc
    _ = c (τ (j₀ x)) := (autCongr_symm_action c σ (j₀ x)).symm
    _ = c (eD δ (j₀ x)) := congrArg (fun t : Gal(M/F) => c (t (j₀ x))) hδ.symm
    _ = _ := congrArg c (hD δ x)

private theorem localInvariant_of_embedded_cyclic_carry
    {K F : Type u} [Field K] [NumberField K] [Field F] [Algebra K F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (N : FiniteGaloisIntermediateField F (SeparableClosure F))
    [Algebra K N] [IsScalarTower K F N]
    [IsCyclic Gal(E/K)] [IsAbelianGalois F N]
    (j : E →ₐ[K] N) (f : Gal(N/F) →* Gal(E/K)) (hf : Function.Injective f)
    (hres : ∀ σ : Gal(N/F), embeddedGaloisRestriction (B := F) j σ = f σ)
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    localBrauerInvariant F (restrict (algebraMap K F) (cyclicBrauerClass E g hg a)) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul
        (f ((LocalClassFieldTheory.abelianLocalArtinMap F N
          (Units.map (algebraMap K F).toMonoidHom a))⁻¹))) := by
  let : CommGroup Gal(E/K) := IsCyclic.commGroup
  let : IsCyclic Gal(N/F) := isCyclic_of_injective f hf
  obtain ⟨h, hh, hgen, hcard⟩ := finiteCyclic_exists_generator_map_index g hg f hf
  let d := f.range.index
  have hd : 0 < d := Nat.pos_of_ne_zero f.range.index_ne_zero_of_finite
  let aF := Units.map (algebraMap K F).toMonoidHom a
  let σ := (LocalClassFieldTheory.abelianLocalArtinMap F N aF)⁻¹
  have hcarry := restrict_cyclicBrauerClass_eq_cyclicBrauerClass
    E N j g hg h hh d hd hcard ((hres h).trans hgen) a
  exact (congrArg (localBrauerInvariant F) hcarry).trans
    ((localBrauerInvariant_cyclicBrauerClass_eq_artin F N h hh aF).trans
      (finiteCyclicArithmeticCharacter_map_of_generator_power g hg h hh f d hd hcard hgen σ).symm)

private theorem finitePlaceBrauerInvariant_globalRestriction
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : Br K) :
    let F := (HeightOneSpectrum.adicAbv K v).Completion
    let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField F :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    placeBrauerInvariant K (Sum.inl v) (finitePlaceRestriction K v x) =
      localBrauerInvariant F (restrict (algebraMap K F) x) := by
  intro F valuationOwner localOwner
  let A := v.adicCompletion K
  let e : A ≃ₐ[K] F := (finitePlaceCompletionAlgEquiv v).symm
  let a : K →+* A := algebraMap K A
  let b : K →+* F := algebraMap K F
  have he : e.toRingHom.comp a = b := RingHom.ext e.commutes
  have hm := (restrict_comp a e.toRingHom).trans (congrArg restrict he)
  have hx : restrictEquiv e.toRingEquiv (finitePlaceRestriction K v x) = restrict b x :=
    DFunLike.congr_fun hm x
  change finitePlaceBrauerInvariantEquiv K v (finitePlaceRestriction K v x) = _
  have h := (finitePlaceBrauerInvariantEquiv_apply K v (finitePlaceRestriction K v x)).trans
    (congrArg (finitePlaceNormalizedBrauerInvariantEquiv K v) hx)
  exact h

private theorem exists_arithmeticArtin_of_decomposition_mem
    {K L : Type u} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(L/K))
    (hσ : σ ∈ finitePlaceDecompositionGroup (K := K) (L := L) v) :
    ∃ b : (v.adicCompletion K)ˣ, arithmeticChosenFinitePlaceArtinMonoidHom K L v b = σ := by
  have hi : σ⁻¹ ∈ finitePlaceDecompositionGroup (K := K) (L := L) v :=
    Subgroup.inv_mem _ hσ
  have hr : σ⁻¹ ∈ (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v).range :=
    (chosenFinitePlaceArtinMonoidHom_range (K := K) (L := L) v).symm ▸ hi
  obtain ⟨b, hb⟩ := hr
  exact ⟨b, (arithmeticChosenFinitePlaceArtinMonoidHom_apply K L v b).trans
    ((congrArg Inv.inv hb).trans (inv_inv σ))⟩

private theorem exists_finiteCyclicCharacter_value_of_subgroup
    {G H U : Type u} [CommGroup G] [Group H] [Fintype G] [Finite H]
    (g : G) (hg : ∀ σ : G, σ ∈ Subgroup.zpowers g)
    (f : H →* G) (hf : Function.Injective f) (artin : U → G)
    (hArtin : ∀ σ : H, ∃ b : U, artin b = f σ)
    (z : AddCircle (1 : ℚ)) (hz : Nat.card H • z = 0) :
    ∃ b : U, finiteCyclicArithmeticCharacter g hg (Additive.ofMul (artin b)) = z := by
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨h, hh, hgen, hcard⟩ := finiteCyclic_exists_generator_map_index g hg f hf
  let d := f.range.index
  have hd : 0 < d := Nat.pos_of_ne_zero f.range.index_ne_zero_of_finite
  obtain ⟨σ, hσ⟩ := (mem_range_finiteCyclicArithmeticCharacter_iff h hh z).2 hz
  obtain ⟨b, hb⟩ := hArtin σ.toMul
  refine ⟨b, ?_⟩
  exact (congrArg (fun τ : G => finiteCyclicArithmeticCharacter g hg (Additive.ofMul τ)) hb).trans
    ((finiteCyclicArithmeticCharacter_map_of_generator_power
      g hg h hh f d hd hcard hgen σ.toMul).trans hσ)

variable (K : Type u) [Field K] [NumberField K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [IsCyclic Gal(E/K)] [IsAbelianGalois K E]
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g)

private theorem placeBrauerInvariant_finite_cyclicBrauerClass_of_closureComparison
    (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := E) v
    let F := vK.Completion
    let M := LocalizedCompletion vK w
    let : Algebra F M := finitePlaceLocalArtinLocalizedAlgebra v w
    ∀ (N : FiniteGaloisIntermediateField F (SeparableClosure F)),
      let : Algebra F N := finiteGaloisStageAlgebra N
      (M ≃ₐ[F] N) →
    placeBrauerInvariant K (Sum.inl v) (finitePlaceRestriction K v (cyclicBrauerClass E g hg a)) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul
        (arithmeticChosenFinitePlaceArtinMonoidHom K E v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a))) := by
  intro vK w F M localAlgebra N stageAlgebra c
  let hvK := RayClass.adicAbv_isNontrivial v
  let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField F := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : Algebra K M := localizedCompletionGlobalAlgebra vK w
  let : IsScalarTower K F M := localizedCompletionIsScalarTower vK w
  let : Algebra K N := ((algebraMap F N).comp (algebraMap K F)).toAlgebra
  let : IsScalarTower K F N := IsScalarTower.of_algebraMap_eq' rfl
  let j₀ : E →ₐ[K] M := localizedCompletionToAlgHom vK w
  let j : E →ₐ[K] N := (c.toAlgHom.restrictScalars K).comp j₀
  let D := absoluteValueDecompositionGroup K w.1
  let eD : D ≃* Gal(M/F) := decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let toGlobal := finitePlaceLocalToGlobalMonoidHom (K := K) (L := ↥E.toIntermediateField) v w
  let f := toGlobal.comp (AlgEquiv.autCongr c.symm).toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp
    (eD.symm.injective.comp (AlgEquiv.autCongr c.symm).injective)
  have hres := embeddedGaloisRestriction_comp_of_localization E j₀ c D eD
    (localizationRamificationGroups_decompositionGroupEquiv_toLocalization vK hvK w)
  let : IsCyclic Gal(N/F) := isCyclic_of_injective f hf
  let : IsAbelianGalois F N := IsAbelianGalois.of_isCyclic F N
  have hArtin := arithmeticChosenFinitePlaceArtin_apply_conjugate
    (K := K) (L := ↥E.toIntermediateField) v a N c
  have hInv := localInvariant_of_embedded_cyclic_carry (K := K) (F := F)
    E N j f hf hres g hg a
  have hv := finitePlaceBrauerInvariant_globalRestriction v (cyclicBrauerClass E g hg a)
  rw [hv, hArtin]
  dsimp (config := { instances := true, zetaDelta := true }) only [F, vK, f, toGlobal] at hInv ⊢
  with_reducible exact hInv

/-- The canonical arithmetic invariant of a localized cyclic carry is the
cyclic character of the actual one-place arithmetic reciprocity symbol. -/
theorem placeBrauerInvariant_finite_cyclicBrauerClass (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    placeBrauerInvariant K (Sum.inl v) (finitePlaceRestriction K v (cyclicBrauerClass E g hg a)) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul
        (arithmeticChosenFinitePlaceArtinMonoidHom K E v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a))) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := E) v
  let F := vK.Completion
  let M := LocalizedCompletion vK w
  let : Algebra F M := finitePlaceLocalArtinLocalizedAlgebra v w
  let := finitePlaceLocalArtinFiniteDimensional v w
  let hM : IsAbelianGalois F M := finitePlaceLocalArtinIsAbelianGalois v w inferInstance
  let : Algebra.IsSeparable F M := hM.toIsGalois.to_isSeparable
  let i : M →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let N := i.finiteGaloisFieldRange
  let : Algebra F N := finiteGaloisStageAlgebra N
  let c : M ≃ₐ[F] N := i.equivFieldRange
  exact placeBrauerInvariant_finite_cyclicBrauerClass_of_closureComparison
    K E g hg v a N c

/-- At a finite place every invariant killed by the chosen local degree is
the cyclic character of an actual one-place Artin value. -/
theorem exists_placeUnitArtin_finite_invariant (v : HeightOneSpectrum (𝓞 K))
    (x : Br (v.adicCompletion K))
    (hx : addOrderOf x ∣ Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) v)
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v)) :
    ∃ b : (v.adicCompletion K)ˣ,
      finiteCyclicArithmeticCharacter g hg
          (Additive.ofMul (arithmeticChosenFinitePlaceArtinMonoidHom K E v b)) =
        placeBrauerInvariant K (Sum.inl v) x := by
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK := RayClass.adicAbv_isNontrivial v
  let w := chosenFinitePlaceExtension (L := E) v
  let F := vK.Completion
  let M := LocalizedCompletion vK w
  let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField F := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : Algebra F M := finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional F M := finitePlaceLocalArtinFiniteDimensional v w
  let : IsAbelianGalois F M := finitePlaceLocalArtinIsAbelianGalois v w inferInstance
  let D := absoluteValueDecompositionGroup K w.1
  let eD : D ≃* Gal(M/F) := decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let f : Gal(M/F) →* Gal(E/K) :=
    finitePlaceLocalToGlobalMonoidHom (K := K) (L := ↥E.toIntermediateField) v w
  have hf : Function.Injective f := Subtype.val_injective.comp eD.symm.injective
  let : CommGroup Gal(E/K) := IsCyclic.commGroup
  let z := placeBrauerInvariant K (Sum.inl v) x
  have hz : Nat.card Gal(M/F) • z = 0 := by
    rw [IsGalois.card_aut_eq_finrank F M]
    change Module.finrank F M • placeBrauerInvariant K (Sum.inl v) x = 0
    have hx' : addOrderOf x ∣ Module.finrank F M := hx
    rw [← map_nsmul, (addOrderOf_dvd_iff_nsmul_eq_zero.mp hx'), map_zero]
  have hLift (σ : Gal(M/F)) : ∃ b : (v.adicCompletion K)ˣ,
      arithmeticChosenFinitePlaceArtinMonoidHom K E v b = f σ := by
    apply exists_arithmeticArtin_of_decomposition_mem
    exact (eD.symm σ).property
  exact exists_finiteCyclicCharacter_value_of_subgroup
    g hg f hf (arithmeticChosenFinitePlaceArtinMonoidHom K E v) hLift z hz

end ClassFieldTheory.Brauer
