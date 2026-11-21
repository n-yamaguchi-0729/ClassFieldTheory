/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteBaseChange
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
public import Nyll.GaloisCohomology.ProP.MultiplicativeInducedShapiro
public import Nyll.GaloisCohomology.Topology.DiscreteGroupH2
public import Nyll.GaloisCohomology.Topology.DiscreteOriginalH2

/-! # Actual Shapiro evaluation on a completed tensor block -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicNumberTheory.Valuations HilbertRamification
open LocalClassFieldTheory ClassFieldTower.Cohomology CyclicCohomology ContinuousCohomology
open scoped TensorProduct

namespace ClassFieldTheory.Brauer

section TensorDiagonal

variable {K L : Type} [Field K] [Field L] [Algebra K L]
    (F : Type) [Field F] [Algebra K F]

local instance : MulDistribMulAction Gal(L/K) (F ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := F)

/-- The tensor-coordinate diagonal uses the original inclusion of the extension field. -/
def tensorDiagonalRepHom : Rep.ofAlgebraAutOnUnits K L ⟶
    Rep.ofMulDistribMulAction Gal(L/K) (F ⊗[K] L)ˣ := by
  let ι := Units.map (Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L).toMonoidHom
  exact Rep.ofHom ⟨ι.toAdditive.toIntLinearMap, fun g => by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    exact (scalarTensorConjugation_tmul (K := K) (L := L) (A := F) g 1 (x.toMul : L)).symm⟩

variable {F} {F' : Type} [Field F'] [Algebra K F']

/-- An equivalence of the completed base acts on the first tensor factor
and commutes with the original Galois action on the second factor. -/
def tensorUnitsRepBaseAlgEquiv (e : F ≃ₐ[K] F') :
    Rep.ofMulDistribMulAction Gal(L/K) (F ⊗[K] L)ˣ ≅
      Rep.ofMulDistribMulAction Gal(L/K) (F' ⊗[K] L)ˣ := by
  let t := Algebra.TensorProduct.congr e (AlgEquiv.refl : L ≃ₐ[K] L)
  let X := Rep.ofMulDistribMulAction Gal(L/K) (F ⊗[K] L)ˣ
  let Y := Rep.ofMulDistribMulAction Gal(L/K) (F' ⊗[K] L)ˣ
  let : Module ℤ (Additive (F ⊗[K] L)ˣ) := X.hV2
  let : Module ℤ (Additive (F' ⊗[K] L)ˣ) := Y.hV2
  let c : X ≃ₗ[ℤ] Y := (Units.mapEquiv t.toMulEquiv).toAdditive.toIntLinearEquiv
  refine Rep.mkIso (Representation.Equiv.mk c ?_)
  intro g
  apply LinearMap.ext
  intro a
  apply Additive.toMul.injective
  apply Units.ext
  change t (scalarTensorConjugation (K := K) (L := L) (A := F) g (a.toMul : F ⊗[K] L)) =
    scalarTensorConjugation (K := K) (L := L) (A := F') g (t (a.toMul : F ⊗[K] L))
  induction (a.toMul : F ⊗[K] L) using TensorProduct.inductionOn with
  | tmul b y => rfl
  | add y z hy hz => simp only [map_add, hy, hz]

/-- The base transport takes the original tensor diagonal to the original
tensor diagonal, including on actual degree-two classes. -/
theorem tensorUnitsH2BaseAlgEquiv_diagonal (e : F ≃ₐ[K] F')
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ((groupCohomology.functor ℤ (Gal(L/K)) 2).mapIso (tensorUnitsRepBaseAlgEquiv (L := L) e)).hom
        (groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom F) 2 x) =
      groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom F') 2 x := by
  let iso := tensorUnitsRepBaseAlgEquiv (L := L) e
  have hdiag : tensorDiagonalRepHom (K := K) (L := L) F ≫ iso.hom = tensorDiagonalRepHom F' := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    apply Additive.toMul.injective
    apply Units.ext
    let u : Lˣ := (show Additive Lˣ from a).toMul
    change e (1 : F) ⊗ₜ[K] (u : L) = (1 : F') ⊗ₜ[K] (u : L)
    rw [map_one]
  change (groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom F) 2 ≫
    groupCohomology.map (MonoidHom.id (Gal(L/K))) iso.hom 2) x = _
  rw [← groupCohomology.map_id_comp, hdiag]

/-- Changing the completed base preserves vanishing of a diagonal tensor class. -/
theorem tensorDiagonalH2_eq_zero_iff_of_baseAlgEquiv (e : F ≃ₐ[K] F')
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom F) 2 x = 0 ↔
      groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom F') 2 x = 0 := by
  let I := (groupCohomology.functor ℤ (Gal(L/K)) 2).mapIso (tensorUnitsRepBaseAlgEquiv (L := L) e)
  let f := I.toLinearEquiv
  let a := groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom F) 2 x
  let b := groupCohomology.map (MonoidHom.id (Gal(L/K))) (tensorDiagonalRepHom F') 2 x
  have hmap : f a = b := tensorUnitsH2BaseAlgEquiv_diagonal e x
  exact ⟨fun h => hmap.symm.trans ((congrArg f h).trans (map_zero f)),
    fun h => f.injective (hmap.trans (h.trans (map_zero f).symm))⟩

end TensorDiagonal

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) (w : AbsoluteValueExtension vK L)

local notation "Decomp" => absoluteValueDecompositionGroup K (Subtype.val w)
local notation "M" => LocalizedCompletion vK w
local notation "T" => LocalTensorAlgebra (L := L) vK
local notation "Kᵥ" => AbsoluteValue.Completion vK

local instance : MulDistribMulAction Gal(L/K) Tˣ := localTensorUnitsAction vK

local instance : Algebra Kᵥ M := localizedCompletionBaseAlgebra vK w

/-- The original decomposition action on the chosen completed field's units. -/
abbrev tensorDecompositionRep : Rep ℤ Decomp :=
  letI := decompositionGroupLocalUnitsAction vK hvK w
  Rep.ofMulDistribMulAction Decomp Mˣ

/-- The representation on the induced block of completed unit groups. -/
abbrev tensorInducedRep : Rep ℤ (Gal(L/K)) :=
  letI := decompositionGroupLocalUnitsAction vK hvK w
  Rep.ofMulDistribMulAction Gal(L/K) (LocalPlaceBlock vK hvK w)

/-- Evaluation at the chosen place on the induced representation. -/
abbrev tensorInducedEvaluation :
    Rep.res (Decomp).subtype (tensorInducedRep vK hvK w) ⟶ tensorDecompositionRep vK hvK w :=
  letI := decompositionGroupLocalUnitsAction vK hvK w
  multiplicativeInducedEvaluation Decomp Mˣ

/-- Shapiro's isomorphism with the chosen decomposition action fixed. -/
abbrev tensorInducedShapiro (n : ℕ) :
    groupCohomology (tensorInducedRep vK hvK w) n ≅
      groupCohomology (tensorDecompositionRep vK hvK w) n :=
  letI := decompositionGroupLocalUnitsAction vK hvK w
  multiplicativeInducedCohomologyIso Decomp Mˣ n

/-- The actual tensor units form the multiplicatively induced decomposition representation. -/
def tensorRepIsoInduced :
    Rep.ofMulDistribMulAction Gal(L/K) Tˣ ≅
      tensorInducedRep vK hvK w := by
  letI := decompositionGroupLocalUnitsAction vK hvK w
  let X := Rep.ofMulDistribMulAction Gal(L/K) Tˣ
  let Y := tensorInducedRep vK hvK w
  let e : Tˣ ≃* LocalPlaceBlock vK hvK w := localTensorUnitsEquivLocalPlaceBlock vK hvK w
  let c : X ≃ₗ[ℤ] Y := e.toAdditive.toIntLinearEquiv
  refine Rep.mkIso (Representation.Equiv.mk c ?_)
  intro g
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  let b : Tˣ := (show Additive Tˣ from x).toMul
  change e (g • b) = g • e b
  exact localTensorUnitsEquivLocalPlaceBlock_smul vK hvK w g b

/-- The original restriction onto the decomposition group followed by
evaluation at the chosen field. -/
def localTensorEvaluationRepHom :
    Rep.res (Decomp).subtype (Rep.ofMulDistribMulAction Gal(L/K) Tˣ) ⟶
      tensorDecompositionRep vK hvK w :=
  (Rep.resFunctor (Decomp).subtype).map (tensorRepIsoInduced vK hvK w).hom ≫
    tensorInducedEvaluation vK hvK w

/-- This coefficient morphism is the actual evaluation of local tensor units. -/
theorem localTensorEvaluationRepHom_apply (x : Additive Tˣ) :
    localTensorEvaluationRepHom vK hvK w x =
      Additive.ofMul (Units.map (localTensorEvaluation vK hvK w).toMonoidHom x.toMul) := by
  let := decompositionGroupLocalUnitsAction vK hvK w
  let f := localTensorUnitsEquivLocalPlaceBlock vK hvK w x.toMul
  let orbit := localTensorOrbitHom vK hvK w x.toMul
  have h₁ : (show Additive Mˣ from localTensorEvaluationRepHom vK hvK w x) =
      Additive.ofMul (f.val 1) :=
    multiplicativeInducedEvaluation_apply Decomp Mˣ (Additive.ofMul f)
  have h₂ : Additive.ofMul (f.val 1) = Additive.ofMul (orbit.val 1) :=
    congrArg (fun a : LocalPlaceBlock vK hvK w => Additive.ofMul (a.val 1))
      (localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply vK hvK w x.toMul)
  have h₃ : Additive.ofMul (orbit.val 1) =
      Additive.ofMul (Units.map (localTensorEvaluation vK hvK w).toMonoidHom x.toMul) := by
    apply Additive.ofMul.injective
    apply Units.ext
    change localTensorEvaluation vK hvK w
      (localTensorConjugation vK (1 : Gal(L/K)) (x.toMul : T)) = _
    exact congrArg (fun t : T => localTensorEvaluation vK hvK w t)
      (localTensorConjugation_one vK (x.toMul : T))
  exact h₁.trans (h₂.trans h₃)

/-- The original tensor block has the cohomology of the chosen decomposition group. -/
def localTensorShapiro (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Tˣ) n ≅
      groupCohomology (tensorDecompositionRep vK hvK w) n :=
  (groupCohomology.functor ℤ (Gal(L/K)) n).mapIso (tensorRepIsoInduced vK hvK w) ≪≫
    tensorInducedShapiro vK hvK w n

private theorem inducedShapiroCompRepIso {G : Type} [Group G] (D : Subgroup G)
    (B : Type) [CommGroup B] [MulDistribMulAction D B] {A : Rep ℤ G}
    (e : A ≅ Rep.ofMulDistribMulAction G (InducedModule (B := B) D)) (n : ℕ) :
    ((groupCohomology.functor ℤ G n).mapIso e ≪≫ (multiplicativeInducedCohomologyIso D B n)).hom =
      groupCohomology.map D.subtype
        ((Rep.resFunctor D.subtype).map e.hom ≫ multiplicativeInducedEvaluation D B) n := by
  change (groupCohomology.functor ℤ G n).map e.hom ≫
    (multiplicativeInducedCohomologyIso D B n).hom = _
  rw [groupCohomology.functor_map, multiplicativeInducedCohomologyIso_hom_eq_map]
  exact (groupCohomology.map_comp (MonoidHom.id G) D.subtype e.hom
    (multiplicativeInducedEvaluation D B) n).symm

/-- On actual cochains the Shapiro map is exactly restriction and tensor evaluation. -/
theorem localTensorShapiro_hom_eq_map (n : ℕ) :
    (localTensorShapiro vK hvK w n).hom =
      groupCohomology.map (Decomp).subtype (localTensorEvaluationRepHom vK hvK w) n := by
  let := decompositionGroupLocalUnitsAction vK hvK w
  exact inducedShapiroCompRepIso Decomp Mˣ (tensorRepIsoInduced vK hvK w) n

/-- The local tensor coordinate of the original diagonal field-unit map. -/
def localTensorDiagonalRepHom : Rep.ofAlgebraAutOnUnits K L ⟶
    Rep.ofMulDistribMulAction Gal(L/K) Tˣ :=
  tensorDiagonalRepHom Kᵥ

/-- Restriction to the actual localized finite field before absolute inflation. -/
def localizedFieldRelativeRestriction :
    continuousCohomology 2 (galoisUnitsRep K L) →+
      continuousCohomology 2 (galoisUnitsRep Kᵥ M) := by
  let : Algebra K M := localizedCompletionGlobalAlgebra vK w
  have : IsScalarTower K Kᵥ M := localizedCompletionIsScalarTower vK w
  let j := localizedCompletionToAlgHom vK w
  let r := embeddedGaloisRestriction (B := Kᵥ) j
  let φ := galoisUnitsMap r j.toRingHom (embeddedGaloisRestriction_commutes (B := Kᵥ) j)
  exact (ContinuousCohomology.map r φ 2).hom.toLinearMap.toAddMonoidHom

/-- The tensor block cohomology identifies with the actual continuous
relative field-unit cohomology of the chosen completed extension. -/
def localTensorRelativeH2Equiv :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Tˣ) 2 ≃+
      continuousCohomology 2 (galoisUnitsRep Kᵥ M) := by
  let : FiniteDimensional Kᵥ M := localizedCompletionFiniteDimensional vK hvK w
  let e := decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let eM := groupCohomology.mapIso
    (A := Rep.ofAlgebraAutOnUnits Kᵥ M) (B := tensorDecompositionRep vK hvK w)
    e (LinearEquiv.refl ℤ (Additive Mˣ)) (fun _ => rfl) 2
  exact ((localTensorShapiro vK hvK w 2 ≪≫ eM).toLinearEquiv.toAddEquiv).trans
    (discreteOriginalH2Equiv (galoisUnitsRep Kᵥ M)).symm

private theorem h2π_iterated_map {G D H : Type} [Group G] [Group D] [Group H]
    {A B : Rep ℤ G} {C : Rep ℤ D} {E : Rep ℤ H}
    (r : D →* G) (q : H →* D) (f : A ⟶ B) (g : Rep.res r B ⟶ C)
    (k : Rep.res q C ⟶ E) (c : groupCohomology.cocycles₂ A) :
    groupCohomology.map q k 2 (groupCohomology.map r g 2
        (groupCohomology.map (MonoidHom.id G) f 2 (groupCohomology.H2π A c))) =
      groupCohomology.H2π E
        (groupCohomology.mapCocycles₂ q k (groupCohomology.mapCocycles₂ r g
          (groupCohomology.mapCocycles₂ (MonoidHom.id G) f c))) := by
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply,
    groupCohomology.H2π_comp_map_apply]

/-- Shapiro carries the actual tensor diagonal to restriction to the chosen
completed field on the original cohomology classes. -/
theorem localTensorRelativeH2Equiv_diagonal
    (z : cocycles (galoisUnitsRep K L) 2) :
    localTensorRelativeH2Equiv vK hvK w (
    groupCohomology.map (MonoidHom.id (Gal(L/K))) (localTensorDiagonalRepHom vK) 2
      (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (dehomogenizeTwoOriginal (galoisUnitsRep K L) z))) =
      localizedFieldRelativeRestriction vK w (π (galoisUnitsRep K L) 2 z) := by
  have : FiniteDimensional Kᵥ M := localizedCompletionFiniteDimensional vK hvK w
  let : Algebra K M := localizedCompletionGlobalAlgebra vK w
  have : IsScalarTower K Kᵥ M := localizedCompletionIsScalarTower vK w
  let j := localizedCompletionToAlgHom vK w
  let r := embeddedGaloisRestriction (B := Kᵥ) j
  let φ := galoisUnitsMap r j.toRingHom (embeddedGaloisRestriction_commutes (B := Kᵥ) j)
  let e := decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let U := Rep.ofAlgebraAutOnUnits K L
  let V := Rep.ofMulDistribMulAction Gal(L/K) Tˣ
  let W := tensorDecompositionRep vK hvK w
  let Y := Rep.ofAlgebraAutOnUnits Kᵥ M
  let f : U ⟶ V := localTensorDiagonalRepHom vK
  let ev : Rep.res (Decomp).subtype V ⟶ W := localTensorEvaluationRepHom vK hvK w
  let eW : W ≃ₗ[ℤ] Y := LinearEquiv.refl ℤ (Additive Mˣ)
  have heW (σ : Decomp) : eW ∘ₗ W.ρ σ = Y.ρ (e σ) ∘ₗ eW := rfl
  let eM := groupCohomology.mapIso e eW heW 2
  let η : Rep.res e.symm.toMonoidHom W ⟶ Y :=
    Rep.ofHom ⟨eW.toLinearMap, fun σ => by
      change eW.toLinearMap ∘ₗ W.ρ (e.symm σ) = Y.ρ σ ∘ₗ eW.toLinearMap
      exact (heW (e.symm σ)).trans (congrArg
        (fun t => Y.ρ t ∘ₗ eW.toLinearMap) (e.apply_symm_apply σ))⟩
  have hr (σ : Decomp) : r (e σ) = σ.val := by
    apply AlgEquiv.ext
    intro x
    apply j.injective
    exact (embeddedGaloisRestriction_commutes (B := Kᵥ) j (e σ) x).trans
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization vK hvK w σ x)
  have hr' (σ : Gal(M/Kᵥ)) : r σ = (e.symm σ).val :=
    (congrArg r (e.apply_symm_apply σ)).symm.trans (hr (e.symm σ))
  have heval (x : Additive Lˣ) :
      ev (f x) = Additive.ofMul (Units.map j.toMonoidHom x.toMul) := by
    let b : Additive Tˣ := f x
    have hb : (Additive.ofMul (Units.map (localTensorEvaluation vK hvK w).toMonoidHom b.toMul) :
        Additive Mˣ) = Additive.ofMul (Units.map j.toMonoidHom x.toMul) := by
      apply Additive.ofMul.injective
      apply Units.ext
      change localTensorEvaluation vK hvK w ((1 : Kᵥ) ⊗ₜ[K] (x.toMul : L)) = j (x.toMul : L)
      rw [localTensorEvaluation_tmul, map_one, one_mul]; rfl
    exact (localTensorEvaluationRepHom_apply vK hvK w b).trans hb
  let c₀ : groupCohomology.cocycles₂ U := dehomogenizeTwoOriginal (galoisUnitsRep K L) z
  let c₁ : groupCohomology.cocycles₂ V := groupCohomology.mapCocycles₂ (MonoidHom.id _) f c₀
  let c₂ : groupCohomology.cocycles₂ W := groupCohomology.mapCocycles₂ (Decomp).subtype ev c₁
  let c₃ : groupCohomology.cocycles₂ Y := groupCohomology.mapCocycles₂ e.symm.toMonoidHom η c₂
  let zM := cocyclesMap r φ 2 z
  let cM : groupCohomology.cocycles₂ Y := dehomogenizeTwoOriginal (galoisUnitsRep Kᵥ M) zM
  have hc : c₃ = cM := by
    apply groupCohomology.cocycles₂_ext
    intro g h
    let d := ((TopRep.homogeneousCochains (galoisUnitsRep K L)).iCycles 2 z).val
    let g₀ := (e.symm g).val
    let h₀ := (e.symm h).val
    let a : Additive Lˣ := c₀ (g₀, h₀)
    change (show Additive Mˣ from ev (f a)) = cM (g, h)
    have ha : a = d 1 g₀ (g₀ * h₀) := dehomogenizeTwoOriginal_apply _ _ g₀ h₀
    have hd : d (r 1) (r g) (r (g * h)) = d 1 g₀ (g₀ * h₀) := by
      rw [map_one, map_mul, hr' g, hr' h]
    have hM : cM (g, h) = φ (d (r 1) (r g) (r (g * h))) :=
      (dehomogenizeTwoOriginal_apply _ _ g h).trans (mappedRelativeCocycle_apply r φ z 1 g (g * h))
    have hφ : (show Additive Mˣ from φ a) = Additive.ofMul (Units.map j.toMonoidHom a.toMul) :=
      galoisUnitsMap_apply r j.toRingHom (embeddedGaloisRestriction_commutes (B := Kᵥ) j) a
    exact (heval a).trans (hφ.symm.trans ((congrArg (fun t : Additive Lˣ => φ t)
      (ha.trans hd.symm)).trans hM.symm))
  let x := groupCohomology.map (MonoidHom.id (Gal(L/K))) f 2 (groupCohomology.H2π U c₀)
  let S := (localTensorShapiro vK hvK w 2).hom
  let eH : continuousCohomology 2 (galoisUnitsRep Kᵥ M) ≃+ groupCohomology Y 2 :=
    discreteOriginalH2Equiv (galoisUnitsRep Kᵥ M)
  have hs : S x = groupCohomology.map (Decomp).subtype ev 2 x :=
    ConcreteCategory.congr_hom (localTensorShapiro_hom_eq_map vK hvK w 2) x
  have h₃ : eM.hom (groupCohomology.map (Decomp).subtype ev 2 x) =
      groupCohomology.H2π Y c₃ :=
    h2π_iterated_map (Decomp).subtype e.symm.toMonoidHom f ev η c₀
  have h₄ : eH (π (galoisUnitsRep Kᵥ M) 2 zM) = groupCohomology.H2π Y cM :=
    discreteOriginalH2Equiv_π (galoisUnitsRep Kᵥ M) zM
  have hx : eM.hom (S x) = eH (π (galoisUnitsRep Kᵥ M) 2 zM) :=
    (congrArg (fun t : groupCohomology W 2 => eM.hom t) hs).trans
      (h₃.trans ((congrArg (fun z' : groupCohomology.cocycles₂ Y =>
        groupCohomology.H2π Y z') hc).trans h₄.symm))
  have hres : localizedFieldRelativeRestriction vK w (π (galoisUnitsRep K L) 2 z) =
      π (galoisUnitsRep Kᵥ M) 2 zM :=
    ConcreteCategory.congr_hom (π_map r φ 2) z
  change eH.symm (eM.hom (S x)) = _
  exact (congrArg eH.symm hx).trans
    ((eH.symm_apply_apply (π (galoisUnitsRep Kᵥ M) 2 zM)).trans hres.symm)

include hvK in
/-- The actual tensor coordinate vanishes when the chosen completed restriction does. -/
theorem localTensorDiagonalH2_eq_zero_of_relativeRestriction
    (z : cocycles (galoisUnitsRep K L) 2)
    (hz : localizedFieldRelativeRestriction vK w (π (galoisUnitsRep K L) 2 z) = 0) :
    groupCohomology.map (MonoidHom.id (Gal(L/K))) (localTensorDiagonalRepHom vK) 2
      (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (dehomogenizeTwoOriginal (galoisUnitsRep K L) z)) = 0 := by
  apply (localTensorRelativeH2Equiv vK hvK w).injective
  rw [localTensorRelativeH2Equiv_diagonal, hz, map_zero]

end ClassFieldTheory.Brauer
