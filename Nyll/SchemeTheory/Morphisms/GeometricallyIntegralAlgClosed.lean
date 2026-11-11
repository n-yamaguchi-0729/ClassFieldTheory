/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.Tactic.Algebraize
public import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed

/-!
# Geometric integrality over an algebraically closed field

An integral scheme locally of finite type over an algebraically closed field is
geometrically integral, using the domain property of tensor products of affine sections.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs.geometricallyIntegral_of_isAlgClosed

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

namespace GeomIntegralOfIsAlgClosed

variable {K : Type u} [Field K]

theorem algebraMap_quotient_bijective_of_isAlgClosed [IsAlgClosed K] {A : Type*} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    Function.Bijective (algebraMap K (A ⧸ m)) := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have : Algebra.IsIntegral K (A ⧸ m) := inferInstance
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

variable (K) in
/-- The rational point corresponding to a maximal ideal over an algebraically closed field. -/
noncomputable def pointOfMaximal [IsAlgClosed K] {A : Type*} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] : A →ₐ[K] K :=
  let e := RingEquiv.ofBijective (algebraMap K (A ⧸ m))
    (algebraMap_quotient_bijective_of_isAlgClosed m)
  { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
    commutes' := fun k => by
      change e.symm (Ideal.Quotient.mk m (algebraMap K A k)) = k
      rw [Ideal.Quotient.mk_algebraMap]
      exact e.symm_apply_apply k }

theorem pointOfMaximal_eq_zero_iff [IsAlgClosed K] {A : Type*} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] (a : A) :
    pointOfMaximal K m a = 0 ↔ a ∈ m := by
  change (RingEquiv.ofBijective (algebraMap K (A ⧸ m))
    (algebraMap_quotient_bijective_of_isAlgClosed m)).symm (Ideal.Quotient.mk m a) = 0 ↔ a ∈ m
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed in
theorem isDomain_tensorProduct_of_isAlgClosed [IsAlgClosed K] (A B : Type u) [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] [IsDomain A] [CommRing B] [Algebra K B] [IsDomain B] :
    IsDomain (A ⊗[K] B) :=
  BaseChangeIrreducible.isDomain_tensorProduct_of_finiteType (K := K) A B

theorem isIntegral_pullback_SpecMap_of_isAlgClosed [IsAlgClosed K] {A : CommRingCat.{u}}
    (φ : CommRingCat.of K ⟶ A) [IsIntegral (Spec A)] [LocallyOfFiniteType (Spec.map φ)]
    (K' : Type u) [Field K'] [Algebra K K'] :
    IsIntegral ↑(pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap K K')))) := by
  algebraize [φ.hom]
  have hft : Algebra.FiniteType K A := by
    have := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp ‹_›
    exact RingHom.finiteType_algebraMap.mp this
  have : IsDomain A := (affine_isIntegral_iff A).mp ‹_›
  have : IsDomain (A ⊗[K] K') := isDomain_tensorProduct_of_isAlgClosed A K'
  let e : pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap K K'))) ≅
      Spec (.of (A ⊗[K] K')) :=
    pullbackSpecIso K A K'
  exact IsIntegral.of_isIso e.inv

end GeomIntegralOfIsAlgClosed

open GeomIntegralOfIsAlgClosed in
theorem _root_.AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [LocallyOfFiniteType f] :
    GeometricallyIntegral f := by
  refine ⟨(geometrically_iff_of_commRing (P := fun Y : Scheme.{u} => IsIntegral Y)).mpr ?_⟩
  intro K' _ _ Y fst snd h
  let i : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  suffices hP : IsIntegral ↑(pullback f i) by
    have := hP
    exact IsIntegral.of_isIso h.isoPullback.inv
  let 𝒰 := X.affineCover
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 f i
  have hint : ∀ j, Nonempty (𝒰.X j) → IsIntegral (𝒱.X j) := by
    intro j hj
    have hI : IsIntegral (𝒰.X j) := isIntegral_of_isOpenImmersion (𝒰.f j)
    change IsIntegral (Spec _) at hI
    have hlft : LocallyOfFiniteType (𝒰.f j ≫ f) := inferInstance
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒰.f j ≫ f)
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ hlft
    have : IsIntegral (pullback (Spec.map φ) i) :=
      isIntegral_pullback_SpecMap_of_isAlgClosed φ K'
    let e : pullback (Spec.map φ) i ≅ pullback (𝒰.f j ≫ f) i := pullback.congrHom hφ rfl
    exact IsIntegral.of_isIso (Y := pullback (𝒰.f j ≫ f) i) e.hom
  have hred : ∀ j, IsReduced (𝒱.X j) := by
    intro j
    rcases isEmpty_or_nonempty (𝒰.X j) with hj | hj
    · have : IsEmpty ↑(pullback (𝒰.f j ≫ f) i) := Function.isEmpty (pullback.fst (𝒰.f j ≫ f) i)
      have (x : ↑(pullback (𝒰.f j ≫ f) i)) :
          _root_.IsReduced ((pullback (𝒰.f j ≫ f) i).presheaf.stalk x) := isEmptyElim x
      exact isReduced_of_isReduced_stalk (pullback (𝒰.f j ≫ f) i)
    · have := hint j hj
      infer_instance
  have : IsReduced ↑(pullback f i) := IsReduced.of_openCover _ 𝒱
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hj₀ : Nonempty (𝒰.X (𝒰.idx x₀)) := let ⟨y, _⟩ := 𝒰.covers x₀; ⟨y⟩
  have := hint _ hj₀
  have hrange : Set.range (𝒱.f (𝒰.idx x₀)) =
      pullback.fst f i ⁻¹' Set.range (𝒰.f (𝒰.idx x₀)) := by
    have hid : Set.range (𝟙 (Spec (.of K')) : Spec (.of K') ⟶ _) = Set.univ :=
      Set.range_eq_univ.mpr fun y => ⟨y, rfl⟩
    have := Scheme.Pullback.range_map (𝒰.f (𝒰.idx x₀) ≫ f) i f i (𝒰.f (𝒰.idx x₀)) (𝟙 _)
      (𝟙 _) (Category.comp_id _)
      (by rw [Category.comp_id, Category.id_comp])
    rw [hid, Set.preimage_univ, Set.inter_univ] at this
    exact this
  have hopen : IsOpenMap (pullback.fst f i) := (pullback.fst f i).isOpenMap
  have hdense : Dense (Set.range (𝒱.f (𝒰.idx x₀))) := by
    rw [hrange, dense_iff_inter_open]
    intro W hW hWne
    obtain ⟨_, ⟨w, hw, rfl⟩, hw'⟩ := nonempty_preirreducible_inter (hopen W hW)
      (𝒰.f (𝒰.idx x₀)).isOpenEmbedding.isOpen_range (hWne.image _) (Set.range_nonempty _)
    exact ⟨w, hw, hw'⟩
  have hirr : IsIrreducible (Set.range (𝒱.f (𝒰.idx x₀))) := by
    have := (IrreducibleSpace.isIrreducible_univ (X := 𝒱.X (𝒰.idx x₀))).image _
      (𝒱.f (𝒰.idx x₀)).continuous.continuousOn
    rwa [Set.image_univ] at this
  have : IrreducibleSpace ↑(pullback f i) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense.closure_eq]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end AlgebraicCurves.Geometry.Curves.Proofs.geometricallyIntegral_of_isAlgClosed
end ProofImplementation
