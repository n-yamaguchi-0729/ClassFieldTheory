/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.AffinePullbackSections
public import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.SectionsOf
public import Nyll.SchemeTheory.Modules.Quasicoherent.TildePullback
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Basic
public import Nyll.SchemeTheory.Modules.Quasicoherent.TildeLocalization
public import Nyll.SchemeTheory.Modules.Quasicoherent.IsoBaseChangeSectionsIsoFromTildeGamma

public import Nyll.SchemeTheory.Modules.Functoriality.AffineSectionsBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Extended sections of a locally trivial module

On an affine open and its affine base change, extending the section module gives
the sections of the pulled-back locally trivial module.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange
  (pullbackAffineOpenIsoSpecTensor) in
open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj
          M)
      ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U)
    ∃ e : A ⊗[R] Γ(M, U) ≃ₗ[A]
        Γ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R
            A))).obj M,
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app U).hom m
              := by
  let p : Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A) ⟶ X :=
    Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)
  let V := p ⁻¹ᵁ U
  let B : Type u := Γ(X, U)
  let C : Type u := Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), V)
  let N : Type u := Γ(M, U)
  let P : Type u := Γ((Scheme.Modules.pullback p).obj M, V)
  let : Algebra R B := Scheme.TwoAffineOpenCover.algebraOfHom c U
  let : Algebra A C := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) V
  let : Algebra B C := (p.app U).hom.toAlgebra
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  let : Module R N := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
  let : Module A P := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
    ((Scheme.Modules.pullback p).obj M) V
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R B N := Scheme.TwoAffineOpenCover.isScalarTower_sections c M U
  have : IsScalarTower A C P := Scheme.TwoAffineOpenCover.isScalarTower_sections
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
    ((Scheme.Modules.pullback p).obj M) V
  let α : A ⊗[R] B ≃ₐ[A] C :=
    _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv c A U hU
  let δ : B →ₐ[R] C := (α.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
  have hδ (b : B) : δ b = algebraMap B C b :=
    _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv_one_tmul c A U hU b
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r =>
    (δ.commutes r).symm.trans (hδ (algebraMap R B r))
  have : Algebra.IsPushout R A B C :=
    ⟨IsBaseChange.of_equiv α.toLinearEquiv (fun b => by
      change α ((1 : A) ⊗ₜ[R] b) = (p.app U).hom b
      exact _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv_one_tmul
        c A U hU b)⟩
  have hV : IsAffineOpen V := by
    change IsAffine V.toScheme
    exact IsAffine.of_isIso
      (pullbackAffineOpenIsoSpecTensor c A U hU).hom
  obtain ⟨β, hβ⟩ := Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback
    p (show Scheme.Modules.IsInvertible M from ⟨htriv⟩) U hU hV
  refine ⟨(Algebra.IsPushout.cancelBaseChange R A B C N).symm.trans
    (β.restrictScalars A), ?_⟩
  intro m
  change β ((Algebra.IsPushout.cancelBaseChange R A B C N).symm ((1 : A) ⊗ₜ[R] m)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]
  exact hβ m

end
end Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
