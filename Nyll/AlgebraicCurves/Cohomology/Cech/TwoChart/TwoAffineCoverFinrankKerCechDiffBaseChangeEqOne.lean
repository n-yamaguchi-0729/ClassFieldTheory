/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.BaseChange.TwoChartCechFinrankKerBaseChangeEq
import Nyll.AlgebraicCurves.Geometry.Schemes.Cohomology.TwoAffineCoverToH0Bijective
import Nyll.AlgebraicCurves.Geometry.Schemes.Cohomology.TwoAffineCoverBaseChangeIsosStructureSheaf
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
The base-changed structure-sheaf Cech kernel has dimension one for a smooth proper integral curve.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem finrank_ker_eq_one_of_isAlgClosed
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L]
    [IsIntegral (Limits.pullback c (specMap R L))]
    [Module.Finite L (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L))] :
    Module.finrank L (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L)) = 1 := by
  obtain ⟨e0, e1, e01, eH0, eH1, -, -, -, -, -⟩ := exists_baseChangeIsos_structureSheaf 𝒱 c L
  let := algebraOfHom (Limits.pullback.snd c (specMap R L)) ⊤
  have hT := toH0_bijective (𝒱.pullback c L) (Limits.pullback.snd c (specMap R L))
  let e : Γ(Limits.pullback c (specMap R L), ⊤) ≃ₗ[L]
      LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L) :=
    (LinearEquiv.ofBijective _ hT).trans eH0.symm
  have : Module.Finite L Γ(Limits.pullback c (specMap R L), ⊤) := Module.Finite.equiv e.symm
  have : Algebra.IsIntegral L Γ(Limits.pullback c (specMap R L), ⊤) :=
    Algebra.IsIntegral.of_finite L _
  have hbij : Function.Bijective (algebraMap L Γ(Limits.pullback c (specMap R L), ⊤)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let eL : L ≃ₗ[L] Γ(Limits.pullback c (specMap R L), ⊤) :=
    LinearEquiv.ofBijective (Algebra.linearMap L _) hbij
  rw [← e.finrank_eq, ← eL.finrank_eq, Module.finrank_self]

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.AlgebraicGeometry
  Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_cechDiff_baseChange_eq_one
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (hint : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R L)))
    (hfin : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      Module.Finite L (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L)))
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) = 1 := by
  let L := AlgebraicClosure K
  have := hint L
  have := hfin L
  rw [_root_.TwoChartCech.finrank_ker_baseChange_eq_of_field_extension
    (𝒱.structureSheafSections c).cechDiff K L]
  exact finrank_ker_eq_one_of_isAlgClosed 𝒱 c L

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
end Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
