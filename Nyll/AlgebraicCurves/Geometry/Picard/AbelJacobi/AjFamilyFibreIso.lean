/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.AbelJacobiFamily
public import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI
public import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.PullbackOfPoint
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPullbackInvModuleIso
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealIsoPullbackModuleComparison

public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal

/-!
# Relative Picard varieties and fibre cohomology

Identify the fibres of the Abel–Jacobi family with the point-difference line bundles.
-/

@[expose] public section

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.Nonempty_ajFamily_fibre_iso

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

/-- The same Abel–Jacobi family pulls back to the difference of the
specified point and the base-point section over any parameter scheme. -/
theorem _root_.AlgebraicGeometry.RelPicard.nonempty_ajFamily_pullbackAlong_iso
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (t : SchemeHomOver s a) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t)).obj (ajFamily (a := a) ε) ≅
      (RelEffCartierDiv.ofPoint a t.1 t.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint a (s ≫ ε.1)
          ((Category.assoc _ _ _).trans
            ((congrArg (s ≫ ·) ε.2).trans (Category.comp_id s)))).idealModule) := by
  change Nonempty ((Scheme.Modules.pullback (mapOnProdOver a t.1 t.2)).obj
    (ajFamily (a := a) ε) ≅ _)
  have hΔ : (diagDiv (a := a)).pullbackAlong t.1 t.2 = RelEffCartierDiv.ofPoint a t.1 t.2 :=
    (RelEffCartierDiv.pullbackAlong_ofPoint a (𝟙 A) (Category.id_comp a) t.1 t.2).trans
      (RelEffCartierDiv.ofPoint_congr a (Category.comp_id _) _ _)
  have hE : (constDiv (a := a) ε).pullbackAlong t.1 t.2 = RelEffCartierDiv.ofPoint a (s ≫ ε.1)
      ((Category.assoc _ _ _).trans
        ((congrArg (s ≫ ·) ε.2).trans (Category.comp_id s))) :=
    (RelEffCartierDiv.pullbackAlong_ofPoint a (a ≫ ε.1) (comp_point_comp ε) t.1 t.2).trans
      (RelEffCartierDiv.ofPoint_congr a (by rw [← Category.assoc, t.2]) _ _)
  have hΔ' : (diagDiv (a := a)).I.comap (mapOnProdOver a t.1 t.2) =
    (RelEffCartierDiv.ofPoint a t.1 t.2).I :=
    congrArg RelEffCartierDiv.I hΔ
  have hE' : (constDiv (a := a) ε).I.comap (mapOnProdOver a t.1 t.2) =
    (RelEffCartierDiv.ofPoint a (s ≫ ε.1)
      ((Category.assoc _ _ _).trans
        ((congrArg (s ≫ ·) ε.2).trans (Category.comp_id s)))).I :=
    congrArg RelEffCartierDiv.I hE
  have hcΔ : ((diagDiv (a := a)).I.comap (mapOnProdOver a t.1 t.2)).IsInvertible :=
    RelEffCartierDiv.isInvertible_I ((diagDiv (a := a)).pullbackAlong t.1 t.2)
  have hcE : ((constDiv (a := a) ε).I.comap (mapOnProdOver a t.1 t.2)).IsInvertible :=
    RelEffCartierDiv.isInvertible_I ((constDiv (a := a) ε).pullbackAlong t.1 t.2)
  obtain ⟨iΔ⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso
    (mapOnProdOver a t.1 t.2)
    (RelEffCartierDiv.isInvertible_I (diagDiv (a := a))) hcΔ
  let iE : (Scheme.Modules.pullback (mapOnProdOver a t.1 t.2)).obj (constDiv (a := a) ε).I.module ≅
      ((constDiv (a := a) ε).I.comap (mapOnProdOver a t.1 t.2)).module :=
    @asIso _ _ _ _ ((constDiv (a := a) ε).I.pullbackModuleComparison (mapOnProdOver a t.1 t.2))
      (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (mapOnProdOver a t.1 t.2)
        (RelEffCartierDiv.isInvertible_I (constDiv (a := a) ε)) hcE)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (?_ ⊗ᵢ ?_)⟩
  · exact iΔ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hΔ')
  · exact iE ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module hE')

/-- The rational-point fibre is the specialization over the identity base. -/
theorem _root_.AlgebraicGeometry.RelPicard.nonempty_ajFamily_fibre_iso
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t)).obj (ajFamily (a := a) ε) ≅
      pointSubBasepointModule (a := a) t ε) := by
  simpa only [Category.id_comp] using nonempty_ajFamily_pullbackAlong_iso ε (𝟙 _) t

end JacobianVarieties.Picard.Proofs.Nonempty_ajFamily_fibre_iso
end ProofImplementation
