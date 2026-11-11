/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois

/-!
# The actual point action of the supplied Galois comparison

This computation is proved over abstract fields, so callers retain their
original field structures without unfolding the construction of the fiber
automorphism group at those concrete fields.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω]

/-- Automorphisms of the geometric-point field act on its actual finite
étale fiber, without requiring the field to be a separable closure.
Only the naturality of the existing point action is used here. -/
def fieldAutomorphismFiberAction : (Ω ≃ₐ[F] Ω) →* Aut (fib F Ω) := by
  have : PreGaloisCategory.IsNaturalSMul (fib F Ω) (Ω ≃ₐ[F] Ω) := by
    constructor
    intro σ X Y f x
    apply (fiberObjEquivHom (ξ F Ω) Y).injective
    rw [algEquiv_smul_fiber_def, algEquiv_smul_fiber_def]
    rw [fiberObjEquivHom_symm_naturality, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, ← fiberObjEquivHom_naturality (ξ F Ω) f x]
    apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom (ξ F Ω) X x).left) ≫ f.left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        ((fiberObjEquivHom (ξ F Ω) X x).left ≫ f.left)
    exact Category.assoc _ _ _
  exact PreGaloisCategory.toAut (fib F Ω) (Ω ≃ₐ[F] Ω)

/-- The general field action retains its literal spectrum map on each
geometric point, including an algebraic-closure point in positive characteristic. -/
theorem fieldAutomorphismFiberAction_point
    (σ : Ω ≃ₐ[F] Ω) (X : FiniteEtale (Spec (.of F))) (x : (fib F Ω).obj X) :
    (fiberObjEquivHom (ξ F Ω) X
      ((fieldAutomorphismFiberAction F Ω σ).asIso.hom.app X x)).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom (ξ F Ω) X x).left := by
  change (fiberObjEquivHom (ξ F Ω) X (σ • x)).left = _
  rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply, algEquiv_smul_hom]
  rfl

variable [IsSepClosure F Ω]

/-- The supplied Galois automorphism acts by its literal spectrum map. -/
theorem suppliedGaloisEquivFundamentalGroup_point
    (σ : Gal(Ω/F)) (X : FiniteEtale (Spec (.of F))) (x : (fib F Ω).obj X) :
    (fiberObjEquivHom (ξ F Ω) X
      ((suppliedGaloisEquivFundamentalGroup F Ω σ).asIso.hom.app X x)).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom (ξ F Ω) X x).left := by
  exact fieldAutomorphismFiberAction_point F Ω σ X x

end AlgebraicGeometry.FiniteEtale
