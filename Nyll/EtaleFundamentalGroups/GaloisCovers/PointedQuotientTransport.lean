/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiberQuotient
public import Mathlib.CategoryTheory.Conj

/-!
# Transport of pointed Galois quotients

The quotient attached to a Galois object is natural under an isomorphism
between fiber functors, provided that the chosen point is transported along
the same isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u₁ u₂ w

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable (Phi Psi : C ⥤ FintypeCat.{w}) [FiberFunctor Phi] [FiberFunctor Psi]

/-- Pointed Galois-object quotients commute with conjugation along an
isomorphism of fiber functors. -/
theorem galoisObjectQuotientMonoidHom_transport
    (p : Phi ≅ Psi) (A : C) [IsGalois A]
    (y : Psi.obj A) (a : Aut Phi) :
    galoisObjectQuotientMonoidHom Phi (Aut Phi) A (p.inv.app A y) a =
      galoisObjectQuotientMonoidHom Psi (Aut Psi) A y (p.conjAut a) := by
  apply MulOpposite.unop_injective
  apply (evaluationEquivOfIsGalois Psi A y).injective
  simp only [evaluationEquivOfIsGalois_apply]
  rw [galoisObjectQuotientMonoidHom_evaluation]
  let theta : Aut A :=
    (galoisObjectQuotientMonoidHom Phi (Aut Phi) A (p.inv.app A y) a).unop
  have hPhi := galoisObjectQuotientMonoidHom_evaluation
    Phi (Aut Phi) A (p.inv.app A y) a
  have hnat := ConcreteCategory.congr_hom (p.hom.naturality theta.asIso.hom)
    (p.inv.app A y)
  change Psi.map theta.asIso.hom y = (p.conjAut a).asIso.hom.app A y
  have hy : p.hom.app A (p.inv.app A y) = y :=
    FintypeCat.inv_hom_id_apply (p.app A) y
  calc
    Psi.map theta.asIso.hom y =
        Psi.map theta.asIso.hom (p.hom.app A (p.inv.app A y)) :=
      congrArg (Psi.map theta.asIso.hom) hy.symm
    _ = p.hom.app A (Phi.map theta.asIso.hom (p.inv.app A y)) := hnat.symm
    _ = p.hom.app A (a • p.inv.app A y) := congrArg (p.hom.app A) hPhi
    _ = (p.conjAut a).asIso.hom.app A y := by
      change p.hom.app A (a.asIso.hom.app A (p.inv.app A y)) = _
      rfl

/-- Naturality of pointed Galois-object quotients after precomposition by an
arbitrary group homomorphism. -/
theorem galoisObjectQuotientMonoidHom_transport_comp
    (p : Phi ≅ Psi) (A : C) [IsGalois A]
    (y : Psi.obj A) {G : Type*} [Group G]
    (h : G →* Aut Phi) :
    (galoisObjectQuotientMonoidHom
        Phi (Aut Phi) A (p.inv.app A y)).comp h =
      (galoisObjectQuotientMonoidHom Psi (Aut Psi) A y).comp
        (p.conjAut.toMonoidHom.comp h) := by
  apply MonoidHom.ext
  intro a
  exact galoisObjectQuotientMonoidHom_transport Phi Psi p A y (h a)

end CategoryTheory.PreGaloisCategory

open AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- Finite-etale specialization of pointed-quotient transport. -/
theorem finiteEtaleGaloisCoverQuotientMonoidHom_transport
    {X : Scheme.{u}} [ConnectedSpace X]
    {Omega Omega' : Type u}
    [Field Omega] [IsSepClosed Omega]
    [Field Omega'] [IsSepClosed Omega']
    (xi : Spec (.of Omega) ⟶ X) (xi' : Spec (.of Omega') ⟶ X)
    (p : fiber xi ≅ fiber xi')
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (fiber xi').obj Y) (a : Aut (fiber xi)) :
    finiteEtaleGaloisCoverQuotientMonoidHom
        xi Y hY (p.inv.app Y y) a =
      finiteEtaleGaloisCoverQuotientMonoidHom
        xi' Y hY y (p.conjAut a) := by
  let : IsGalois Y := hY
  exact galoisObjectQuotientMonoidHom_transport
    (fiber xi) (fiber xi') p Y y a

end EtaleFundamentalGroups

end
