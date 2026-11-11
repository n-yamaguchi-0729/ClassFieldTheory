/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-!
# Geometric fiber comparison under a source isomorphism

Precomposition of field-valued points supplies the fiber comparison. The
existing point representation and equivalence of hom sets retain its actual
coefficient map, without choosing an unspecified fiber isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω Ω' : Type u}
    [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (xi : Spec (.of Ω) ⟶ S) (e : Spec (.of Ω') ≅ Spec (.of Ω))

/-- The geometric fiber comparison induced by precomposition of points. -/
def fiberSourceIso : fiber xi ≅ fiber (e.hom ≫ xi) := by
  let p : Over.mk (e.hom ≫ xi) ≅ Over.mk xi := Over.isoMk e rfl
  let a (A : FiniteEtale S) : (fiber xi).obj A ≃ (fiber (e.hom ≫ xi)).obj A :=
    (fiberObjEquivHom xi A).trans
      (p.symm.homFromEquiv.trans (fiberObjEquivHom (e.hom ≫ xi) A).symm)
  have ha (A : FiniteEtale S) (x : (fiber xi).obj A) :
      fiberObjEquivHom (e.hom ≫ xi) A (a A x) = p.hom ≫ fiberObjEquivHom xi A x := by
    exact (fiberObjEquivHom (e.hom ≫ xi) A).apply_symm_apply _
  refine NatIso.ofComponents (fun A => FintypeCat.equivEquivIso (a A)) ?_
  intro A B f
  ext x
  apply (fiberObjEquivHom (e.hom ≫ xi) B).injective
  change fiberObjEquivHom (e.hom ≫ xi) B (a B ((fiber xi).map f x)) =
    fiberObjEquivHom (e.hom ≫ xi) B ((fiber (e.hom ≫ xi)).map f (a A x))
  rw [ha, ← fiberObjEquivHom_naturality (e.hom ≫ xi), ha,
    ← fiberObjEquivHom_naturality xi]
  exact (Category.assoc _ _ _).symm

/-- The comparison acts on actual field-valued points by the specified source isomorphism. -/
theorem fiberSourceIso_point (A : FiniteEtale S) (x : (fiber xi).obj A) :
    (fiberObjEquivHom (e.hom ≫ xi) A ((fiberSourceIso xi e).hom.app A x)).left =
      e.hom ≫ (fiberObjEquivHom xi A x).left := by
  change ((fiberObjEquivHom (e.hom ≫ xi) A)
    ((fiberObjEquivHom (e.hom ≫ xi) A).symm _)).left = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem fiberObjEquivHom_point_transport
    {Y : Scheme.{u}} (x y : Spec (.of Ω') ⟶ Y) (h : x = y)
    (A : FiniteEtale Y) (a : (fiber x).obj A) :
    (fiberObjEquivHom y A ((eqToIso (congrArg fiber h)).hom.app A a)).left =
      (fiberObjEquivHom x A a).left := by
  subst y
  rfl

/-- Closing the specified source comparison at the same geometric point retains
its actual action on field-valued points. -/
theorem fiberSourceIso_aut_point
    {Y : Scheme.{u}} {E : Type u} [Field E] [IsSepClosed E]
    (x : Spec (.of E) ⟶ Y) (a : Spec (.of E) ≅ Spec (.of E))
    (h : a.hom ≫ x = x) (A : FiniteEtale Y) (v : (fiber x).obj A) :
    (fiberObjEquivHom x A
      ((fiberSourceIso x a ≪≫ eqToIso (congrArg fiber h)).hom.app A v)).left =
        a.hom ≫ (fiberObjEquivHom x A v).left := by
  change (fiberObjEquivHom x A ((eqToIso (congrArg fiber h)).hom.app A
    ((fiberSourceIso x a).hom.app A v))).left = _
  rw [fiberObjEquivHom_point_transport _ _ h, fiberSourceIso_point]

/-- Precomposition of geometric points commutes with the original pullback-fiber comparison. -/
theorem fiberSourceIso_pullback {Y : Scheme.{u}} (f : S ⟶ Y) :
    pullbackFiberIso f xi ≪≫ fiberSourceIso (xi ≫ f) e =
      Functor.isoWhiskerLeft (pullback f) (fiberSourceIso xi e) ≪≫
        pullbackFiberIso f (e.hom ≫ xi) ≪≫
          eqToIso (congrArg fiber (Category.assoc e.hom xi f)) := by
  apply Iso.ext
  ext A a
  apply (fiberObjEquivHom (e.hom ≫ (xi ≫ f)) A).injective
  ext1
  change (fiberObjEquivHom (e.hom ≫ (xi ≫ f)) A
    ((fiberSourceIso (xi ≫ f) e).hom.app A ((pullbackFiberIso f xi).hom.app A a))).left =
    (fiberObjEquivHom (e.hom ≫ (xi ≫ f)) A
      ((eqToIso (congrArg fiber (Category.assoc e.hom xi f))).hom.app A
        ((pullbackFiberIso f (e.hom ≫ xi)).hom.app A
          ((fiberSourceIso xi e).hom.app ((pullback f).obj A) a)))).left
  rw [fiberSourceIso_point,
    fiberObjEquivHom_point_transport _ _ (Category.assoc e.hom xi f),
    pullbackFiberIso_hom_fiberObjEquivHom_left,
    pullbackFiberIso_hom_fiberObjEquivHom_left, fiberSourceIso_point]
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.FiniteEtale
