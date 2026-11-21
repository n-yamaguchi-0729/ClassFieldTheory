/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Sheaves.IdealSheafComap
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Actual affine section quotients under closed base change

The kernel ideal of a cartesian closed immersion is calculated on the
original affine-open sections. It is the extension of the original
ring-homomorphism kernel under the actual structural coefficient map.
Together with surjectivity, this identifies the affine section transition
as a quotient, without postulating a quotient presentation of the source.

The structural coefficient calculations also retain the factorization
through a specified quotient of the base ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

/-- On global sections the kernel of an actual spectrum morphism is the
original kernel transported through the canonical global-section isomorphism. -/
theorem ker_Spec_map_appTop {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    RingHom.ker (Spec.map φ).appTop.hom =
      (RingHom.ker φ.hom).map (ΓSpecIso R).inv.hom := by
  have hker : (RingHom.ker (Spec.map φ).appTop.hom).comap (ΓSpecIso R).inv.hom =
      RingHom.ker φ.hom := by
    calc
      (RingHom.ker (Spec.map φ).appTop.hom).comap (ΓSpecIso R).inv.hom =
          RingHom.ker (((ΓSpecIso R).inv ≫ (Spec.map φ).appTop).hom) :=
        RingHom.comap_ker _ _
      _ = RingHom.ker ((φ ≫ (ΓSpecIso S).inv).hom) :=
        congrArg (fun k : R ⟶ Γ(Spec S, ⊤) => RingHom.ker k.hom)
          (ΓSpecIso_inv_naturality φ).symm
      _ = RingHom.ker φ.hom :=
        RingHom.ker_comp_of_injective φ.hom
          (ConcreteCategory.bijective_of_isIso (ΓSpecIso S).inv).injective
  have hmap := congrArg (Ideal.map (ΓSpecIso R).inv.hom) hker
  rw [Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv).surjective] at hmap
  exact hmap

namespace Hom

/-- The original coefficients on a composite with a spectrum map retain
the specified ring homomorphism. -/
theorem constToPresheaf_comp_Spec_map {R S : CommRingCat.{u}}
    {Y : Scheme.{u}} (g : Y ⟶ Spec S) (φ : R ⟶ S) (U : Y.Opens) :
    ((g ≫ Spec.map φ).constToPresheaf.app (op U)).hom =
      ((g.constToPresheaf.app (op U)).hom).comp φ.hom := by
  let aR : R ⟶ Γ(Spec R, ⊤) := (ΓSpecIso R).inv
  let aS : S ⟶ Γ(Spec S, ⊤) := (ΓSpecIso S).inv
  let b : Γ(Spec R, ⊤) ⟶ Γ(Spec S, ⊤) := (Spec.map φ).appTop
  let c : Γ(Spec S, ⊤) ⟶ Γ(Y, U) := g.appLE ⊤ U le_top
  let d : Γ(Spec R, ⊤) ⟶ Γ(Y, U) := (g ≫ Spec.map φ).appLE ⊤ U le_top
  have hd : d = b ≫ c := Hom.comp_appLE g (Spec.map φ) ⊤ U le_top
  have hb : aR ≫ b = φ ≫ aS := (ΓSpecIso_inv_naturality φ).symm
  have hcat : aR ≫ d = φ ≫ (aS ≫ c) :=
    (congrArg (fun k => aR ≫ k) hd).trans
      ((Category.assoc aR b c).symm.trans
        ((congrArg (fun k => k ≫ c) hb).trans (Category.assoc φ aS c)))
  exact congrArg CommRingCat.Hom.hom hcat

/-- Coefficients commute with the actual section homomorphism on a
preimage open. -/
theorem constToPresheaf_comp_app {R : CommRingCat.{u}} {Y X : Scheme.{u}}
    (g : Y ⟶ X) (f : X ⟶ Spec R) (U : X.Opens) :
    (g.app U).hom.comp ((f.constToPresheaf.app (op U)).hom) =
      ((g ≫ f).constToPresheaf.app (op (g ⁻¹ᵁ U))).hom := by
  let a : R ⟶ Γ(Spec R, ⊤) := (ΓSpecIso R).inv
  let b : Γ(Spec R, ⊤) ⟶ Γ(X, U) := f.appLE ⊤ U le_top
  let c : Γ(X, U) ⟶ Γ(Y, g ⁻¹ᵁ U) := g.app U
  let d : Γ(Spec R, ⊤) ⟶ Γ(Y, g ⁻¹ᵁ U) := (g ≫ f).appLE ⊤ (g ⁻¹ᵁ U) le_top
  have hbc : b ≫ c = d :=
    (congrArg (fun k : Γ(X, U) ⟶ Γ(Y, g ⁻¹ᵁ U) => b ≫ k)
      (g.app_eq_appLE (U := U))).trans
        (Hom.appLE_comp_appLE g f ⊤ U (g ⁻¹ᵁ U) le_top le_rfl)
  have hcat : (a ≫ b) ≫ c = a ≫ d :=
    (Category.assoc a b c).trans (congrArg (fun k => a ≫ k) hbc)
  exact congrArg CommRingCat.Hom.hom hcat

/-- A cartesian closed base change extends the original kernel on every
actual affine-open section ring. -/
theorem ker_app_of_closed_baseChange {R S : CommRingCat.{u}}
    {Y' Y : Scheme.{u}} (g : Y ⟶ Spec R) (g' : Y' ⟶ Spec S)
    (r : Y' ⟶ Y) (φ : R ⟶ S)
    (h : IsPullback r g' g (Spec.map φ)) (hφ : Function.Surjective φ.hom)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    RingHom.ker (r.app U).hom =
      (RingHom.ker φ.hom).map (g.constToPresheaf.app (op U)).hom := by
  have hi : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  have hr : IsClosedImmersion r :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hi
  have hker : r.ker = (Spec.map φ).ker.comap g := by
    calc
      r.ker = (h.isoPullback.hom ≫ pullback.fst g (Spec.map φ)).ker :=
        congrArg (fun k : Y' ⟶ Y => k.ker) h.isoPullback_hom_fst.symm
      _ = (pullback.fst g (Spec.map φ)).ker := Hom.ker_comp_of_isIso _ _
      _ = (Spec.map φ).ker.comap g :=
        IdealSheafData.ker_fst_of_isClosedImmersion (Spec.map φ) g
  calc
    RingHom.ker (r.app U).hom = r.ker.ideal ⟨U, hU⟩ := (r.ker_apply ⟨U, hU⟩).symm
    _ = ((Spec.map φ).ker.comap g).ideal ⟨U, hU⟩ :=
      congrArg (fun J : Y.IdealSheafData => J.ideal ⟨U, hU⟩) hker
    _ = ((Spec.map φ).ker.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩).map
        (g.appLE ⊤ U le_top).hom :=
      IdealSheafData.ideal_comap_of_le (Spec.map φ).ker g
        ⟨⊤, isAffineOpen_top (Spec R)⟩ ⟨U, hU⟩ le_top
    _ = (RingHom.ker φ.hom).map (g.constToPresheaf.app (op U)).hom := by
      let p : Γ(Spec R, ⊤) ⟶ Γ(Y, U) := g.appLE ⊤ U le_top
      have hbase : (Spec.map φ).ker.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩ =
          (RingHom.ker φ.hom).map (ΓSpecIso R).inv.hom :=
        ((Spec.map φ).ker_apply ⟨⊤, isAffineOpen_top (Spec R)⟩).trans (ker_Spec_map_appTop φ)
      exact (congrArg (fun J : Ideal Γ(Spec R, ⊤) => J.map p.hom) hbase).trans
        (Ideal.map_map _ _)

/-- The same cartesian closed base change gives the actual surjective
section transition; its affine source is also obtained by base change. -/
theorem surjective_app_of_closed_baseChange {R S : CommRingCat.{u}}
    {Y' Y : Scheme.{u}} (g : Y ⟶ Spec R) (g' : Y' ⟶ Spec S)
    (r : Y' ⟶ Y) (φ : R ⟶ S)
    (h : IsPullback r g' g (Spec.map φ)) (hφ : Function.Surjective φ.hom)
    (U : Y.Opens) (hU : IsAffineOpen U) : Function.Surjective (r.app U) := by
  have hi : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  have hr : IsClosedImmersion r :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hi
  exact r.app_surjective U hU

/-- A factorization through the literal quotient spectrum annihilates
the original ideal in every actual section ring. -/
theorem constToPresheaf_annihilates_of_quotient
    {A : Type u} [CommRing A] {Y : Scheme.{u}} (J : Ideal A)
    (g : Y ⟶ Spec (.of (A ⧸ J))) (U : Y.Opens) {a : A} (ha : a ∈ J) :
    (((g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).constToPresheaf.app
      (op U)).hom) a = 0 := by
  rw [constToPresheaf_comp_Spec_map]
  change (g.constToPresheaf.app (op U)).hom (Ideal.Quotient.mk J a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

end Hom

end AlgebraicGeometry.Scheme
