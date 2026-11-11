/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.Field
public import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteGeometricallyReducedEtale

/-!
# Geometric reducedness under finite etale covers

A finite etale morphism has reduced fibres after every field extension.
A finite etale cover of a geometrically reduced family of finite type is
therefore geometrically reduced over the original base. No Noetherian
condition is imposed on that base: the intermediate geometric fibre is
locally Noetherian because it is of finite type over its field.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A reduced finite scheme over a perfect field is étale over that field.
The algebra structure is the one induced by its original structure morphism. -/
lemma etale_of_isFinite_of_isReduced_over_perfectField
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsFinite f] [IsReduced X] :
    Etale f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let : Algebra K Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  have : Module.Finite K Γ(X, ⊤) :=
    f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have hEtale : Algebra.Etale K Γ(X, ⊤) :=
    Algebra.etale_of_finite_of_isReduced_of_perfectField K Γ(X, ⊤)
  exact (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mpr
    ((RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv f.appTop).mp hEtale)

/-- Finite etale morphisms are geometrically reduced. -/
lemma geometricallyReduced_of_isFinite_of_etale
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] :
    GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ y
  let p : pullback f y ⟶ Spec (CommRingCat.of K) := pullback.snd f y
  have : IsAffine (pullback f y) := isAffine_of_isAffineHom p
  have hEtale : p.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := p)).mp inferInstance
  let : Algebra K Γ(pullback f y, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop).hom.toAlgebra
  have : Algebra.Etale K Γ(pullback f y, ⊤) :=
    (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv p.appTop).mpr hEtale
  have : _root_.IsReduced Γ(pullback f y, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field K Γ(pullback f y, ⊤)
  exact isReduced_of_isAffine_isReduced (pullback f y)

/-- A finite etale cover preserves geometric reducedness of a family locally
of finite type over its original base. -/
lemma GeometricallyReduced.comp_of_isFinite_of_etale
    {Y X S : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ S)
    [IsFinite g] [Etale g] [LocallyOfFiniteType f] [GeometricallyReduced f] :
    GeometricallyReduced (g ≫ f) := by
  have : GeometricallyReduced g := geometricallyReduced_of_isFinite_of_etale g
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ y
  have : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced (f := f) y
      (pullback.fst f y) (pullback.snd f y) (IsPullback.of_hasPullback f y)
  have : IsReduced (pullback g (pullback.fst f y)) := inferInstance
  exact isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso f y g).inv

end AlgebraicGeometry
