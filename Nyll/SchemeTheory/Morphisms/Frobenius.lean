/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.RingTheory.Ideal.Operations

/-!
# Frobenius of schemes over finite fields

Frobenius acts as the identity on the topological space and by the actual power
homomorphism on each ring of sections. The germ formula identifies its stalk
map with the same power map and proves that it is local. The construction
also covers the zero ring of sections on the empty open.
-/

noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme) (k : Type*) [Field k] [Fintype k]
    [∀ U : X.Opens, Algebra k Γ(X, U)]

/-- The actual power maps on sections, assembled as a presheafed-space morphism. -/
def frobeniusPresheafHom : X.toPresheafedSpace.Hom X.toPresheafedSpace where
  base := 𝟙 _
  c :=
    { app := fun U => CommRingCat.ofHom (FiniteField.frobeniusAlgHom k Γ(X, U.unop)).toRingHom
      naturality := by
        intro U V i
        apply CommRingCat.hom_ext
        ext a
        exact (map_pow (X.presheaf.map i).hom a (Fintype.card k)).symm }

/-- On stalks the sectionwise Frobenius is the actual power map. -/
theorem frobeniusPresheafHom_stalkMap (x : X) (a : X.presheaf.stalk x) :
    (frobeniusPresheafHom X k).stalkMap x a = a ^ Fintype.card k := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have h := congrArg (fun f : Γ(X, U) ⟶ X.presheaf.stalk x => f s)
    (PresheafedSpace.stalkMap_germ (frobeniusPresheafHom X k) U x hx)
  change (frobeniusPresheafHom X k).stalkMap x (X.presheaf.germ U x hx s) =
    X.presheaf.germ U x hx (s ^ Fintype.card k) at h
  exact h.trans (map_pow (X.presheaf.germ U x hx).hom s (Fintype.card k))

/-- Finite-field Frobenius as a morphism of the actual scheme. -/
def finiteFieldFrobenius : X ⟶ X where
  toLRSHom' :=
    { toHom := frobeniusPresheafHom X k
      prop := fun x =>
        { map_nonunit := fun a ha => by
            have hp := frobeniusPresheafHom_stalkMap X k x a
            have ha' : IsUnit (a ^ Fintype.card k) := hp ▸ ha
            exact (isUnit_pow_iff Fintype.card_pos.ne').mp ha' } }

/-- Finite-field Frobenius is the identity on the underlying topological space. -/
theorem finiteFieldFrobenius_base : (finiteFieldFrobenius X k).base = 𝟙 X.toTopCat := rfl

/-- The actual map on sections is the cardinality power map. -/
theorem finiteFieldFrobenius_app (U : X.Opens) (a : Γ(X, U)) :
    (finiteFieldFrobenius X k).app U a = a ^ Fintype.card k := rfl

/-- The actual map on global sections is the cardinality power map. -/
theorem finiteFieldFrobenius_appTop (a : Γ(X, ⊤)) :
    (finiteFieldFrobenius X k).appTop a = a ^ Fintype.card k := rfl

/-- The stalk map of finite-field Frobenius raises elements to the same power. -/
theorem finiteFieldFrobenius_stalkMap (x : X) (a : X.presheaf.stalk x) :
    (finiteFieldFrobenius X k).stalkMap x a = a ^ Fintype.card k :=
  frobeniusPresheafHom_stalkMap X k x a

/-- Frobenius sends the maximal ideal into its corresponding power at every stalk. -/
theorem finiteFieldFrobenius_map_maximalIdeal_le_pow (x : X) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk ((finiteFieldFrobenius X k).base x))).map
        ((finiteFieldFrobenius X k).stalkMap x).hom ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ Fintype.card k := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change (finiteFieldFrobenius X k).stalkMap x a ∈
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ Fintype.card k
  have hp := finiteFieldFrobenius_stalkMap X k x a
  exact hp.symm ▸ Ideal.pow_mem_pow ha (Fintype.card k)

/-- Finite-field Frobenius has zero cotangent map, expressed using the actual stalk ideals. -/
theorem finiteFieldFrobenius_map_maximalIdeal_le_sq (x : X) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk ((finiteFieldFrobenius X k).base x))).map
        ((finiteFieldFrobenius X k).stalkMap x).hom ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 :=
  (finiteFieldFrobenius_map_maximalIdeal_le_pow X k x).trans
    (Ideal.pow_le_pow_right Fintype.one_lt_card)

/-- Frobenius commutes with every morphism between schemes carrying finite-field
algebras of sections, independently of the chosen algebra presentations. -/
theorem finiteFieldFrobenius_naturality (Y : Scheme) [∀ U : Y.Opens, Algebra k Γ(Y, U)]
    (f : X ⟶ Y) : finiteFieldFrobenius X k ≫ f = f ≫ finiteFieldFrobenius Y k := by
  have hbase : (finiteFieldFrobenius X k ≫ f).base =
      (f ≫ finiteFieldFrobenius Y k).base := rfl
  apply Scheme.Hom.ext hbase
  intro U
  change (f.app U ≫ CommRingCat.ofHom
    (FiniteField.frobeniusAlgHom k Γ(X, f ⁻¹ᵁ U)).toRingHom) ≫
      X.presheaf.map (𝟙 (op (f ⁻¹ᵁ U))) =
    CommRingCat.ofHom (FiniteField.frobeniusAlgHom k Γ(Y, U)).toRingHom ≫ f.app U
  rw [CategoryTheory.Functor.map_id]
  apply CommRingCat.hom_ext
  ext a
  change (f.app U a) ^ Fintype.card k = f.app U (a ^ Fintype.card k)
  exact (map_pow (f.app U).hom a (Fintype.card k)).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

universe u

variable (k R : Type u) [Field k] [Fintype k] [CommRing R] [Algebra k R]
    [∀ U : (Spec (.of R)).Opens, Algebra k Γ(Spec (.of R), U)]

/-- On an affine spectrum, scheme Frobenius is induced by the actual ring Frobenius. -/
theorem finiteFieldFrobenius_spec :
    (Spec (.of R)).finiteFieldFrobenius k =
      Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k R).toRingHom) := by
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (.of R)).hom).mp
  rw [Scheme.ΓSpecIso_naturality]
  apply CommRingCat.hom_ext
  ext a
  change (Scheme.ΓSpecIso (.of R)).hom (a ^ Fintype.card k) =
    ((Scheme.ΓSpecIso (.of R)).hom a) ^ Fintype.card k
  exact map_pow (Scheme.ΓSpecIso (.of R)).hom.hom a (Fintype.card k)

end AlgebraicGeometry.Scheme
