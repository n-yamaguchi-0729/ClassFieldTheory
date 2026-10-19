/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.FrobeniusOver
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Frobenius after extending finite constants

On the actual base change to an algebraic extension of the finite field, compose
absolute Frobenius with inverse Frobenius on the constants. The resulting map
is over the extended constants, is the base change of the original Frobenius,
and has zero cotangent map at every stalk.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "Y" => pullback f b

private local instance constantSpecOver : (Spec (.of Ω)).Over (Spec (CommRingCat.of k)) := ⟨b⟩

private local instance constantPullbackOver : (Y).Over (Spec (CommRingCat.of k)) :=
  ⟨pullback.fst f b ≫ f⟩

private def inverseFrobeniusOnConstants : Spec (.of Ω) ⟶ Spec (.of Ω) :=
  Spec.map (CommRingCat.ofHom
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm.toRingHom)

private theorem inverseFrobeniusOnConstants_comp :
    inverseFrobeniusOnConstants k Ω ≫ b = b := by
  rw [inverseFrobeniusOnConstants, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm.commutes a

private def inverseConstantTwist : Y ⟶ Y :=
  pullback.lift (pullback.fst f b)
    (pullback.snd f b ≫ inverseFrobeniusOnConstants k Ω) (by
      rw [Category.assoc, inverseFrobeniusOnConstants_comp]
      exact pullback.condition)

private theorem frobenius_inverseFrobeniusOnConstants :
    (Spec (.of Ω)).finiteFieldFrobenius k ≫ inverseFrobeniusOnConstants k Ω =
      𝟙 (Spec (.of Ω)) := by
  rw [finiteFieldFrobenius_spec, inverseFrobeniusOnConstants, ← Spec.map_comp]
  have h : CommRingCat.ofHom (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm.toRingHom ≫
      CommRingCat.ofHom (FiniteField.frobeniusAlgHom k Ω).toRingHom = 𝟙 (CommRingCat.of Ω) := by
    apply CommRingCat.hom_ext
    ext a
    exact (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).apply_symm_apply a
  rw [h, Spec.map_id]

/-- The genuine Frobenius endomorphism of the scheme after extending its finite constants. -/
def constantBaseChangeFrobenius : Y ⟶ Y :=
  (Y).finiteFieldFrobenius k ≫ inverseConstantTwist k Ω X

/-- The constructed Frobenius fixes the extended constant base. -/
theorem constantBaseChangeFrobenius_snd :
    constantBaseChangeFrobenius k Ω X ≫ pullback.snd f b = pullback.snd f b := by
  rw [constantBaseChangeFrobenius, inverseConstantTwist, Category.assoc, pullback.lift_snd,
    ← Category.assoc, finiteFieldFrobenius_naturality, Category.assoc,
    frobenius_inverseFrobeniusOnConstants, Category.comp_id]

/-- Its first projection is Frobenius on the original scheme. -/
theorem constantBaseChangeFrobenius_fst :
    constantBaseChangeFrobenius k Ω X ≫ pullback.fst f b =
      pullback.fst f b ≫ X.finiteFieldFrobenius k := by
  rw [constantBaseChangeFrobenius, inverseConstantTwist, Category.assoc, pullback.lift_fst]
  exact finiteFieldFrobenius_naturality Y k X (pullback.fst f b)

/-- On actual stalks, the Frobenius after base change has zero cotangent map. -/
theorem constantBaseChangeFrobenius_map_maximalIdeal_le_sq (x : ↥(Y : Scheme)) :
    (IsLocalRing.maximalIdeal
      ((Y).presheaf.stalk ((constantBaseChangeFrobenius k Ω X).base x))).map
        ((constantBaseChangeFrobenius k Ω X).stalkMap x).hom ≤
      IsLocalRing.maximalIdeal ((Y).presheaf.stalk x) ^ 2 := by
  change (IsLocalRing.maximalIdeal _).map
    (((Y).finiteFieldFrobenius k ≫ inverseConstantTwist k Ω X).stalkMap x).hom ≤ _
  rw [Hom.stalkMap_comp]
  change (IsLocalRing.maximalIdeal _).map
    ((((Y).finiteFieldFrobenius k).stalkMap x).hom.comp
      ((inverseConstantTwist k Ω X).stalkMap (((Y).finiteFieldFrobenius k) x)).hom) ≤ _
  rw [← Ideal.map_map]
  exact (Ideal.map_mono (IsLocalRing.map_maximalIdeal_le _)).trans
    (finiteFieldFrobenius_map_maximalIdeal_le_sq Y k x)

end AlgebraicGeometry.Scheme
