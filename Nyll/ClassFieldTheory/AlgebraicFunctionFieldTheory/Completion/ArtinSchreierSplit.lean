/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.SplitGenerator
import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter

/-!
# Splitting an Artin–Schreier extension in a completion

Two Artin–Schreier roots differ by an element of the prime field.
A root in the base completion therefore places the actual generating root
in that completion. The completed degree is one and its norm is onto.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- A local Artin–Schreier root makes the actual completed extension trivial. -/
theorem completion_finrank_eq_one_of_artinSchreier_root
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (w : Place k L) (a : K) (β : L)
    (hβ : β ^ p - β = algebraMap K L a) (hgen : Algebra.adjoin K {β} = ⊤)
    (x : (w.restrict K).adicCompletion)
    (hx : x ^ p - x = algebraMap K (w.restrict K).adicCompletion a) :
    Module.finrank (w.restrict K).adicCompletion w.adicCompletion = 1 := by
  let aKW : Algebra K w.adicCompletion :=
    ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
  have hKLW : IsScalarTower K L w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKVW : IsScalarTower K (w.restrict K).adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq
      (fun z => Place.adicCompletionComap_algebraMap_algebraMap K w z)
  have hcharW : CharP w.adicCompletion p :=
    (Algebra.charP_iff K w.adicCompletion p).mp inferInstance
  have hcharV : CharP (w.restrict K).adicCompletion p :=
    (Algebra.charP_iff K (w.restrict K).adicCompletion p).mp inferInstance
  have hb : (algebraMap L w.adicCompletion β) ^ p -
      algebraMap L w.adicCompletion β = algebraMap K w.adicCompletion a := by
    rw [← map_pow, ← map_sub, hβ, ← IsScalarTower.algebraMap_apply K L w.adicCompletion]
  have hxW : (algebraMap (w.restrict K).adicCompletion w.adicCompletion x) ^ p -
      algebraMap (w.restrict K).adicCompletion w.adicCompletion x =
      algebraMap K w.adicCompletion a := by
    rw [← map_pow, ← map_sub, hx,
      ← IsScalarTower.algebraMap_apply K (w.restrict K).adicCompletion w.adicCompletion]
  have hd : (algebraMap L w.adicCompletion β -
      algebraMap (w.restrict K).adicCompletion w.adicCompletion x) ^ p =
      algebraMap L w.adicCompletion β -
        algebraMap (w.restrict K).adicCompletion w.adicCompletion x := by
    rw [sub_pow_char]
    linear_combination hb - hxW
  obtain ⟨z, hz⟩ := ArtinSchreierTheory.exists_zmod_of_pow_eq p w.adicCompletion hd
  apply completion_finrank_eq_one_of_generator w β hgen
    (x + (ZMod.castHom (dvd_refl p) (w.restrict K).adicCompletion) z)
  rw [map_add]
  have hcast : algebraMap (w.restrict K).adicCompletion w.adicCompletion
      ((ZMod.castHom (dvd_refl p) (w.restrict K).adicCompletion) z) =
      (ZMod.castHom (dvd_refl p) w.adicCompletion) z := by
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
  rw [hcast, hz]
  ring

/-- A local Artin–Schreier root supplies all actual local norm preimages. -/
theorem localNorm_surjective_of_artinSchreier_root
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (w : Place k L) (a : K) (β : L)
    (hβ : β ^ p - β = algebraMap K L a) (hgen : Algebra.adjoin K {β} = ⊤)
    (x : (w.restrict K).adicCompletion)
    (hx : x ^ p - x = algebraMap K (w.restrict K).adicCompletion a) :
    Function.Surjective (localNorm (K := K) w) :=
  localNorm_surjective_of_completion_finrank_eq_one w
    (completion_finrank_eq_one_of_artinSchreier_root p w a β hβ hgen x hx)

end FunctionField.IdeleGroup
