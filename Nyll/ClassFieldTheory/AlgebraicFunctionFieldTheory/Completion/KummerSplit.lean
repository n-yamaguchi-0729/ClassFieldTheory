/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.SplitGenerator
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Splitting of a Kummer extension at an actual place

If a generating radical has a root in the base completion, every conjugate
root lies there because the roots of unity already lie in the base field.
The actual decomposition group therefore fixes the generating radical and
is trivial. This computes the completed degree and gives actual norm preimages.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- A local root makes the actual completion of a one-radical Kummer extension
have degree one. The decomposition group is killed on its actual generator. -/
theorem completion_finrank_eq_one_of_kummer_root (w : Place k L) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) (β : L)
    (hβ : β ^ (n : ℕ) = algebraMap K L (a : K))
    (hgen : Algebra.adjoin K {β} = ⊤)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (x : (w.restrict K).adicCompletion) ^ (n : ℕ) =
      algebraMap K (w.restrict K).adicCompletion (a : K)) :
    Module.finrank (w.restrict K).adicCompletion w.adicCompletion = 1 := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let aKW : Algebra K w.adicCompletion :=
    ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
  have hKLW : IsScalarTower K L w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKVW : IsScalarTower K (w.restrict K).adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq
      (fun z => Place.adicCompletionComap_algebraMap_algebraMap K w z)
  obtain ⟨ζ, hζ⟩ := hmu
  have hζW : IsPrimitiveRoot (algebraMap K w.adicCompletion ζ) (n : ℕ) :=
    (isPrimitiveRoot_of_mem_primitiveRoots hζ).map_of_injective
      (algebraMap K w.adicCompletion).injective
  have hbpow : (algebraMap L w.adicCompletion β) ^ (n : ℕ) =
      algebraMap K w.adicCompletion (a : K) := by
    rw [← map_pow, hβ, ← IsScalarTower.algebraMap_apply K L w.adicCompletion]
  have hxpow : (algebraMap (w.restrict K).adicCompletion w.adicCompletion
      (x : (w.restrict K).adicCompletion)) ^ (n : ℕ) =
      algebraMap K w.adicCompletion (a : K) := by
    rw [← map_pow, hx,
      ← IsScalarTower.algebraMap_apply K (w.restrict K).adicCompletion w.adicCompletion]
  have hroot : (algebraMap L w.adicCompletion β /
      algebraMap (w.restrict K).adicCompletion w.adicCompletion
        (x : (w.restrict K).adicCompletion)) ^ (n : ℕ) = 1 := by
    rw [div_pow, hbpow, hxpow,
      div_self ((map_ne_zero (algebraMap K w.adicCompletion)).mpr a.ne_zero)]
  obtain ⟨i, _, hi⟩ := hζW.eq_pow_of_pow_eq_one hroot
  have hlocal : ∃ c : (w.restrict K).adicCompletion,
      algebraMap (w.restrict K).adicCompletion w.adicCompletion c =
        algebraMap L w.adicCompletion β := by
    refine ⟨(algebraMap K (w.restrict K).adicCompletion ζ) ^ i * x, ?_⟩
    rw [map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply K (w.restrict K).adicCompletion w.adicCompletion]
    exact ((div_eq_iff ((map_ne_zero
      (algebraMap (w.restrict K).adicCompletion w.adicCompletion)).mpr x.ne_zero)).mp
        hi.symm).symm
  obtain ⟨c, hc⟩ := hlocal
  exact completion_finrank_eq_one_of_generator w β hgen c hc

/-- A local radical root gives a preimage for every element under the actual
completed norm: apply the base inclusion in the now degree-one extension. -/
theorem localNorm_surjective_of_kummer_root (w : Place k L) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) (β : L)
    (hβ : β ^ (n : ℕ) = algebraMap K L (a : K))
    (hgen : Algebra.adjoin K {β} = ⊤)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (x : (w.restrict K).adicCompletion) ^ (n : ℕ) =
      algebraMap K (w.restrict K).adicCompletion (a : K)) :
    Function.Surjective (localNorm (K := K) w) := by
  exact localNorm_surjective_of_completion_finrank_eq_one w
    (completion_finrank_eq_one_of_kummer_root w n hmu a β hβ hgen x hx)

end FunctionField.IdeleGroup
