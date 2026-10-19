/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Finiteness.Basic
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.CompactModule

/-!
# Finite integral completions for arbitrary finite extensions

Compactness of the actual upper integer ring supplies its finite generation over
the open lower integer ring. Separability is unnecessary.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place WithZero

namespace FunctionField

variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L]

/-- The actual integral completed extension is finite for every finite extension
of global function fields, including purely inseparable extensions. -/
theorem moduleFinite_adicCompletionIntegers (w : Place k L) :
    Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers := by
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfunctionL : FunctionField k L := presentation.property.2
  let hRankOne : (Valued.v : Valuation (w.restrict K).adicCompletion ℤᵐ⁰).RankOne :=
    Place.kw_ffgc_rankOne_adicCompletion (w.restrict K)
  let hNormed : NontriviallyNormedField (w.restrict K).adicCompletion :=
    Valued.toNontriviallyNormedField (w.restrict K).adicCompletion ℤᵐ⁰
  let f : w.adicCompletionIntegers →ₗ[(w.restrict K).adicCompletionIntegers]
      w.adicCompletion :=
    (IsScalarTower.toAlgHom (w.restrict K).adicCompletionIntegers
      w.adicCompletionIntegers w.adicCompletion).toLinearMap
  have hcompact : IsCompact (f.range : Set w.adicCompletion) := by
    change IsCompact (Set.range fun x : w.adicCompletionIntegers => (x : w.adicCompletion))
    simpa only [Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq] using isCompact_localIntegers w
  have hnoetherian :
      IsNoetherianRing (w.restrict K).adicCompletionIntegers.toSubring :=
    inferInstanceAs (IsNoetherianRing (w.restrict K).adicCompletionIntegers)
  have htower : IsScalarTower (w.restrict K).adicCompletionIntegers.toSubring
      (w.restrict K).adicCompletion w.adicCompletion :=
    Place.kw_ffgc_isScalarTower_integersCompletionCompletion K w
  have hfinite : Module.Finite (w.restrict K).adicCompletionIntegers f.range :=
    LocalFieldTheory.moduleFinite_of_isCompact_of_isOpen
      (K := (w.restrict K).adicCompletion) (E := w.adicCompletion)
      (moduleAE := inferInstanceAs (Module (w.restrict K).adicCompletionIntegers
        w.adicCompletion)) (towerAKE := htower)
      (w.restrict K).adicCompletionIntegers.toSubring f.range
      (Valued.isOpen_valuationSubring (w.restrict K).adicCompletion) hcompact
  exact Module.Finite.equiv (LinearEquiv.ofInjective f Subtype.val_injective).symm

end FunctionField
