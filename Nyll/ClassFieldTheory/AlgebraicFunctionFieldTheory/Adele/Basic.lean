/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-!
# Adeles over all places

These adeles use the completed fields at every place, including infinity. The
idele group already constructed from local units is identified with their units
by Mathlib's restricted-product equivalence.
-/

open scoped RestrictedProduct

noncomputable section

namespace FunctionField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- The ring of completed adeles at all places trivial on `k`. -/
abbrev AdeleRing :=
  Πʳ v : AlgebraicCurve.Place k K, [v.adicCompletion, v.adicCompletionIntegers]

namespace AdeleRing

variable {k K}

/-- Evaluation in one completed field. -/
def component (v : AlgebraicCurve.Place k K) : AdeleRing k K →+* v.adicCompletion :=
  RestrictedProduct.evalRingHom (fun w : AlgebraicCurve.Place k K => w.adicCompletion) v

@[ext]
theorem ext {a b : AdeleRing k K}
    (h : ∀ v : AlgebraicCurve.Place k K, component v a = component v b) : a = b :=
  RestrictedProduct.ext _ _ h

/-- Units in the all-place adele ring are exactly the all-place ideles. -/
def unitsEquivIdele : (AdeleRing k K)ˣ ≃* IdeleGroup k K :=
  RestrictedProduct.unitsEquiv
    (B := fun v : AlgebraicCurve.Place k K => v.adicCompletionIntegers)
    (fun v : AlgebraicCurve.Place k K => v.adicCompletion)

@[simp]
theorem coe_unitsEquivIdele_component (a : (AdeleRing k K)ˣ)
    (v : AlgebraicCurve.Place k K) :
    ((unitsEquivIdele (k := k) (K := K) a) v : v.adicCompletion) = component v a.val :=
  rfl

end AdeleRing

end FunctionField
