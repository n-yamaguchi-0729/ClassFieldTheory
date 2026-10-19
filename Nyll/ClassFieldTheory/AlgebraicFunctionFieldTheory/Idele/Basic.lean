/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Completion
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Ideles over all places of a function field

The index type is the existing `AlgebraicCurve.Place k K`. In particular, places
above infinity in an affine presentation are included. The restricted factors
are the multiplicative groups of the existing completions, with respect to the
unit groups of their valuation subrings.
-/

open scoped RestrictedProduct

noncomputable section

namespace FunctionField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- The idele group over all places of `K` trivial on the constant field `k`. -/
abbrev IdeleGroup :=
  Πʳ v : AlgebraicCurve.Place k K, [v.adicCompletionˣ, v.adicCompletionIntegers.units]

namespace IdeleGroup

variable {k K}

/-- Evaluation at a place. -/
def component (v : AlgebraicCurve.Place k K) :
    IdeleGroup k K →* v.adicCompletionˣ :=
  RestrictedProduct.evalMonoidHom
    (fun w : AlgebraicCurve.Place k K => w.adicCompletionˣ) v

@[simp]
theorem component_apply (v : AlgebraicCurve.Place k K) (a : IdeleGroup k K) :
    component v a = a v :=
  rfl

/-- Two ideles agree if their components agree at every place. -/
@[ext]
theorem ext {a b : IdeleGroup k K}
    (h : ∀ v : AlgebraicCurve.Place k K, component v a = component v b) : a = b :=
  RestrictedProduct.ext _ _ h

/-- The local components are integral units outside a finite set of places. -/
theorem eventually_mem_localUnits (a : IdeleGroup k K) :
    ∀ᶠ v in Filter.cofinite, a v ∈ v.adicCompletionIntegers.units :=
  a.2

open scoped Classical in
/-- Insert a local unit at one place and use `1` at all other places. -/
def placeIdele (v : AlgebraicCurve.Place k K) :
    v.adicCompletionˣ →* IdeleGroup k K :=
  RestrictedProduct.mulSingleMonoidHom
    (fun w : AlgebraicCurve.Place k K => w.adicCompletionIntegers.units) v

@[simp]
theorem component_placeIdele_same (v : AlgebraicCurve.Place k K)
    (x : v.adicCompletionˣ) : component v (placeIdele v x) = x := by
  classical
  exact RestrictedProduct.mulSingle_eq_same
    (fun w : AlgebraicCurve.Place k K => w.adicCompletionIntegers.units) v x

@[simp]
theorem component_placeIdele_of_ne (v w : AlgebraicCurve.Place k K)
    (x : v.adicCompletionˣ) (h : w ≠ v) :
    component w (placeIdele v x) = 1 := by
  classical
  exact RestrictedProduct.mulSingle_eq_of_ne
    (fun u : AlgebraicCurve.Place k K => u.adicCompletionIntegers.units) x h

/-- The local inclusion is injective, since its supporting component recovers the input. -/
theorem placeIdele_injective (v : AlgebraicCurve.Place k K) :
    Function.Injective (placeIdele v) := by
  intro x y h
  have hc := congrArg (component v) h
  simpa only [component_placeIdele_same] using hc

end IdeleGroup

end FunctionField
