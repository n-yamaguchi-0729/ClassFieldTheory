/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Adele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore

/-!
# Principal adeles

The diagonal map on the entire field reuses the already proved finite support
of nonzero principal ideles. Its restriction to units is the principal idele map.
-/

noncomputable section

namespace FunctionField.AdeleRing

variable (k K : Type*) [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The diagonal ring homomorphism into the all-place completed adeles. -/
def principalAdele : K →+* AdeleRing k K where
  toFun x := ⟨fun v => algebraMap K v.adicCompletion x, by
    by_cases hx : x = 0
    · subst x
      exact Filter.Eventually.of_forall fun v => by
        change algebraMap K v.adicCompletion 0 ∈ v.adicCompletionIntegers
        rw [map_zero]
        exact v.adicCompletionIntegers.zero_mem
    · exact (IdeleGroup.principalIdele k K (Units.mk0 x hx)).2.mono fun v hv => hv.1⟩
  map_zero' := by
    apply RestrictedProduct.ext
    intro v
    exact map_zero (algebraMap K v.adicCompletion)
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact map_one (algebraMap K v.adicCompletion)
  map_add' x y := by
    apply RestrictedProduct.ext
    intro v
    exact map_add (algebraMap K v.adicCompletion) x y
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro v
    exact map_mul (algebraMap K v.adicCompletion) x y

variable {k K}

@[simp]
theorem component_principalAdele (x : K) (v : AlgebraicCurve.Place k K) :
    component v (principalAdele k K x) = algebraMap K v.adicCompletion x :=
  rfl

/-- The adelic diagonal map and the idelic diagonal map agree on units. -/
theorem unitsEquivIdele_principalAdele (x : Kˣ) :
    (unitsEquivIdele (k := k) (K := K))
      (Units.map (principalAdele k K).toMonoidHom x) = IdeleGroup.principalIdele k K x := by
  apply IdeleGroup.ext
  intro v
  apply Units.ext
  rfl

/-- The diagonal embedding is faithful, by evaluation at an actual place. -/
theorem principalAdele_injective [PerfectField k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K] :
    Function.Injective (principalAdele k K) := by
  obtain ⟨v⟩ := FunctionField.nonempty_place k K
  intro x y h
  exact (algebraMap K v.adicCompletion).injective (congrArg (component v) h)

end FunctionField.AdeleRing
