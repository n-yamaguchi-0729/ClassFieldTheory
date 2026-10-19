/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Topology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Compact

/-!
# The finite degree-zero part of a ray class group

Congruence ideles have zero divisor and hence zero degree. Degree descends to the
full ray quotient. Its kernel is a discrete image of the compact degree-zero idele
class group, and is therefore finite. The full ray class group retains its degree part.
-/

noncomputable section

namespace FunctionField.RayClass

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Congruence ideles have degree zero after passage to idele classes. -/
theorem rayClassSubgroup_le_degreeZero (m : Modulus k K) :
    rayClassSubgroup m ≤ IdeleClassGroup.degreeZero (k := k) (K := K) := by
  rintro c ⟨a, ha, rfl⟩
  rw [IdeleClassGroup.mem_degreeZero, IdeleClassGroup.degree_mk]
  apply Multiplicative.ext
  rw [IdeleGroup.degree_apply,
    (IdeleGroup.divisor_eq_one_iff a).2 (congruenceSubgroup_le_integralSubgroup m ha)]
  exact map_zero (AlgebraicCurve.Divisor.degree (K := k) (F := K))

/-- The surviving degree map on the full ray class group. -/
def degree (m : Modulus k K) : RayClassGroup m →* Multiplicative ℤ :=
  QuotientGroup.lift (rayClassSubgroup m) (IdeleClassGroup.degree (k := k) (K := K))
    (fun _ hc => rayClassSubgroup_le_degreeZero m hc)

@[simp]
theorem degree_mk (m : Modulus k K) (c : IdeleClassGroup k K) :
    degree m (QuotientGroup.mk' (rayClassSubgroup m) c) =
      IdeleClassGroup.degree (k := k) (K := K) c :=
  rfl

/-- The degree-zero ray classes are exactly the image of degree-zero idele classes. -/
theorem degree_ker_eq_image (m : Modulus k K) :
    ((degree m).ker : Set (RayClassGroup m)) =
      (QuotientGroup.mk' (rayClassSubgroup m)) ''
        (IdeleClassGroup.degreeZero (k := k) (K := K) : Set (IdeleClassGroup k K)) := by
  ext r
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (rayClassSubgroup m) r
  constructor
  · intro hc
    exact ⟨c, hc, rfl⟩
  · rintro ⟨d, hd, hdc⟩
    rw [← hdc]
    exact hd

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The degree-zero part of every all-place ray class group is finite. -/
theorem finite_degreeZero (m : Modulus k K) : Finite (degree m).ker := by
  have : DiscreteTopology (RayClassGroup m) :=
    QuotientGroup.discreteTopology (isOpen_rayClassSubgroup m)
  have hc : IsCompact ((degree m).ker : Set (RayClassGroup m)) := by
    rw [degree_ker_eq_image]
    exact IdeleClassGroup.isCompact_degreeZero.image QuotientGroup.continuous_mk
  have : CompactSpace (degree m).ker := isCompact_iff_compactSpace.mp hc
  exact finite_of_compact_of_discrete

end FunctionField.RayClass
