/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalCompatibility
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalFactor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalInertia
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSplitting
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.UnramifiedFrobenius

/-!
# Decomposition, inertia and splitting under the global Artin map
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The local-global factor is the inclusion of the actual decomposition group. -/
theorem localGlobalArtinFactor_eq_subtype (w : Place k L) :
    localGlobalArtinFactor (K := K) w =
      (IdeleGroup.decompositionGroup (K := K) w).subtype := by
  apply MonoidHom.ext
  intro σ
  obtain ⟨x, rfl⟩ := localDecompositionArtin_surjective (K := K) w σ
  exact (localGlobalArtinFactor_apply_localDecompositionArtin w x).trans
    (localArtin_eq_abelianFiniteArtin_placeIdele k K L w x).symm

/-- The full local subgroup has global Artin image equal to the actual decomposition group. -/
theorem abelianFiniteArtin_placeIdele_range (w : Place k L) :
    ((abelianFiniteArtin k K L).comp
      ((IdeleClassGroup.mk (k := k) (K := K)).comp
        (IdeleGroup.placeIdele (w.restrict K)))).range =
      IdeleGroup.decompositionGroup (K := K) w := by
  have hhom : (abelianFiniteArtin k K L).comp
      ((IdeleClassGroup.mk (k := k) (K := K)).comp
        (IdeleGroup.placeIdele (w.restrict K))) = localArtin (K := K) w := by
    apply MonoidHom.ext
    intro x
    exact (localArtin_eq_abelianFiniteArtin_placeIdele k K L w x).symm
  rw [hhom, localArtin_range]

/-- A place splits completely exactly when global reciprocity kills every
one-place idele there. -/
theorem abelianFiniteArtin_placeIdele_trivial_iff_completelySplit (w : Place k L) :
    (∀ x : (w.restrict K).adicCompletionˣ,
      abelianFiniteArtin k K L
        (IdeleClassGroup.mk (k := k) (K := K)
          (IdeleGroup.placeIdele (w.restrict K) x)) = 1) ↔
      w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1 := by
  simp only [← localArtin_eq_abelianFiniteArtin_placeIdele k K L w]
  exact localArtin_trivial_iff_completelySplit (K := K) w

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- Local units have global image equal to actual residue inertia, included
in the global Galois group. -/
theorem abelianFiniteArtin_placeIdele_units (w : Place k L) :
    (RayClass.localHigherUnitGroup (w.restrict K) 0).map
      ((abelianFiniteArtin k K L).comp
        ((IdeleClassGroup.mk (k := k) (K := K)).comp
          (IdeleGroup.placeIdele (w.restrict K)))) =
      (IdeleGroup.decompositionResidueAut (K := K) w).ker.map
        (IdeleGroup.decompositionGroup (K := K) w).subtype := by
  have hhom : (abelianFiniteArtin k K L).comp
      ((IdeleClassGroup.mk (k := k) (K := K)).comp
        (IdeleGroup.placeIdele (w.restrict K))) = localArtin (K := K) w := by
    apply MonoidHom.ext
    intro x
    exact (localArtin_eq_abelianFiniteArtin_placeIdele k K L w x).symm
  rw [hhom, localArtin_units_eq_residue_ker_map]

/-- At an unramified place the global symbol is the local-order power of
the arithmetic Frobenius acting on the original residue field. -/
theorem abelianFiniteArtin_placeIdele_eq_unramifiedFrobenius_zpow
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ) :
    abelianFiniteArtin k K L
      (IdeleClassGroup.mk (k := k) (K := K)
        (IdeleGroup.placeIdele (w.restrict K) x)) =
      (unramifiedDecompositionFrobenius (K := K) w he).val ^
        (IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  rw [← localArtin_eq_abelianFiniteArtin_placeIdele k K L w x]
  exact congrArg (fun σ : IdeleGroup.decompositionGroup (K := K) w => σ.val)
    (localDecompositionArtin_eq_unramifiedFrobenius_zpow w he x)

/-- At an unramified place the order of the global symbol of a uniformizer
is the residue degree. -/
theorem orderOf_abelianFiniteArtin_uniformizer
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (IdeleGroup.localOrder (w.restrict K) x).toAdd = 1) :
    orderOf (abelianFiniteArtin k K L
      (IdeleClassGroup.mk (k := k) (K := K)
        (IdeleGroup.placeIdele (w.restrict K) x))) = w.inertiaDeg K := by
  rw [abelianFiniteArtin_placeIdele_eq_unramifiedFrobenius_zpow w he x, hx, zpow_one]
  exact (orderOf_injective
    (IdeleGroup.decompositionGroup (K := K) w).subtype Subtype.val_injective
      (unramifiedDecompositionFrobenius (K := K) w he)).trans
    (orderOf_unramifiedDecompositionFrobenius w he)

/-- An unramified place splits completely precisely when the global
symbol of a uniformizer is trivial. -/
theorem abelianFiniteArtin_uniformizer_eq_one_iff
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (IdeleGroup.localOrder (w.restrict K) x).toAdd = 1) :
    abelianFiniteArtin k K L
        (IdeleClassGroup.mk (k := k) (K := K)
          (IdeleGroup.placeIdele (w.restrict K) x)) = 1 ↔ w.inertiaDeg K = 1 := by
  rw [← orderOf_eq_one_iff, orderOf_abelianFiniteArtin_uniformizer w he x hx]

/-- At an unramified place, a one-place idele class is a global norm
exactly when its local order is divisible by the residue degree. -/
theorem placeIdele_mem_norm_range_iff_inertiaDeg_dvd
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ) :
    IdeleClassGroup.mk (k := k) (K := K)
        (IdeleGroup.placeIdele (w.restrict K) x) ∈
      (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range ↔
        (w.inertiaDeg K : ℤ) ∣ (IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  rw [← abelianFiniteArtin_eq_one_iff_mem_norm,
    ← localArtin_eq_abelianFiniteArtin_placeIdele k K L w x,
    localArtin_eq_one_iff, mem_localNorm_range_iff_inertiaDeg_dvd w he x]

end FunctionField
