/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basis
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.ExtensionConductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalRamification
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalCompatibility
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Conductor
import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
import Mathlib.Data.Finsupp.Single

/-!
# Actual global and completed local conductors

The local-global Artin theorem identifies the ray norm condition with
the conductors of the actual completed extensions.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace FunctionField.RayClass

open AlgebraicCurve

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L] in
/-- The completed local conductor is detected by the actual global norm
subgroup pulled back along the corresponding one-place idele. -/
theorem localConductorExponent_le_iff_placeNorm (w : Place k L) (n : ℕ) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    have _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    LocalClassFieldTheory.localConductorExponent
      (w.restrict K).adicCompletion w.adicCompletion ≤ n ↔
      localHigherUnitGroup (w.restrict K) n ≤
        (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range.comap
          ((IdeleClassGroup.mk (k := k) (K := K)).comp
            (IdeleGroup.placeIdele (w.restrict K))) := by
  intro hrelation hlocal
  have hlocalArtin := localConductorExponent_le_iff_localArtin (K := K) w n
  dsimp only at hlocalArtin
  rw [hlocalArtin]
  constructor
  · intro h x hx
    apply (abelianFiniteArtin_eq_one_iff_mem_norm k K L _).mp
    exact (localArtin_eq_abelianFiniteArtin_placeIdele k K L w x).symm.trans (h x hx)
  · intro h x hx
    rw [localArtin_eq_abelianFiniteArtin_placeIdele k K L w x]
    exact (abelianFiniteArtin_eq_one_iff_mem_norm k K L _).mpr (h hx)

/-- A modulus bounds the actual norm conductor exactly when it bounds the
conductor of every actual completed extension. -/
theorem extensionConductor_le_iff_localConductor (m : Modulus k K) :
    extensionConductor (k := k) (K := K) (L := L) ≤ m ↔
      ∀ w : Place k L,
        let _ : ValuativeRel (w.restrict K).adicCompletion :=
          placeCompletionValuativeRel (w.restrict K)
        have _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
          placeCompletion_isNonarchimedeanLocalField (w.restrict K)
        LocalClassFieldTheory.localConductorExponent
          (w.restrict K).adicCompletion w.adicCompletion ≤ m (w.restrict K) := by
  rw [extensionConductor_le_iff,
    rayClassSubgroup_le_iff m _ (IdeleClassGroup.isOpen_norm_range (k := k) (K := K) (L := L))]
  constructor
  · intro h w hrelation hlocal
    have hcriterion := localConductorExponent_le_iff_placeNorm (K := K) w (m (w.restrict K))
    dsimp only at hcriterion
    exact hcriterion.mpr (h (w.restrict K))
  · intro h v
    obtain ⟨w, hw⟩ := Place.exists_restrict_eq (M := L) v
    subst v
    have hcriterion := localConductorExponent_le_iff_placeNorm (K := K) w (m (w.restrict K))
    have hbound := h w
    dsimp only at hcriterion hbound
    exact hcriterion.mp hbound

/-- Every coefficient of the actual global conductor is exactly the
conductor exponent of any completed extension above that place. -/
theorem extensionConductor_apply_eq_localConductor (w : Place k L) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    have _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    extensionConductor (k := k) (K := K) (L := L) (w.restrict K) =
      LocalClassFieldTheory.localConductorExponent
        (w.restrict K).adicCompletion w.adicCompletion := by
  intro hrelation hlocal
  classical
  let c := extensionConductor (k := k) (K := K) (L := L)
  let n := LocalClassFieldTheory.localConductorExponent
    (w.restrict K).adicCompletion w.adicCompletion
  have hclocal := (extensionConductor_le_iff_localConductor (L := L) c).mp le_rfl
  have hcriterion := localConductorExponent_le_iff_placeNorm (K := K) w n
  dsimp only at hcriterion
  have hn := hcriterion.mp (le_refl n)
  let m : Modulus k K := c.update (w.restrict K) n
  have hcm : c ≤ m := by
    apply (extensionConductor_le_iff_localConductor (L := L) m).mpr
    intro u hurelation hulocal
    have hucriterion := localConductorExponent_le_iff_placeNorm (K := K) u (m (u.restrict K))
    dsimp only at hucriterion
    apply hucriterion.mpr
    have hmv : m (u.restrict K) =
        if u.restrict K = w.restrict K then n else c (u.restrict K) :=
      Finsupp.update_apply c (w.restrict K) n (u.restrict K)
    rw [hmv]
    by_cases hu : u.restrict K = w.restrict K
    · rw [ite_eq_left hu]
      rw [hu]
      exact hn
    · rw [ite_eq_right hu]
      have hucriterion' := localConductorExponent_le_iff_placeNorm (K := K) u (c (u.restrict K))
      have hubound := hclocal u
      dsimp only at hucriterion' hubound
      exact hucriterion'.mp hubound
  have hmv : m (w.restrict K) = n := by
    change c.update (w.restrict K) n (w.restrict K) = n
    rw [Finsupp.update_apply, ite_eq_left rfl]
  have hwbound := hclocal w
  dsimp only at hwbound
  exact le_antisymm ((hcm (w.restrict K)).trans hmv.le) hwbound

/-- The completed local conductor vanishes outside any admissible modulus. -/
theorem localConductorExponent_eq_zero_of_not_mem_support
    (m : Modulus k K) (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m)
    (w : Place k L) (hw : w.restrict K ∉ m.support) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    have _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    LocalClassFieldTheory.localConductorExponent
      (w.restrict K).adicCompletion w.adicCompletion = 0 := by
  intro hrelation hlocal
  have hbound := (extensionConductor_le_iff_localConductor (L := L) m).mp hm w
  dsimp only at hbound
  rw [Finsupp.notMem_support_iff.mp hw] at hbound
  exact Nat.eq_zero_of_le_zero hbound

/-- Every original place outside an admissible modulus is actually
unramified. This controls the support of the constructed class field. -/
theorem ramificationIndex_eq_one_of_not_mem_support
    (m : Modulus k K) (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m)
    (w : Place k L) (hw : w.restrict K ∉ m.support) : w.ramificationIndex K = 1 := by
  have hcriterion := localConductorExponent_eq_zero_iff_ramificationIndex_eq_one (K := K) w
  have hzero := localConductorExponent_eq_zero_of_not_mem_support m hm w hw
  dsimp only at hcriterion hzero
  exact hcriterion.mp hzero

end FunctionField.RayClass
