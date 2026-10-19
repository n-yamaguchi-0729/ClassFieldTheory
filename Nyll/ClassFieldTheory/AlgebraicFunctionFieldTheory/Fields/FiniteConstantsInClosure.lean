/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite constant fields inside a separably closed ambient field

For every positive degree, the existing finite-field extension embeds into the
ambient separably closed field. Its actual image is a finite Galois intermediate
field of the requested degree. Thus the subsequent constant compositum can be
formed inside the original ambient field, with no assumed extension data.
-/

noncomputable section

namespace FunctionField

variable (k Ω : Type*) [Field k] [Finite k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (n : ℕ) [NeZero n]

/-- An actual degree-`n` finite constant field inside the separably closed
ambient field, packaged with its finite Galois structure. -/
def finiteConstantsInClosure : FiniteGaloisIntermediateField k Ω := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  let i : FiniteField.Extension k (ringChar k) n →ₐ[k] Ω := IsSepClosed.lift
  let e : FiniteField.Extension k (ringChar k) n ≃ₐ[k] i.fieldRange := i.equivFieldRange
  exact
    { toIntermediateField := i.fieldRange
      finiteDimensional := e.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv e }

/-- The image of the chosen finite-field embedding has the requested degree. -/
theorem finrank_finiteConstantsInClosure :
    Module.finrank k (finiteConstantsInClosure k Ω n) = n := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  let i : FiniteField.Extension k (ringChar k) n →ₐ[k] Ω := IsSepClosed.lift
  change Module.finrank k i.fieldRange = n
  rw [← i.equivFieldRange.toLinearEquiv.finrank_eq]
  exact FiniteField.finrank_extension k (ringChar k) n

/-- The constant field constructed in the ambient field is a finite set. -/
theorem finite_finiteConstantsInClosure : Finite (finiteConstantsInClosure k Ω n) :=
  Module.finite_of_finite k

variable {n}

/-- Divisibility of degrees gives actual containment of the finite constant
fields in the fixed ambient field. -/
theorem finiteConstantsInClosure_mono {m : ℕ} [NeZero m] (h : n ∣ m) :
    (finiteConstantsInClosure k Ω n).toIntermediateField ≤
      (finiteConstantsInClosure k Ω m).toIntermediateField := by
  have : Finite (finiteConstantsInClosure k Ω m) := finite_finiteConstantsInClosure k Ω m
  have hdegree : Module.finrank k (finiteConstantsInClosure k Ω n) ∣
      Module.finrank k (finiteConstantsInClosure k Ω m) := by
    rw [finrank_finiteConstantsInClosure, finrank_finiteConstantsInClosure]
    exact h
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdegree
  let j : finiteConstantsInClosure k Ω n →ₐ[k] Ω :=
    (finiteConstantsInClosure k Ω m).toIntermediateField.val.comp f
  have hj : j.fieldRange = (finiteConstantsInClosure k Ω n).toIntermediateField :=
    AlgHom.fieldRange_of_normal j
  intro x hx
  rw [← hj] at hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  exact (f y).2

/-- Inclusion in the actual constant tower is characterized by divisibility
of the requested degrees. -/
theorem finiteConstantsInClosure_le_iff {m : ℕ} [NeZero m] :
    (finiteConstantsInClosure k Ω n).toIntermediateField ≤
        (finiteConstantsInClosure k Ω m).toIntermediateField ↔ n ∣ m := by
  constructor
  · intro h
    have hd := IntermediateField.finrank_dvd_of_le_right h
    rw [finrank_finiteConstantsInClosure, finrank_finiteConstantsInClosure] at hd
    exact hd
  · exact finiteConstantsInClosure_mono k Ω

end FunctionField
