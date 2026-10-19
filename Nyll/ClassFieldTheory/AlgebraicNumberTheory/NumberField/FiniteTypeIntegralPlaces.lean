/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.GoodReductionPlaces
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Integral local maps for finitely generated arithmetic models

A finitely generated integer subalgebra of a number field maps into the
integer rings of all but finitely many finite completions. The maps are the
restrictions of the actual field embeddings into those completions.
-/

open scoped NumberField
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace AlgebraicNumberTheory.PrimeSelection

/-- Finite generation gives integral coefficient maps outside finitely many
places, with the original generic coefficient map retained. -/
theorem exists_finite_integral_places
    (K : Type*) [Field K] [NumberField K] (T : Subalgebra ℤ K) (hT : T.FG) :
    ∃ E : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ E →
        ∃ f : T →+* v.adicCompletionIntegers K,
          ∀ t : T, (f t : v.adicCompletion K) =
            algebraMap K (v.adicCompletion K) (t : K) := by
  classical
  obtain ⟨s, hs, hsT⟩ := Subalgebra.fg_def.mp hT
  let E : Set (HeightOneSpectrum (𝓞 K)) :=
    ⋃ x ∈ s, HeightOneSpectrum.Support (𝓞 K) x
  have hE : E.Finite :=
    hs.biUnion fun x _ => HeightOneSpectrum.Support.finite (𝓞 K) x
  refine ⟨hE.toFinset, ?_⟩
  intro v hv
  have hvE : v ∉ E := by simpa only [Set.Finite.mem_toFinset] using hv
  have hgen (x : K) (hx : x ∈ s) :
      (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']
    apply le_of_not_gt
    intro h
    apply hvE
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, h⟩⟩
  let C : Subring K :=
    (v.adicCompletionIntegers K).toSubring.comap
      (algebraMap K (v.adicCompletion K))
  let A : Subalgebra ℤ K :=
    { C.toSubsemiring with
      algebraMap_mem' := fun n => by
        change (n : K) ∈ C
        exact intCast_mem C n }
  have hTA : T ≤ A := by
    rw [← hsT]
    apply Algebra.adjoin_le
    intro x hx
    change algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K
    simpa only [algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using hgen x hx
  let f : T →+* v.adicCompletionIntegers K :=
    { toFun := fun t => ⟨algebraMap K (v.adicCompletion K) t.1, hTA t.2⟩
      map_zero' := Subtype.ext (map_zero (algebraMap K (v.adicCompletion K)))
      map_one' := Subtype.ext (map_one (algebraMap K (v.adicCompletion K)))
      map_add' a b :=
        Subtype.ext (map_add (algebraMap K (v.adicCompletion K)) a.1 b.1)
      map_mul' a b :=
        Subtype.ext (map_mul (algebraMap K (v.adicCompletion K)) a.1 b.1) }
  exact ⟨f, fun _ => rfl⟩

/-- Including the inverse of a nonzero integer in the coefficient ring makes
that integer a unit before choosing a finite place. -/
theorem isUnit_natCast_of_inverse_mem
    (K : Type*) [Field K] [CharZero K] (T : Subalgebra ℤ K)
    (n : ℕ) (hn : n ≠ 0) (hinv : (n : K)⁻¹ ∈ T) : IsUnit (n : T) := by
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨{
    val := (n : T)
    inv := ⟨(n : K)⁻¹, hinv⟩
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · apply Subtype.ext
    change (n : K) * (n : K)⁻¹ = 1
    exact mul_inv_cancel₀ hnK
  · apply Subtype.ext
    change (n : K)⁻¹ * (n : K) = 1
    exact inv_mul_cancel₀ hnK

/-- A finitely generated arithmetic coefficient ring admits an actual integral
map at an unramified degree-one place avoiding specified characteristics. -/
theorem exists_degreeOne_integral_place
    (K : Type*) [Field K] [NumberField K] (T : Subalgebra ℤ K) (hT : T.FG)
    (bad : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ bad ∧
      ∃ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) ∧
        v.asIdeal.inertiaDeg ℤ = 1 ∧ Algebra.IsUnramifiedAt ℤ v.asIdeal ∧
        ∃ f : T →+* v.adicCompletionIntegers K,
          ∀ t : T, (f t : v.adicCompletion K) =
            algebraMap K (v.adicCompletion K) (t : K) := by
  obtain ⟨E, hE⟩ := exists_finite_integral_places K T hT
  obtain ⟨q, hq, hbad, v, hv, hover, hdeg, hur⟩ :=
    exists_unramified_degreeOnePrime_avoiding K bad E
  exact ⟨q, hq, hbad, v, hover, hdeg, hur, hE v hv⟩

end AlgebraicNumberTheory.PrimeSelection
