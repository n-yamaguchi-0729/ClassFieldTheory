/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FinitePlaceContraction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes

/-!
# A finite set controlling the ramification and values of a finite stage

Outside the contracted exceptional set, the finite extension is unramified
and all values of a specified finite family are units at every place above.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace ClassFieldTheory.Brauer

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem finite_places_valuation_ne_one (a : Lˣ) :
    {w : HeightOneSpectrum (𝓞 L) | w.valuation L (a : L) ≠ 1}.Finite := by
  let x : FiniteIdeleGroup L := IdeleGroup.finiteCoordinates (IdeleGroup.principalIdele L a)
  have hfinite :
      {w : HeightOneSpectrum (𝓞 L) | x w ∉ (w.adicCompletionIntegers L).units}.Finite :=
    Filter.eventually_cofinite.mp (FiniteIdeleGroup.eventually_mem_localUnits x)
  refine hfinite.subset ?_
  intro w hw hunit
  have hval : Valued.v
      ((IdeleGroup.finiteComponent w (IdeleGroup.principalIdele L a) :
        (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hunit
  rw [IdeleGroup.finiteComponent_principalIdele,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hval
  exact hw hval

variable (K) in
/-- A finite family of field units is integral everywhere above each finite
place outside a single finite set, and the same set excludes all ramification. -/
theorem exists_finite_exceptional_places {I : Type*} [Finite I] (a : I → Lˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ w : HeightOneSpectrum (𝓞 L), finitePlaceBelow (K := K) w ∉ S →
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ∧ (∀ i, w.valuation L (a i : L) = 1) := by
  classical
  let B : Set (HeightOneSpectrum (𝓞 L)) :=
    {w | ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal} ∪
      ⋃ i : I, {w | w.valuation L (a i : L) ≠ 1}
  have hB : B.Finite :=
    (AlgebraicNumberTheory.Ramification.finite_ramified_heightOne_primes (𝓞 K) (𝓞 L)).union
      (Set.finite_iUnion fun i => finite_places_valuation_ne_one (a i))
  let hS := hB.image (finitePlaceBelow (K := K))
  refine ⟨hS.toFinset, fun w hw => ?_⟩
  have hwB : w ∉ B := fun hw' => hw (hS.mem_toFinset.mpr ⟨w, hw', rfl⟩)
  constructor
  · by_contra hRam
    exact hwB (Set.mem_union_left _ hRam)
  · intro i
    by_contra hi
    exact hwB (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hi⟩))

end ClassFieldTheory.Brauer
