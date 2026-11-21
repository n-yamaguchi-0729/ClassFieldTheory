/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.DirectSum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.RealPlace
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalInvariant

/-! # The sum of the actual local Brauer invariants -/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField GlobalClassFieldTheory.Reciprocity LocalFieldTheory
open scoped BigOperators DirectSum NumberField ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The arithmetic Brauer invariant on the normalized absolute-value completion. -/
def finitePlaceNormalizedBrauerInvariantEquiv (v : HeightOneSpectrum (𝓞 K)) :
    Br (HeightOneSpectrum.adicAbv K v).Completion ≃+ AddCircle (1 : ℚ) := by
  let F := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField F := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact localBrauerInvariantEquiv F

/-- The arithmetic local invariant on the original adic completion, using
its canonical comparison with the normalized absolute-value completion. -/
def finitePlaceBrauerInvariantEquiv (v : HeightOneSpectrum (𝓞 K)) :
    Br (v.adicCompletion K) ≃+ AddCircle (1 : ℚ) :=
  (restrictEquiv (finitePlaceCompletionAlgEquiv v).symm.toRingEquiv).trans
    (finitePlaceNormalizedBrauerInvariantEquiv K v)

/-- The finite-place invariant evaluates through the original completion isomorphism. -/
theorem finitePlaceBrauerInvariantEquiv_apply (v : HeightOneSpectrum (𝓞 K))
    (x : Br (v.adicCompletion K)) :
    finitePlaceBrauerInvariantEquiv K v x =
      finitePlaceNormalizedBrauerInvariantEquiv K v
        (restrictEquiv (finitePlaceCompletionAlgEquiv v).symm.toRingEquiv x) := by
  exact AddEquiv.trans_apply _ _ x

/-- The local invariant on the actual completion, with zero at complex places. -/
def placeBrauerInvariant (v : Place K) : Br (placeCompletion K v) →+ AddCircle (1 : ℚ) := by
  classical
  cases v with
  | inl v => exact (finitePlaceBrauerInvariantEquiv K v).toAddMonoidHom
  | inr v => exact if h : v.IsReal then realPlaceBrauerInvariant h else 0

/-- Sum the arithmetic invariants of the actual finitely supported local classes. -/
def sumLocalInv : (⨁ v : Place K, Br (placeCompletion K v)) →+ AddCircle (1 : ℚ) := by
  classical
  exact DirectSum.toAddMonoid (placeBrauerInvariant K)

open scoped Classical in
/-- On the summand at a place the sum is the original local invariant. -/
theorem sumLocalInv_single (v : Place K) (x : Br (placeCompletion K v)) :
    sumLocalInv K (DirectSum.of (fun w : Place K => Br (placeCompletion K w)) v x) =
      placeBrauerInvariant K v x := by
  classical
  exact DirectSum.toAddMonoid_of (placeBrauerInvariant K) v x

open scoped Classical in
/-- The actual sum is the finite sum of the invariant of each nonzero coordinate. -/
theorem sumLocalInv_apply (x : ⨁ v : Place K, Br (placeCompletion K v)) :
    sumLocalInv K x = ∑ v ∈ x.support, placeBrauerInvariant K v (x v) := by
  classical
  calc
    _ = sumLocalInv K (∑ v ∈ x.support,
        DirectSum.of (fun w : Place K => Br (placeCompletion K w)) v (x v)) :=
      congrArg (sumLocalInv K) (DirectSum.sum_support_of x).symm
    _ = _ := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun v _ => sumLocalInv_single K v (x v))

/-- Every number field has a finite place, by choosing a place above the prime two. -/
theorem finitePlace_nonempty : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  let p : HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨2, Nat.prime_two⟩
  let : p.asIdeal.IsMaximal := p.isMaximal
  obtain ⟨q, hq, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) p.asIdeal
  let : q.IsMaximal := hq
  exact ⟨⟨q, hq.isPrime, Ideal.IsMaximal.ne_bot_of_isIntegral_int q⟩⟩

/-- Every rational-circle value occurs by using the invariant inverse at one finite place. -/
theorem sumLocalInv_surjective : Function.Surjective (sumLocalInv K) := by
  classical
  obtain ⟨v⟩ := finitePlace_nonempty K
  intro x
  let e := finitePlaceBrauerInvariantEquiv K v
  refine ⟨DirectSum.of (fun w : Place K => Br (placeCompletion K w)) (Sum.inl v) (e.symm x), ?_⟩
  rw [sumLocalInv_single]
  exact e.apply_symm_apply x

end ClassFieldTheory.Brauer
