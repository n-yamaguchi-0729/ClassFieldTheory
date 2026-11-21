/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FinitePlaceInvariantRestriction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FullIdeleClassRestriction

/-! # Restriction of the arithmetic invariant of a single-place idèle class -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Martinet.Shafarevich
open IsDedekindDomain NumberField
open scoped BigOperators DirectSum NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Field E] [NumberField E] [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]
  [FiniteDimensional K M] [FiniteDimensional M E]
  [FiniteDimensional K E] [IsGalois K E] [IsGalois M E]

open scoped Classical in
/-- The sum of the restrictions of a one-place idèle cocycle is multiplied by
the global degree, using every completed place in the actual restriction fiber. -/
theorem fullIdeleBrauerInvariantSum_baseRestriction_single
    (v : HeightOneSpectrum (𝓞 K)) (b : Br (v.adicCompletion K))
    (x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2)
    (hx : fullIdeleBrauerTuple K E x =
      DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b) :
    fullIdeleBrauerInvariantSum M E (fullIdeleH2BaseRestriction (M := M) x) =
      Module.finrank K M • finitePlaceBrauerInvariantEquiv K v b := by
  classical
  let Wf := {W : HeightOneSpectrum (𝓞 M) // finitePlaceBelow (K := K) W = v}
  let : Fintype Wf := finitePlaceRestrictionFiberFintype (L := M) v
  let c (W : Wf) := restrict (finitePlaceAdicCompletionMap K M v W) b
  let χ (W : Wf) :=
    DirectSum.of (fun p : Place M => Br (placeCompletion M p)) (Sum.inl W.val) (c W)
  let y := fullIdeleH2BaseRestriction (M := M) x
  have ht : fullIdeleBrauerTuple M E y = ∑ W : Wf, χ W := by
    apply DFinsupp.ext
    intro w
    rw [DirectSum.sum_apply]
    cases w with
    | inr u =>
      rw [fullIdeleBrauerTuple_infinite_apply]
      change fullIdeleInfiniteBrauerCoordinate (E := E) u y = _
      rw [fullIdeleInfiniteBrauerCoordinate_baseRestriction]
      have hu : fullIdeleInfiniteBrauerCoordinate (E := E) (infinitePlaceBelow (K := K) u) x =
          fullIdeleBrauerTuple K E x (Sum.inr (infinitePlaceBelow (K := K) u)) :=
        (fullIdeleBrauerTuple_infinite_apply K E x (infinitePlaceBelow (K := K) u)).symm
      rw [hu, hx, DirectSum.of_eq_of_ne _ _ _ (by intro h; cases h), map_zero]
      symm
      apply Finset.sum_eq_zero
      intro W _
      exact DirectSum.of_eq_of_ne _ _ _ (by intro h; cases h)
    | inl u =>
      rw [fullIdeleBrauerTuple_finite_apply]
      change fullIdeleFiniteBrauerCoordinate (E := E) u y = _
      rw [fullIdeleFiniteBrauerCoordinate_baseRestriction]
      have hu' : fullIdeleFiniteBrauerCoordinate (E := E) (finitePlaceBelow (K := K) u) x =
          fullIdeleBrauerTuple K E x (Sum.inl (finitePlaceBelow (K := K) u)) :=
        (fullIdeleBrauerTuple_finite_apply K E x (finitePlaceBelow (K := K) u)).symm
      rw [hu', hx]
      by_cases hu : finitePlaceBelow (K := K) u = v
      · subst v
        let U : Wf := ⟨u, rfl⟩
        rw [Finset.sum_eq_single U]
        · rw [DirectSum.of_eq_same]
          change c U = χ U (Sum.inl U.val)
          exact (DirectSum.of_eq_same (β := fun w : Place M => Br (placeCompletion M w))
            (Sum.inl U.val) (c U)).symm
        · intro W _ hW
          exact DirectSum.of_eq_of_ne _ _ _ (fun h => hW (Subtype.ext (Sum.inl.inj h).symm))
        · intro h
          exact (h (Finset.mem_univ U)).elim
      · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hu (Sum.inl.inj h)), map_zero]
        symm
        apply Finset.sum_eq_zero
        intro W _
        exact DirectSum.of_eq_of_ne _ _ _ (fun h => hu
          ((congrArg (finitePlaceBelow (K := K)) (Sum.inl.inj h)).trans W.property))
  change sumLocalInv M (fullIdeleBrauerTuple M E y) = _
  rw [ht, map_sum]
  calc
    _ = ∑ W : Wf, adicCompletionDegree v W • finitePlaceBrauerInvariantEquiv K v b := by
      apply Finset.sum_congr rfl
      intro W _
      rw [show sumLocalInv M (χ W) = finitePlaceBrauerInvariantEquiv M W.val (c W) from
        sumLocalInv_single M (Sum.inl W.val) (c W)]
      exact finitePlaceBrauerInvariant_restrict v W b
    _ = (∑ W : Wf, adicCompletionDegree v W) • finitePlaceBrauerInvariantEquiv K v b :=
      Finset.sum_smul.symm
    _ = _ := by rw [sum_adicCompletionDegree (L := M) v]

end GlobalClassFieldTheory.Cohomology
