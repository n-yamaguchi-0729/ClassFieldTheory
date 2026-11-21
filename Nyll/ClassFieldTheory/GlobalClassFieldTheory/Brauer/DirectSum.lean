/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Data.Finset.Sum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteLocalizedStage

/-! # Brauer localization into the direct sum over all places -/

public section

noncomputable section

open IsDedekindDomain NumberField
open scoped DirectSum NumberField

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The finite and infinite places with their original completions. -/
abbrev Place := HeightOneSpectrum (𝓞 K) ⊕ InfinitePlace K

/-- The original completion at a finite or infinite place. -/
abbrev placeCompletion : Place K → Type u
  | Sum.inl v => v.adicCompletion K
  | Sum.inr v => v.Completion

instance placeCompletionField : (v : Place K) → Field (placeCompletion K v)
  | Sum.inl v => inferInstanceAs (Field (v.adicCompletion K))
  | Sum.inr v => inferInstanceAs (Field v.Completion)

/-- The restriction on continuous Brauer groups of the indicated completion. -/
@[expose]
def placeRestriction : (v : Place K) → Br K →+ Br (placeCompletion K v)
  | Sum.inl v => finitePlaceRestriction K v
  | Sum.inr v => infinitePlaceRestriction K v

private theorem exists_placeRestriction_support (x : Br K) :
    ∃ S : Finset (Place K), ∀ v : Place K, v ∉ S → placeRestriction K v x = 0 := by
  classical
  obtain ⟨S, hS⟩ := finitePlaceRestriction_hasFiniteSupport x
  refine ⟨S.disjSum Finset.univ, ?_⟩
  intro v hv
  cases v with
  | inl v => exact hS v (fun hin => hv (Finset.inl_mem_disjSum.mpr hin))
  | inr v => exact (hv (Finset.inr_mem_disjSum.mpr (Finset.mem_univ _))).elim

private def localizedTuple (x : Br K) : ⨁ v : Place K, Br (placeCompletion K v) := by
  classical
  exact DFinsupp.mk (exists_placeRestriction_support K x).choose
    (fun v => placeRestriction K v.val x)

private theorem localizedTuple_apply (x : Br K) (v : Place K) :
    localizedTuple K x v = placeRestriction K v x := by
  classical
  by_cases hv : v ∈ (exists_placeRestriction_support K x).choose
  · simp only [localizedTuple, DFinsupp.mk_apply, dite_eq_left hv]
  · simp only [localizedTuple, DFinsupp.mk_apply, dite_eq_right hv]
    exact ((exists_placeRestriction_support K x).choose_spec v hv).symm

/-- The global Brauer localization map into the actual direct sum of local groups. -/
def localization : Br K →+ (⨁ v : Place K, Br (placeCompletion K v)) where
  toFun := localizedTuple K
  map_zero' := DFinsupp.ext fun v => by
    rw [localizedTuple_apply, map_zero, DFinsupp.zero_apply]
  map_add' x y := DFinsupp.ext fun v => by
    change localizedTuple K (x + y) v = localizedTuple K x v + localizedTuple K y v
    rw [localizedTuple_apply, localizedTuple_apply, localizedTuple_apply, map_add]

/-- Each direct-sum coordinate is the original restriction at that place. -/
@[simp]
theorem localization_apply (x : Br K) (v : Place K) :
    localization K x v = placeRestriction K v x :=
  localizedTuple_apply K x v

/-- The direct sum of the finite local groups and the product of the infinite local groups. -/
abbrev FiniteInfiniteLocalBrauer :=
  (⨁ v : HeightOneSpectrum (𝓞 K), Br (v.adicCompletion K)) ×
    ((v : InfinitePlace K) → Br v.Completion)

private def finiteInfiniteValue (x : FiniteInfiniteLocalBrauer K) :
    (w : Place K) → Br (placeCompletion K w)
  | Sum.inl v => x.1 v
  | Sum.inr v => x.2 v

private def assembleLocalBrauer (x : FiniteInfiniteLocalBrauer K) :
    ⨁ w : Place K, Br (placeCompletion K w) := by
  classical
  let S : Finset (Place K) := x.1.support.disjSum Finset.univ
  let f (w : S) : Br (placeCompletion K w.val) := finiteInfiniteValue K x w.val
  exact DFinsupp.mk S f

private theorem assembleLocalBrauer_apply (x : FiniteInfiniteLocalBrauer K) (w : Place K) :
    assembleLocalBrauer K x w = finiteInfiniteValue K x w := by
  classical
  let S : Finset (Place K) := x.1.support.disjSum (Finset.univ : Finset (InfinitePlace K))
  let f (u : S) : Br (placeCompletion K u.val) := finiteInfiniteValue K x u.val
  let a : ⨁ v : Place K, Br (placeCompletion K v) := DFinsupp.mk S f
  change a w = finiteInfiniteValue K x w
  by_cases hw : w ∈ S
  · exact DFinsupp.mk_of_mem
      (β := fun v : Place K => Br (placeCompletion K v)) (x := f) hw
  · have h0 : finiteInfiniteValue K x w = 0 := by
      cases w with
      | inl v =>
        exact DFinsupp.notMem_support_iff.mp (fun hv => hw (Finset.inl_mem_disjSum.mpr hv))
      | inr v =>
        exact (hw (Finset.inr_mem_disjSum.mpr (Finset.mem_univ v))).elim
    exact (DFinsupp.mk_of_notMem
      (β := fun v : Place K => Br (placeCompletion K v)) (x := f) hw).trans h0.symm

/-- The finite/infinite product gives the same all-place family with the original coordinates. -/
def finiteInfiniteLocalBrauerEquiv :
    (⨁ w : Place K, Br (placeCompletion K w)) ≃+ FiniteInfiniteLocalBrauer K where
  toFun x := ⟨DFinsupp.comapDomain Sum.inl Sum.inl_injective x, fun v => x (Sum.inr v)⟩
  invFun := assembleLocalBrauer K
  left_inv x := by
    apply DirectSum.ext
    intro w
    rw [assembleLocalBrauer_apply]
    cases w <;> rfl
  right_inv x := by
    apply Prod.ext
    · apply DirectSum.ext
      intro v
      exact assembleLocalBrauer_apply K x (Sum.inl v)
    · funext v
      exact assembleLocalBrauer_apply K x (Sum.inr v)
  map_add' x y :=
    Prod.ext (DFinsupp.comapDomain_add Sum.inl Sum.inl_injective x y) (funext fun _ => rfl)

end ClassFieldTheory.Brauer
