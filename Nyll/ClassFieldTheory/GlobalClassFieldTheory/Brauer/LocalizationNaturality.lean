/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.InfinitePlaceModel
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.Localization

/-! # Brauer localization commutes with actual number-field restriction -/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace ClassFieldTheory.Brauer

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The two routes from the global field to the original larger finite completion agree. -/
theorem finitePlaceRestriction_comp_restrict (v : HeightOneSpectrum (𝓞 K))
    (w : {w : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) w = v}) :
    (finitePlaceRestriction L w.val).comp (restrict (algebraMap K L)) =
      (restrict (finitePlaceAdicCompletionMap K L v w)).comp (finitePlaceRestriction K v) := by
  unfold finitePlaceRestriction
  rw [restrict_comp, restrict_comp]
  congr 1
  apply RingHom.ext
  intro x
  exact (finitePlaceAdicCompletionMap_coe K L v w x).symm

/-- The same actual extension of completions at an infinite place above the given place. -/
def infinitePlaceBrauerCompletionMap (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) : v.Completion →+* w.Completion := by
  let : w.1.LiesOver v.1 := ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  exact AbsoluteValue.Completion.map v.1 w.1

/-- The two routes to a larger infinite completion agree for the original field maps. -/
theorem infinitePlaceRestriction_comp_restrict (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    (infinitePlaceRestriction L w).comp (restrict (algebraMap K L)) =
      (restrict (infinitePlaceBrauerCompletionMap v w hw)).comp (infinitePlaceRestriction K v) := by
  let : w.1.LiesOver v.1 := ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  unfold infinitePlaceRestriction
  rw [restrict_comp, restrict_comp]
  congr 1
  apply RingHom.ext
  intro x
  change algebraMap L w.Completion (algebraMap K L x) =
    AbsoluteValue.Completion.map v.1 w.1 (algebraMap K v.Completion x)
  simpa only [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, WithAbs.map_apply, WithAbs.ofAbs_toAbs] using
      (AbsoluteValue.Completion.map_coe v.1 w.1 (WithAbs.toAbs v.1 x)).symm

end ClassFieldTheory.Brauer
