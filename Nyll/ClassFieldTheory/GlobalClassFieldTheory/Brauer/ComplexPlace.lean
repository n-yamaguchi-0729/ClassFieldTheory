/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Nyll.ClassFieldTheory.Algebra.Brauer.SeparablyClosed
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.Localization

/-! # Brauer localization at a complex place -/

@[expose] public section

namespace ClassFieldTheory.Brauer

variable {K : Type*} [Field K]

/-- All cohomological Brauer classes over the completion at a complex place vanish. -/
theorem complexPlace_br_subsingleton {v : NumberField.InfinitePlace K} (hv : v.IsComplex) :
    Subsingleton (Br v.Completion) := by
  let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
  have : IsAlgClosed v.Completion := by
    apply IsAlgClosed.of_exists_root
    intro p _ hp
    have hdeg : (p.map e.toRingHom).degree ≠ 0 := by
      rw [Polynomial.degree_map]
      exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (k := ℂ) (p.map e.toRingHom) hdeg
    refine ⟨e.symm z, ?_⟩
    apply e.injective
    have he := Polynomial.eval_map_apply e.toRingHom (p := p) (e.symm z)
    have hroot : (p.map e.toRingHom).eval (e (e.symm z)) = 0 :=
      (congrArg (fun x => (p.map e.toRingHom).eval x) (e.apply_symm_apply z)).trans hz
    exact (he.symm.trans hroot).trans (map_zero e).symm
  exact subsingleton_of_isSepClosed v.Completion

/-- The actual localization at a complex place sends every class to zero. -/
theorem infinitePlaceRestriction_eq_zero_of_isComplex
    {v : NumberField.InfinitePlace K} (hv : v.IsComplex) :
    infinitePlaceRestriction K v = 0 := by
  let : Subsingleton (Br v.Completion) := complexPlace_br_subsingleton hv
  apply AddMonoidHom.ext
  intro x
  exact Subsingleton.elim _ _

end ClassFieldTheory.Brauer
