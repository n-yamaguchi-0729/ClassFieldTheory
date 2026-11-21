/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateInducedShift
public import Nyll.GaloisCohomology.GroupTheory.InducedShiftNaturality

/-! # Naturality of the actual induced integral Tate shift -/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- Naturality of the actual connecting-map equivalence for the induced shift. -/
theorem indShiftDownEquiv_naturality {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n : ℤ) :
    (indShiftDownEquiv A n).toModuleIso.hom ≫
        (tateFunctor G (n + 1)).map (Rep.indShiftDownMap f) =
      (tateFunctor G n).map f ≫ (indShiftDownEquiv B n).toModuleIso.hom :=
  tateδ_naturality (Rep.indShiftSequence_shortExact A)
    (Rep.indShiftSequence_shortExact B) (Rep.indShiftSequenceMap f) n

/-- The same naturality square evaluated on an original Tate class. -/
theorem indShiftDownEquiv_naturality_apply {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n : ℤ)
    (x : tate A n) :
    (tateFunctor G (n + 1)).map (Rep.indShiftDownMap f) (indShiftDownEquiv A n x) =
      indShiftDownEquiv B n ((tateFunctor G n).map f x) :=
  congrArg (fun h : tate A n ⟶ tate (Rep.indShiftDown B) (n + 1) => h x)
    (indShiftDownEquiv_naturality f n)

end IntegralGroupCohomology.Universe
