/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateDimensionShift
public import Nyll.GaloisCohomology.GroupTheory.CoinducedShiftNaturality

/-!
# Naturality of integral Tate dimension shifting

The actual shift isomorphism commutes with coefficient maps because it is the
connecting map of the specified coinduced short exact sequence.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- The actual connecting-map equivalence is natural for coefficient morphisms. -/
theorem coindShiftUpEquiv_naturality {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n : ℤ) :
    (coindShiftUpEquiv A n).toModuleIso.hom ≫ (tateFunctor G (n + 1)).map f =
      (tateFunctor G n).map (Rep.coindShiftUpMap f) ≫
        (coindShiftUpEquiv B n).toModuleIso.hom :=
  tateδ_naturality (Rep.coindShiftSequence_shortExact A)
    (Rep.coindShiftSequence_shortExact B) (Rep.coindShiftSequenceMap f) n

/-- Elementwise naturality uses the same maps on the original Tate groups. -/
theorem coindShiftUpEquiv_naturality_apply {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n : ℤ)
    (x : tate (Rep.coindShiftUp A) n) :
    (tateFunctor G (n + 1)).map f (coindShiftUpEquiv A n x) =
      coindShiftUpEquiv B n ((tateFunctor G n).map (Rep.coindShiftUpMap f) x) :=
  congrArg (fun h : tate (Rep.coindShiftUp A) n ⟶ tate B (n + 1) => h x)
    (coindShiftUpEquiv_naturality f n)

end IntegralGroupCohomology.Universe
