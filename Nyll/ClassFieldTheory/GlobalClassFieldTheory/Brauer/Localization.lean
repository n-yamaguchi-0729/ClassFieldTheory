/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction

/-!
# Restriction to completions of a number field

Both maps use the original embeddings into the completions. They apply at
all finite and infinite places, including real places.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace ClassFieldTheory.Brauer

variable (K : Type*) [Field K] [NumberField K]

/-- Restriction of a global Brauer class to the completion at a finite place. -/
def finitePlaceRestriction (v : HeightOneSpectrum (𝓞 K)) :
    Br K →+ Br (v.adicCompletion K) :=
  restrict (algebraMap K (v.adicCompletion K))

/-- Restriction of a global Brauer class to the completion at an infinite place. -/
def infinitePlaceRestriction (v : InfinitePlace K) : Br K →+ Br v.Completion :=
  restrict (algebraMap K v.Completion)

end ClassFieldTheory.Brauer
