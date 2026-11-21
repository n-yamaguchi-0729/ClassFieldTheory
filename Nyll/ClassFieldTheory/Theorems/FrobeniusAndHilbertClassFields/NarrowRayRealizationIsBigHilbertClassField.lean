/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsRayArtinModulusProjection
import Nyll.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldExists
import Nyll.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldNarrowRayRealization

/-!
# A narrow ray realization is a big Hilbert class field

The Frobenius-normalized realization of the narrow ray class group is
maximal among finite abelian extensions unramified at finite places.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- Every realization of the narrow ray class group is a big Hilbert class
field, including its maximality property. -/
theorem narrowRayRealization_isBigHilbertClassField
    (K : Type u) [Field K] [NumberField K]
    (R : RayClassFieldRealization K (narrowRayClassModulus K)) :
    IsBigHilbertClassField R.extension := by
  obtain ⟨E, hE⟩ := exists_bigHilbertClassField K
  obtain ⟨S, hS⟩ := bigHilbertClassField_hasNarrowRayRealization K E hE
  subst E
  obtain ⟨f, _⟩ :=
    exists_rayArtin_modulusProjection
      (le_refl (narrowRayClassModulus K)) S R
  constructor
  · apply (IsUnramifiedAtFinitePlaces.iff_forall_below K R.extension).mpr
    intro v
    exact R.unramifiedOutsideModulus.1 v (by
      change v ∉ (0 : RayClass.FiniteModulus K).support
      rw [Finsupp.support_zero]
      exact Finset.notMem_empty _)
  · intro F hF
    obtain ⟨g⟩ := hE.2 F hF
    exact ⟨f.comp g⟩

end ClassFieldTheory
