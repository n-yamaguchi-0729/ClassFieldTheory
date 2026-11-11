/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IsMaximalAbelianGlobalArtin
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.TopologicalGlobalReciprocity
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNaturality

/-!
# The maximal abelian global Artin map

This map from Mathlib's idèle class group to Mathlib's abelianized absolute
Galois group is continuous, surjective, and has the identity component as
its kernel. The existence statement uses the specified `mathlibGlobalArtin`
map itself. Its actual finite projections and base/model naturality are proved
in `MathlibGlobalArtinNaturality`; the predicate here records only surjectivity
and the kernel and does not by itself assert uniqueness.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- A continuous surjective global Artin map with the expected kernel exists. -/
theorem maximalAbelianGlobalArtin
    (K : Type u) [Field K] [NumberField K] :
    ∃ artin : NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
        Field.absoluteGaloisGroupAbelianization K,
      IsMaximalAbelianGlobalArtin K artin := by
  exact ⟨GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin K,
    GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin_surjective K,
    GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin_ker K⟩

end ClassFieldTheory
