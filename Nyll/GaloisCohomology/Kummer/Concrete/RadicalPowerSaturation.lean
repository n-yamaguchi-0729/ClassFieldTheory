/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.ExtensionRoundTrip

/-! # Ambient powers do not enlarge a Kummer root field -/

noncomputable section

namespace KummerTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Adding ambient powers to the radicands leaves the actual root field unchanged.
This allows quotient calculations to use an admissible Kummer subgroup while
ramification calculations use only the original generators. -/
theorem kummerRadicalExtension_sup_unitNthPowers
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (U : Subgroup Kˣ) :
    kummerRadicalExtension (K := K) (Omega := Ω) n (U ⊔ unitNthPowersSubgroup K n) =
      kummerRadicalExtension (K := K) (Omega := Ω) n U := by
  let E := kummerRadicalExtension (K := K) (Omega := Ω) n U
  have hU : U ≤ finiteKummerRadicalSubgroup (K := K) (L := E) n :=
    le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hn U
  have hP : unitNthPowersSubgroup K n ≤
      finiteKummerRadicalSubgroup (K := K) (L := E) n := by
    rintro a ⟨b, rfl⟩
    refine ⟨Units.map (algebraMap K E).toMonoidHom b, ?_⟩
    exact (map_pow (Units.map (algebraMap K E).toMonoidHom) b (n : ℕ)).symm
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro β ⟨a, ha⟩
    exact kummerRootSet_finiteKummerRadicalSubgroup_le E n hmu
      ⟨⟨a.val, sup_le hU hP a.property⟩, ha⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro β ⟨a, ha⟩
    exact IntermediateField.subset_adjoin K _
      ⟨⟨a.val, (show U ≤ U ⊔ unitNthPowersSubgroup K n from le_sup_left) a.property⟩, ha⟩

end KummerTheory
