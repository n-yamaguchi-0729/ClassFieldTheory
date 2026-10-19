/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitCongruencePowerIndex
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups

/-!
# Intrinsic local prime-power congruence index

The complete-DVF count is expressed in the canonical local principal-unit
filtration used by ray class groups and local reciprocity.
-/

noncomputable section
namespace LocalFieldTheory
open scoped ValuativeRel
open DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- At depth pn, the local prime-power congruence quotient has p q^(pn-n)
classes, with q the cardinality of the actual local residue field. -/
theorem card_primePowerCongruenceQuotient (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Kˣ ⧸ (fieldPrincipalUnits K (p * n) ⊔
      (powMonoidHom (α := Kˣ) p).range)) =
        p * Nat.card 𝓀[K] ^ (p * n - n) := by
  let F := localCompleteDVF K
  have hfinite : Finite F.residueField := by
    change Finite 𝓀[K]
    infer_instance
  have hsub :
      (DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F (p * n)).map
        (valuationSubringUnitFieldUnitHom F) = fieldPrincipalUnits K (p * n) := by
    rfl
  have hcard := DiscreteValuationField.card_fieldUnits_mod_primePowers_and_principalUnits
    F p n hn
  rw [hsub] at hcard
  exact hcard

end LocalFieldTheory
