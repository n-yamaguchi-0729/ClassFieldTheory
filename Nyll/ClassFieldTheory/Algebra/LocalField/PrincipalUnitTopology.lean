/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ProfiniteUnits
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Group.Units

/-!
# Openness of the existing local principal-unit filtration

The filtration is the one already used by local class field theory. Its image in
the field unit group is open because the integer-unit inclusion is an open embedding.
-/

noncomputable section

open scoped ValuativeRel
open Topology

namespace LocalFieldTheory

open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- Integer units embed as the open subgroup of valuation-one field units. -/
theorem isOpenEmbedding_integerUnitsToFieldUnits :
    IsOpenEmbedding (integerUnitsToFieldUnits F) := by
  have : T2Space F := localFieldT2Space F
  have hc : Continuous (integerUnitsToFieldUnits F) :=
    continuous_subtype_val.units_map (algebraMap 𝒪[F] F).toMonoidHom
  exact
    { toIsEmbedding :=
        (hc.isClosedEmbedding (integerUnitsToFieldUnits_injective F)).isEmbedding
      isOpen_range := localBaseUnitSubgroup_isOpen F }

/-- Every step of the existing principal-unit filtration is open in integer units. -/
theorem isOpen_principalUnits (n : ℕ) :
    IsOpen (principalUnits F n : Set 𝒪[F]ˣ) := by
  have : T2Space F := localFieldT2Space F
  change IsOpen ((fun u : 𝒪[F]ˣ => (u : 𝒪[F]) - 1) ⁻¹'
    (((IsLocalRing.maximalIdeal 𝒪[F]) ^ n : Ideal 𝒪[F]) : Set 𝒪[F]))
  exact (IsLocalRing.isOpen_maximalIdeal_pow 𝒪[F] n).preimage
    (Units.continuous_val.sub continuous_const)

/-- The same filtration is open in the full multiplicative group of the local field. -/
theorem isOpen_fieldPrincipalUnits (n : ℕ) :
    IsOpen (fieldPrincipalUnits F n : Set Fˣ) := by
  change IsOpen ((integerUnitsToFieldUnits F) '' (principalUnits F n : Set 𝒪[F]ˣ))
  exact (isOpenEmbedding_integerUnitsToFieldUnits F).isOpenMap _
    (isOpen_principalUnits F n)

end LocalFieldTheory
