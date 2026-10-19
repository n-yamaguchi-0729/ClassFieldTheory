/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Instances.Int

/-!
# Continuity of valuation vectors

The integral-unit subgroup is open in the restricted-product topology. Consequently,
the valuation-vector map is continuous when its finitely supported target is discrete.
The topology of that target is supplied explicitly, without installing a topology on
all finitely supported functions.
-/

open scoped RestrictedProduct WithZero

noncomputable section

namespace RestrictedProduct.DiscreteValuation

section Local

variable (F : Type*) [Field F] [Valued F ℤᵐ⁰]

/-- The normalized local order is continuous with values in the discrete integers. -/
theorem continuous_localOrder : Continuous (localOrder F) := by
  apply ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete
  have hker : (localOrder F).ker =
      (Valued.v : Valuation F ℤᵐ⁰).valuationSubring.units := by
    apply Subgroup.ext
    intro x
    exact localOrder_eq_zero_iff F x
  rw [hker]
  exact Submonoid.isOpen_units (Valued.isOpen_valuationSubring F)

/-- Normalized local order as a continuous group homomorphism. -/
def localOrderContinuous : Fˣ →ₜ* Multiplicative ℤ where
  toMonoidHom := localOrder F
  continuous_toFun := continuous_localOrder F

end Local

section Family

variable {ι : Type*} (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Valued (F i) ℤᵐ⁰]

/-- Families that are integral units everywhere form an open subgroup. -/
theorem isOpen_integralSubgroup : IsOpen (integralSubgroup F : Set (UnitProduct F)) :=
  RestrictedProduct.isOpen_forall_mem
    (fun i => Submonoid.isOpen_units (Valued.isOpen_valuationSubring (F i)))

variable [TopologicalSpace (Multiplicative (ι →₀ ℤ))]
  [DiscreteTopology (Multiplicative (ι →₀ ℤ))]

/-- The valuation vector is continuous for the discrete topology on its target. -/
theorem continuous_valuationVector : Continuous (valuationVector F) := by
  have : Fact (∀ i, IsOpen
      ((Valued.v : Valuation (F i) ℤᵐ⁰).valuationSubring.units : Set (F i)ˣ)) :=
    ⟨fun i => Submonoid.isOpen_units (Valued.isOpen_valuationSubring (F i))⟩
  apply ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete
  rw [valuationVector_ker]
  exact isOpen_integralSubgroup F

/-- The valuation vector as a continuous group homomorphism to the discrete divisor group. -/
def valuationVectorContinuous : UnitProduct F →ₜ* Multiplicative (ι →₀ ℤ) where
  toMonoidHom := valuationVector F
  continuous_toFun := continuous_valuationVector F

end Family

end RestrictedProduct.DiscreteValuation
