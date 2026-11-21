/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderInvertibleIdeal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderConductor
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderIdeals
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The actual prime-to-conductor ideal class map

Contraction of nonzero ideals coprime to the conductor is multiplicative.
Bundling the already proved invertible contractions therefore gives a monoid
homomorphism into the existing fractional-ideal unit group, and composition
with `ClassGroup.mk` gives the original order's actual ideal class map.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors

noncomputable section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] [IsFractionRing O K]

/-- Nonzero integral ideals of the maximal order coprime to the order conductor. -/
def orderPrimeToConductorIdeals : Submonoid (Ideal (𝓞 K)) where
  carrier := {I | I ≠ ⊥ ∧ I ⊔ orderConductor O = ⊤}
  one_mem' := ⟨one_ne_zero, by rw [Ideal.one_eq_top, top_sup_eq]⟩
  mul_mem' hI hJ := ⟨mul_ne_zero hI.1 hJ.1,
    (Ideal.mul_sup_eq_of_coprime_left hI.2).trans hJ.2⟩

/-- The invertible contraction of a product is the product of the actual
invertible contractions. -/
theorem orderContractedIdealUnit_mul
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcI : I ⊔ orderConductor O = ⊤) (hcJ : J ⊔ orderConductor O = ⊤) :
    orderContractedIdealUnit O (I * J) (mul_ne_zero hI hJ)
        ((Ideal.mul_sup_eq_of_coprime_left hcI).trans hcJ) =
      orderContractedIdealUnit O I hI hcI * orderContractedIdealUnit O J hJ hcJ := by
  apply Units.ext
  rw [Units.val_mul, orderContractedIdealUnit_val, orderContractedIdealUnit_val,
    orderContractedIdealUnit_val, orderIdeal_comap_mul_of_coprime_conductor O I J hcI hcJ,
    FractionalIdeal.coeIdeal_mul]

/-- The actual contraction homomorphism into invertible fractional ideals
of the original order. -/
def orderContractedIdealUnitMap :
    orderPrimeToConductorIdeals O →* (FractionalIdeal O⁰ K)ˣ where
  toFun I := orderContractedIdealUnit O I.1 I.2.1 I.2.2
  map_one' := by
    apply Units.ext
    rw [orderContractedIdealUnit_val, Units.val_one]
    change ((1 : Ideal (𝓞 K)).comap (orderToRingOfIntegers O).toRingHom :
      FractionalIdeal O⁰ K) = 1
    rw [Ideal.one_eq_top, Ideal.comap_top, FractionalIdeal.coeIdeal_top]
  map_mul' I J := orderContractedIdealUnit_mul O I.1 J.1 I.2.1 J.2.1 I.2.2 J.2.2

/-- The prime-to-conductor ideal class map uses Mathlib's invertible-ideal
class group of the original, possibly nonmaximal, order. -/
def orderIdealClassMap : orderPrimeToConductorIdeals O →* ClassGroup O :=
  (ClassGroup.mk K).comp (orderContractedIdealUnitMap O)

/-- Evaluation is the class of the original contracted invertible ideal. -/
@[simp]
theorem orderIdealClassMap_apply (I : orderPrimeToConductorIdeals O) :
    orderIdealClassMap O I = orderContractedIdealClass O I.1 I.2.1 I.2.2 := rfl

end NumberField
