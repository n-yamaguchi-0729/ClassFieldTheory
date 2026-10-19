/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.PositiveCharacteristicQuotient
import Nyll.ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
import Nyll.ValuedFieldTheory.LocalField.GroupTheory.QuotientPowers

/-!
# Field-unit power indices with congruence conditions

The established unit/uniformizer decomposition descends modulo any subgroup
of the valuation-ring units. The uniformizer factor then contributes n to
the index after adjoining n-th powers. In characteristic p, the exact
principal-unit Frobenius calculation supplies the other factor.
-/

noncomputable section
namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
open CompleteDVF.higherPrincipalUnitGroup

variable {K : Type*} [Field K] (F : CompleteDVF K) [Finite F.residueField]

/-- A finite congruence quotient contributes its power classes, while the
uniformizer direction contributes exactly the exponent. -/
theorem card_fieldUnits_mod_congruence_and_powers
    (H : Subgroup F.valuationSubringˣ) [Finite (F.valuationSubringˣ ⧸ H)]
    (n : ℕ) (hn : n ≠ 0) :
    let Q := F.valuationSubringˣ ⧸ H
    Nat.card (Kˣ ⧸ (H.map (valuationSubringUnitFieldUnitHom F) ⊔
      (powMonoidHom (α := Kˣ) n).range)) =
    n * Nat.card (Q ⧸
      (MonoidHom.range (G := Q) (N := Q) (powMonoidHom (α := Q) n))) := by
  intro Q
  obtain ⟨π, hπ⟩ := F.exists_uniformizer
  let eField := fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ
  let eUnits := valuationSubringUnitsEquivRootsTimesPrincipalUnits F
  let e : Kˣ ≃* F.valuationSubringˣ × Multiplicative ℤ :=
    eField.symm.trans (MulEquiv.prodCongr eUnits (MulEquiv.refl (Multiplicative ℤ)))
  let i : F.valuationSubringˣ →* Kˣ := valuationSubringUnitFieldUnitHom F
  have he (u : F.valuationSubringˣ) : e.symm (u, 1) = i u := by
    change eField (eUnits.symm u, 1) = i u
    rw [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]
    simp only [toAdd_one, zpow_zero, mul_one]
    rw [← map_mul]
    exact congrArg i (eUnits.apply_symm_apply u)
  have hmap : (H.prod (⊥ : Subgroup (Multiplicative ℤ))).map e.symm.toMonoidHom =
      H.map i := by
    ext x
    constructor
    · rintro ⟨⟨u, z⟩, ⟨hu, hz⟩, rfl⟩
      have hz1 : z = 1 := hz
      subst z
      exact ⟨u, hu, (he u).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u, 1), ⟨hu, rfl⟩, he u⟩
  let eQ : (Kˣ ⧸ H.map i) ≃* Q × Multiplicative ℤ :=
    (QuotientGroup.congr (H.prod (⊥ : Subgroup (Multiplicative ℤ)))
      (H.map i) e.symm hmap).symm.trans
      ((QuotientGroup.prodMulEquiv H (⊥ : Subgroup (Multiplicative ℤ))).trans
        (MulEquiv.prodCongr (MulEquiv.refl Q)
          (QuotientGroup.quotientBot (G := Multiplicative ℤ))))
  have hninst : NeZero n := ⟨hn⟩
  have hfinite : Finite ((Kˣ ⧸ H.map i) ⧸
      (MonoidHom.range (G := Kˣ ⧸ H.map i) (N := Kˣ ⧸ H.map i)
        (powMonoidHom (α := Kˣ ⧸ H.map i) n))) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv_units_prod_int
      (Kˣ ⧸ H.map i) Q eQ
  let eP := LocalFieldTheory.quotientSupRangePowEquiv Kˣ (H.map i) n
  have heP := Nat.card_congr eP
  exact heP.trans
    (LocalFieldTheory.card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int
      (Kˣ ⧸ H.map i) Q hn eQ)

/-- The characteristic-p power quotient modulo depth-pn principal units
has exactly p q^(pn-n) elements. -/
theorem card_fieldUnits_mod_primePowers_and_principalUnits
    (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Kˣ ⧸ ((CompleteDVF.higherPrincipalUnitGroup F (p * n)).map
      (valuationSubringUnitFieldUnitHom F) ⊔ (powMonoidHom (α := Kˣ) p).range)) =
        p * Nat.card F.residueField ^ (p * n - n) := by
  rw [card_fieldUnits_mod_congruence_and_powers F
    (CompleteDVF.higherPrincipalUnitGroup F (p * n)) p (Fact.out : p.Prime).ne_zero,
    card_unitQuotient_primePowerQuotient F p n hn]

end LocalFieldTheory.DiscreteValuationField
