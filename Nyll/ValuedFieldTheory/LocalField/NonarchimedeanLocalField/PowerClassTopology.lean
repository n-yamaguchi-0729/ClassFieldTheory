/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ProfiniteUnits
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Closed power subgroups in local fields

Compactness of valuation-ring units makes their power image closed.
A field-unit power is integral precisely when its root is integral, so
the full power subgroup is locally closed at one and hence closed.
This includes characteristic powers, whose quotient need not be finite.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- Actual positive power subgroups are closed for the native local topology. -/
theorem isClosed_powerSubgroup (n : ℕ) (hn : n ≠ 0) :
    IsClosed ((powMonoidHom (α := Kˣ) n).range : Set Kˣ) := by
  have : T2Space K := localFieldT2Space K
  let P : Subgroup Kˣ := (powMonoidHom (α := Kˣ) n).range
  let f : 𝒪[K]ˣ →* Kˣ :=
    (powMonoidHom (α := Kˣ) n).comp (integerUnitsToFieldUnits K)
  have hf : Continuous f :=
    (continuous_id.pow n).comp (integerUnitsToFieldUnits_continuous K)
  have hcompact : IsCompact (f.range : Set Kˣ) := by
    change IsCompact (Set.range f)
    simpa only [Set.image_univ] using isCompact_univ.image hf
  have hintersection : f.range = P ⊓ localBaseUnitSubgroup K := by
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨integerUnitsToFieldUnits K a, rfl⟩,
        (localBaseUnitSubgroup K).pow_mem ⟨a, rfl⟩ n⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      have hval := (mem_localBaseUnitSubgroup_iff_valuation_eq_one K (z ^ n)).mp hz
      change ValuativeRel.valuation K ((z : K) ^ n) = 1 at hval
      rw [map_pow] at hval
      have hzval : ValuativeRel.valuation K (z : K) = 1 :=
        (pow_eq_one_iff_of_nonneg zero_le hn).mp hval
      obtain ⟨a, ha⟩ := (mem_localBaseUnitSubgroup_iff_valuation_eq_one K z).mpr hzval
      exact ⟨a, congrArg (fun u : Kˣ => u ^ n) ha⟩
  apply P.isClosed_of_isLocallyClosedAt P.one_mem
  refine ⟨(localBaseUnitSubgroup K : Set Kˣ),
    (localBaseUnitSubgroup_isOpen K).mem_nhds (localBaseUnitSubgroup K).one_mem,
    (f.range : Set Kˣ), hcompact.isClosed, ?_⟩
  rw [hintersection]
  ext x
  change (x ∈ localBaseUnitSubgroup K ∧ x ∈ P) ↔
    (x ∈ localBaseUnitSubgroup K ∧ x ∈ P ∧ x ∈ localBaseUnitSubgroup K)
  exact ⟨fun h => ⟨h.1, h.2, h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩

/-- A non-power remains a non-power modulo sufficiently deep principal units. -/
theorem exists_not_mem_powerSup_principalUnits (n : ℕ) (hn : n ≠ 0)
    (x : Kˣ) (hx : x ∉ (powMonoidHom (α := Kˣ) n).range) :
    ∃ r : ℕ, 1 ≤ r ∧
      x ∉ (powMonoidHom (α := Kˣ) n).range ⊔ fieldPrincipalUnits K r := by
  let P : Subgroup Kˣ := (powMonoidHom (α := Kˣ) n).range
  let V : Set Kˣ := (fun u : Kˣ => x * u) ⁻¹' (P : Set Kˣ)ᶜ
  have hV : IsOpen V :=
    (isClosed_powerSubgroup K n hn).isOpen_compl.preimage
      (continuous_const.mul continuous_id)
  have hOne : (1 : Kˣ) ∈ V := by
    change x * 1 ∉ P
    rw [mul_one]
    exact hx
  obtain ⟨r, hr, hsubset⟩ :=
    exists_fieldPrincipalUnits_subset_of_mem_nhds K V (hV.mem_nhds hOne)
  refine ⟨r, hr, ?_⟩
  intro h
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp h
  have hnot := hsubset ((fieldPrincipalUnits K r).inv_mem hz)
  change x * z⁻¹ ∉ P at hnot
  apply hnot
  rw [← hyz, mul_assoc, mul_inv_cancel, mul_one]
  exact hy

/-- A single finite depth separates a prescribed finite set of local power classes. -/
theorem exists_powerSup_principalUnits_separates_finset (n : ℕ) (hn : n ≠ 0)
    (T : Finset Kˣ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ x ∈ T,
      (x ∈ (powMonoidHom (α := Kˣ) n).range ⊔ fieldPrincipalUnits K r ↔
        x ∈ (powMonoidHom (α := Kˣ) n).range) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨1, le_rfl, fun x hx => (Finset.notMem_empty x hx).elim⟩
  | @insert a T ha ih =>
      obtain ⟨r, hr, hT⟩ := ih
      by_cases haP : a ∈ (powMonoidHom (α := Kˣ) n).range
      · refine ⟨r, hr, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with hxa | hxT
        · subst x
          exact ⟨fun _ => haP, Subgroup.mem_sup_left⟩
        · exact hT x hxT
      · obtain ⟨s, hs, has⟩ := exists_not_mem_powerSup_principalUnits K n hn a haP
        have hmono {i j : ℕ} (hij : i ≤ j) :
            fieldPrincipalUnits K j ≤ fieldPrincipalUnits K i :=
          Subgroup.map_mono (principalUnits_antitone K hij)
        refine ⟨max r s, hr.trans (le_max_left r s), fun x hx => ?_⟩
        refine ⟨fun h => ?_, Subgroup.mem_sup_left⟩
        rcases Finset.mem_insert.mp hx with hxa | hxT
        · subst x
          exact (has ((sup_le_sup_left (hmono (le_max_right r s)) _) h)).elim
        · exact (hT x hxT).mp
            ((sup_le_sup_left (hmono (le_max_left r s)) _) h)

end LocalFieldTheory
