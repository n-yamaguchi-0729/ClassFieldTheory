/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Sylow
public import Nyll.GaloisCohomology.Cyclic.IntegralTateDegreeOne
public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupIsomorphism
public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupTransfer
public import Nyll.GaloisCohomology.Cyclic.IntegralTateNormTower
public import Nyll.GaloisCohomology.Cyclic.IntegralTateSubgroupShift

/-!
# Adjacent Tate groups on subgroups of prime-power order

Degree-zero vanishing on the subgroups makes the subgroup norms surjective.
Induction on the order of a `p`-group, using its cyclic quotient of order `p`,
then equates universal vanishing of Tate degrees `-1` and `1`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance tateFiniteSubgroup (S : Subgroup G) : Fintype S :=
  Fintype.ofFinite S

private theorem tate_isZero_of_subsingleton_group {K : Type u} [Group K] [Fintype K]
    [Subsingleton K] (B : Rep.{u} ℤ K) (n : ℤ) : IsZero (tate B n) := by
  let : Unique K := { default := 1, uniq := fun g => Subsingleton.elim g 1 }
  refine tate_isZero_of_trace_identity B LinearMap.id (fun x => ?_) n
  rw [Fintype.sum_unique]
  have hd : (default : K) = 1 := Subsingleton.elim _ _
  rw [hd, inv_one, map_one, LinearMap.id_apply, one_apply_eq_self, one_apply_eq_self]

/-- A subgroup of a subgroup has the same actual Tate groups as its image
in the original group, via the original inclusion of its elements. -/
def tateNestedSubgroupIso (A : Rep.{u} ℤ G) (S : Subgroup G) (T : Subgroup S) (n : ℤ) :
    tate (Rep.res T.subtype (Rep.res S.subtype A)) n ≅
      tate (Rep.res (T.map S.subtype).subtype A) n := by
  let e := T.equivMapOfInjective S.subtype S.subtype_injective
  let B := Rep.res T.subtype (Rep.res S.subtype A)
  let C := Rep.res (T.map S.subtype).subtype A
  let c : Rep.res e.symm.toMonoidHom B ≅ C := Rep.mkIso
    (Representation.Equiv.mk (LinearEquiv.refl ℤ _) (fun g => by
      apply LinearMap.ext
      intro x
      change A.ρ (((e.symm g : T) : S) : G) x = A.ρ (g : G) x
      exact congrArg (fun y : T.map S.subtype => A.ρ (y : G) x) (e.apply_symm_apply g)))
  exact tateReindexIso e B n ≪≫ (tateFunctor (T.map S.subtype) n).mapIso c

/-- On every `p`-subgroup, zero in Tate degree zero makes universal vanishing
in degree minus one equivalent to universal vanishing in degree one. -/
theorem pSubgroup_tateNegOne_isZero_iff_one (p : ℕ) [Fact p.Prime] (A : Rep.{u} ℤ G)
    (h₀ : ∀ (S : Subgroup G), IsPGroup p S → IsZero (tate (Rep.res S.subtype A) 0)) :
    (∀ (S : Subgroup G), IsPGroup p S → IsZero (tate (Rep.res S.subtype A) (-1))) ↔
      (∀ (S : Subgroup G), IsPGroup p S → IsZero (tate (Rep.res S.subtype A) 1)) := by
  constructor
  · intro hneg S hS
    induction hs : Nat.card S using Nat.strong_induction_on generalizing S with
    | _ N ih =>
      subst hs
      rcases IsPGroup.card_eq_or_dvd hS with hcard | hdvd
      · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hcard).1
        exact tate_isZero_of_subsingleton_group _ 1
      have := IsPGroup.isNilpotent hS
      obtain ⟨T, hTindex, hTnormal⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
      let : T.Normal := hTnormal
      let : Fintype (S ⧸ T) := Fintype.ofFinite _
      let : IsCyclic (S ⧸ T) := isCyclic_of_prime_card (p := p) (by rw [← hTindex, Subgroup.index])
      let B := Rep.res S.subtype A
      have hp : IsPGroup p (T.map S.subtype) := IsPGroup.to_le hS (Subgroup.map_subtype_le T)
      have hlt : Nat.card (T.map S.subtype) < Nat.card S := by
        rw [Subgroup.card_map_of_injective S.subtype_injective, ← T.card_mul_index, hTindex]
        exact lt_mul_right Nat.card_pos (Fact.out : p.Prime).one_lt
      have hT₀ := (h₀ (T.map S.subtype) hp).of_iso (tateNestedSubgroupIso A S T 0)
      have hTneg := (hneg (T.map S.subtype) hp).of_iso (tateNestedSubgroupIso A S T (-1))
      have hTpos := (ih _ hlt (T.map S.subtype) hp rfl).of_iso (tateNestedSubgroupIso A S T 1)
      have hQneg := (tateNegOne_quotient_isZero_iff T B hT₀ hTneg).mpr (hneg S hS)
      exact tateOne_isZero_of_normalSubgroup T B hTpos
        ((tateOne_isZero_iff_negOne_of_cyclic _).mpr hQneg)
  · intro hpos S hS
    induction hs : Nat.card S using Nat.strong_induction_on generalizing S with
    | _ N ih =>
      subst hs
      rcases IsPGroup.card_eq_or_dvd hS with hcard | hdvd
      · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hcard).1
        exact tate_isZero_of_subsingleton_group _ (-1)
      have := IsPGroup.isNilpotent hS
      obtain ⟨T, hTindex, hTnormal⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
      let : T.Normal := hTnormal
      let : Fintype (S ⧸ T) := Fintype.ofFinite _
      let : IsCyclic (S ⧸ T) := isCyclic_of_prime_card (p := p) (by rw [← hTindex, Subgroup.index])
      let B := Rep.res S.subtype A
      have hp : IsPGroup p (T.map S.subtype) := IsPGroup.to_le hS (Subgroup.map_subtype_le T)
      have hlt : Nat.card (T.map S.subtype) < Nat.card S := by
        rw [Subgroup.card_map_of_injective S.subtype_injective, ← T.card_mul_index, hTindex]
        exact lt_mul_right Nat.card_pos (Fact.out : p.Prime).one_lt
      have hT₀ := (h₀ (T.map S.subtype) hp).of_iso (tateNestedSubgroupIso A S T 0)
      have hTneg := (ih _ hlt (T.map S.subtype) hp rfl).of_iso (tateNestedSubgroupIso A S T (-1))
      have hQpos := tateOne_quotient_isZero_of_isZero T B (hpos S hS)
      exact (tateNegOne_quotient_isZero_iff T B hT₀ hTneg).mp
        ((tateOne_isZero_iff_negOne_of_cyclic _).mp hQpos)

/-- Vanishing of the same Tate degree on every subgroup of prime-power order. -/
abbrev TateVanishingOnPSubgroups (A : Rep.{u} ℤ G) (n : ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S → IsZero (tate (Rep.res S.subtype A) n)

private theorem coindShift_pSubgroups (A : Rep.{u} ℤ G) (n : ℤ) :
    TateVanishingOnPSubgroups (Rep.coindShiftUp A) n ↔ TateVanishingOnPSubgroups A (n + 1) :=
  ⟨fun h p _ S hS => (h p S hS).of_iso (subgroupCoindShiftEquiv S A n).toModuleIso.symm,
    fun h p _ S hS => (h p S hS).of_iso (subgroupCoindShiftEquiv S A n).toModuleIso⟩

private theorem indShift_pSubgroups (A : Rep.{u} ℤ G) (n : ℤ) :
    TateVanishingOnPSubgroups A n ↔ TateVanishingOnPSubgroups (Rep.indShiftDown A) (n + 1) :=
  ⟨fun h p _ S hS => (h p S hS).of_iso (subgroupIndShiftEquiv S A n).toModuleIso.symm,
    fun h p _ S hS => (h p S hS).of_iso (subgroupIndShiftEquiv S A n).toModuleIso⟩

/-- The vanishing of an intervening Tate degree on the `p`-subgroups makes
vanishing of the two neighboring degrees equivalent. -/
theorem pSubgroup_tate_neighbor_iff (A : Rep.{u} ℤ G) (q : ℤ)
    (h : TateVanishingOnPSubgroups A (q + 1)) :
    TateVanishingOnPSubgroups A q ↔ TateVanishingOnPSubgroups A (q + 2) := by
  let P (i : ℤ) : Prop := ∀ (B : Rep.{u} ℤ G), TateVanishingOnPSubgroups B (i + 1) →
    (TateVanishingOnPSubgroups B i ↔ TateVanishingOnPSubgroups B (i + 2))
  have hbase : P (-1) := by
    intro B hB
    constructor
    · intro h₁ p _ S hS
      exact (pSubgroup_tateNegOne_isZero_iff_one p B (hB p)).mp (h₁ p) S hS
    · intro h₁ p _ S hS
      exact (pSubgroup_tateNegOne_isZero_iff_one p B (hB p)).mpr (h₁ p) S hS
  have hup (i : ℤ) (hi : P i) : P (i + 1) := by
    intro B hB
    have hc := (coindShift_pSubgroups B (i + 1)).mpr hB
    have ht : TateVanishingOnPSubgroups (Rep.coindShiftUp B) (i + 2) ↔
        TateVanishingOnPSubgroups B (i + 1 + 2) := by
      rw [show i + 1 + 2 = i + 2 + 1 by omega]
      exact coindShift_pSubgroups B (i + 2)
    exact (coindShift_pSubgroups B i).symm.trans ((hi (Rep.coindShiftUp B) hc).trans ht)
  have hdown (i : ℤ) (hi : P i) : P (i - 1) := by
    intro B hB
    have hc : TateVanishingOnPSubgroups (Rep.indShiftDown B) (i + 1) :=
      (indShift_pSubgroups B i).mp (by
        rw [show i = i - 1 + 1 by omega]
        exact hB)
    have hl : TateVanishingOnPSubgroups B (i - 1) ↔
        TateVanishingOnPSubgroups (Rep.indShiftDown B) i := by
      simpa only [sub_add_cancel] using indShift_pSubgroups B (i - 1)
    have hr : TateVanishingOnPSubgroups B (i - 1 + 2) ↔
        TateVanishingOnPSubgroups (Rep.indShiftDown B) (i + 2) := by
      rw [show i + 2 = (i - 1 + 2) + 1 by omega]
      exact indShift_pSubgroups B (i - 1 + 2)
    exact hl.trans ((hi (Rep.indShiftDown B) hc).trans hr.symm)
  have hq : P q := Int.inductionOn' q (-1) hbase (fun i _ => hup i) (fun i _ => hdown i)
  exact hq A h

/-- Two consecutive Tate vanishings on every subgroup of prime-power order
give the original vanishing there in every integer degree. -/
theorem tateVanishingOnPSubgroups_of_adjacent (A : Rep.{u} ℤ G) (q n : ℤ)
    (h₀ : TateVanishingOnPSubgroups A q) (h₁ : TateVanishingOnPSubgroups A (q + 1)) :
    TateVanishingOnPSubgroups A n := by
  let P (i : ℤ) : Prop :=
    TateVanishingOnPSubgroups A i ∧ TateVanishingOnPSubgroups A (i + 1)
  have hbase : P q := ⟨h₀, h₁⟩
  have hup (i : ℤ) (_ : q ≤ i) (hi : P i) : P (i + 1) := by
    refine ⟨hi.2, ?_⟩
    rw [show (i + 1) + 1 = i + 2 by omega]
    exact (pSubgroup_tate_neighbor_iff A i hi.2).mp hi.1
  have hdown (i : ℤ) (_ : i ≤ q) (hi : P i) : P (i - 1) := by
    have hm : TateVanishingOnPSubgroups A (i - 1 + 1) := by
      rw [show i - 1 + 1 = i by omega]
      exact hi.1
    have ht : TateVanishingOnPSubgroups A (i - 1 + 2) := by
      rw [show i - 1 + 2 = i + 1 by omega]
      exact hi.2
    exact ⟨(pSubgroup_tate_neighbor_iff A (i - 1) hm).mpr ht, hm⟩
  have hn : P n := Int.inductionOn' n q hbase hup hdown
  exact hn.1

/-- Sylow restriction detects vanishing of the actual Tate cohomology in
any integer degree, using the original corestriction and index formula. -/
theorem tate_isZero_of_vanishing_pSubgroups (A : Rep.{u} ℤ G) (n : ℤ)
    (h : TateVanishingOnPSubgroups A n) : IsZero (tate A n) := by
  have hzero (x : tate A n) : x = 0 := by
    classical
    by_contra hx
    have ho : addOrderOf x ≠ 1 := fun hz => hx (AddMonoid.addOrderOf_eq_one_iff.mp hz)
    obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd ho
    let : Fact p.Prime := ⟨hp⟩
    let P : Sylow p G := Classical.choice inferInstance
    let S : Subgroup G := P
    let : Fintype (G ⧸ S) := Fintype.ofFinite _
    have hz : IsZero (tate (Rep.res S.subtype A) n) := h p S P.isPGroup
    have : Subsingleton (tate (Rep.res S.subtype A) n) := ModuleCat.subsingleton_of_isZero hz
    have hres : tateRestrict S A n x = 0 := Subsingleton.elim _ _
    have hkill : P.index • x = 0 := by
      change S.index • x = 0
      rw [← tateCorestrict_restrict S n A x, hres, map_zero]
    exact P.not_dvd_index (hpx.trans (addOrderOf_dvd_of_nsmul_eq_zero hkill))
  have : Subsingleton (tate A n) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Two consecutive Tate vanishings on all `p`-subgroups imply that the
original whole-group Tate group vanishes in every integer degree. -/
theorem tate_isZero_of_adjacent_pSubgroups (A : Rep.{u} ℤ G) (q n : ℤ)
    (h₀ : TateVanishingOnPSubgroups A q) (h₁ : TateVanishingOnPSubgroups A (q + 1)) :
    IsZero (tate A n) :=
  tate_isZero_of_vanishing_pSubgroups A n (tateVanishingOnPSubgroups_of_adjacent A q n h₀ h₁)

end IntegralGroupCohomology.Universe
