/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicNorm
public import Nyll.ClassFieldTheory.Algebra.Brauer.DiscreteRelative
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteInflation
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.GaloisCohomology.GroupTheory.FiniteExactSequence
public import Nyll.GaloisCohomology.Kummer.LiftedFiniteGaloisTowerUnitsH2
public import Nyll.ValuedFieldTheory.Ramification.LocalField.Solvable

/-! # Degree bounds for unit H² of finite local Galois extensions -/

@[expose] public section

open CategoryTheory ClassFieldTower.Cohomology LocalFieldTheory Module

noncomputable section

namespace ClassFieldTheory.Brauer

universe u v

/-- The actual unit H² of a cyclic local extension has order the field degree.
The identification compares the common norm kernels of two surjective maps. -/
theorem finiteCyclicLocalUnitsH2_card
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    Finite (groupCohomology (liftedGaloisUnitsRep K L) 2) ∧
      Nat.card (groupCohomology (liftedGaloisUnitsRep K L) 2) = finrank K L := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let : IsAbelianGalois K L := { is_comm.comm := mul_comm }
  let f := cyclicUnitClass K L g hg
  let a := LocalClassFieldTheory.abelianLocalArtinMonoidHom K L
  have hker : f.ker = a.toAdditive.ker := by
    ext x
    change cyclicUnitClass K L g hg (Additive.ofMul x.toMul) = 0 ↔ x.toMul ∈ a.ker
    rw [cyclicUnitClass_eq_zero_iff_norm,
      LocalClassFieldTheory.abelianLocalArtinMonoidHom_ker]
  let eF := QuotientAddGroup.quotientKerEquivOfSurjective f (cyclicUnitClass_surjective K L g hg)
  let e := eF.symm.trans ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective a.toAdditive
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom_surjective K L)))
  exact ⟨Finite.of_equiv _ e.symm.toEquiv,
    (Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr (Additive.toMul : Additive Gal(L/K) ≃ Gal(L/K))).trans
        (IsGalois.card_aut_eq_finrank K L))⟩

private theorem exists_proper_normal_of_isSolvable_of_not_isCyclic
    (G : Type*) [Group G] [Group.IsSolvable G] (hG : ¬ IsCyclic G) :
    ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ ∧ H < ⊤ := by
  rcases subsingleton_or_nontrivial G with hG' | hG'
  · exact False.elim (hG ((isCyclic_iff_exists_zpowers_eq_top).mpr ⟨1,
      (Subgroup.eq_top_iff' _).2 fun x => (Subsingleton.elim (1 : G) x) ▸
        (Subgroup.zpowers 1).one_mem⟩))
  · by_cases hc : commutator G = ⊥
    · let : CommGroup G :=
        Group.commGroupOfCenterEqTop ((commutator_eq_bot_iff_center_eq_top G).mp hc)
      obtain ⟨x, hx⟩ := exists_ne (1 : G)
      refine ⟨Subgroup.zpowers x, inferInstance, Subgroup.zpowers_ne_bot.mpr hx,
        lt_top_iff_ne_top.mpr ?_⟩
      exact fun he => hG (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, he⟩)
    · exact ⟨commutator G, inferInstance, hc, Group.IsSolvable.commutator_lt_top_of_nontrivial G⟩

private theorem finiteSolvableLocalUnitsH2_bound (n : ℕ) :
    ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K],
      Group.IsSolvable Gal(L/K) → finrank K L = n →
      Finite (groupCohomology (liftedGaloisUnitsRep K L) 2) ∧
        Nat.card (groupCohomology (liftedGaloisUnitsRep K L) 2) ≤ finrank K L := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro K L _ _ _ _ _ _ _ _ hSolv hdegree
    let : Group.IsSolvable Gal(L/K) := hSolv
    by_cases hcyc : IsCyclic Gal(L/K)
    · let : IsCyclic Gal(L/K) := hcyc
      obtain ⟨hfinite, hcard⟩ := finiteCyclicLocalUnitsH2_card K L
      exact ⟨hfinite, hcard.le⟩
    obtain ⟨H, hHNormal, hHBot, hHTop⟩ :=
      exists_proper_normal_of_isSolvable_of_not_isCyclic Gal(L/K) hcyc
    let : H.Normal := hHNormal
    let E := IntermediateField.fixedField H
    let : IsGalois K E := IsGalois.of_fixedField_normal_subgroup H
    let : IsGalois E L := IsGalois.of_fixed_field L H
    let eTop := IntermediateField.subgroupEquivAlgEquiv H
    let eBot := IsGalois.normalAutEquivQuotient H
    have hSolvTop : Group.IsSolvable Gal(L/E) :=
      Group.isSolvable_of_isSolvable_injective (f := eTop.symm.toMonoidHom) eTop.symm.injective
    have hSolvBot : Group.IsSolvable Gal(E/K) :=
      Group.isSolvable_of_isSolvable_injective (f := eBot.symm.toMonoidHom) eBot.symm.injective
    have hTopCard : finrank E L = Nat.card H := IntermediateField.finrank_fixedField_eq_card H
    have hTopDegree : finrank E L < n := by
      rw [hTopCard, ← hdegree, ← IsGalois.card_aut_eq_finrank K L,
        ← Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup Gal(L/K)) ≃* Gal(L/K)).toEquiv]
      exact Subgroup.card_lt_of_lt hHTop
    have hTopNontrivial : 1 < finrank E L := by
      rw [hTopCard, ← Subgroup.card_bot (G := Gal(L/K))]
      exact Subgroup.card_lt_of_lt (bot_lt_iff_ne_bot.mpr hHBot)
    have hBotDegree : finrank K E < n := by
      rw [← hdegree, ← finrank_mul_finrank K E L]
      exact lt_mul_of_one_lt_right finrank_pos hTopNontrivial
    obtain ⟨hFiniteBot, hBoundBot⟩ := ih _ hBotDegree K E hSolvBot rfl
    let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
    let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
    let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
    obtain ⟨hFiniteTop, hBoundTop⟩ := ih _ hTopDegree E L hSolvTop rfl
    let : Finite (groupCohomology (liftedGaloisUnitsRep K E) 2) := hFiniteBot
    let : Finite (groupCohomology (liftedGaloisUnitsRep E L) 2) := hFiniteTop
    let f := (liftedFiniteGaloisTowerUnitsH2Inflation K E L).hom.toAddMonoidHom
    let g := (liftedFiniteGaloisTowerUnitsH2Restriction K E L).hom.toAddMonoidHom
    obtain ⟨hFinite, hBound⟩ := f.finite_natCard_le_mul_of_ker_le_range g
      (liftedFiniteGaloisTowerUnitsH2Restriction_ker_le_inflation_range K E L)
    exact ⟨hFinite, (hBound.trans (Nat.mul_le_mul hBoundBot hBoundTop)).trans
      (finrank_mul_finrank K E L).le⟩

/-- Degree-two cohomology of the actual field units in a finite local Galois
extension is finite with order at most the extension degree. -/
theorem finiteLocalUnitsH2_finite_card_le
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Finite (groupCohomology (liftedGaloisUnitsRep K L) 2) ∧
      Nat.card (groupCohomology (liftedGaloisUnitsRep K L) 2) ≤ finrank K L :=
  finiteSolvableLocalUnitsH2_bound (finrank K L) K L
    (RamificationTheory.LocalField.localGaloisGroup_isSolvable K L) rfl

/-- The same bound holds for the continuous relative Brauer group. -/
theorem relativeBr_finite_card_le (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    Finite (relativeBr E) ∧ Nat.card (relativeBr E) ≤ finrank K E := by
  obtain ⟨hfinite, hcard⟩ := finiteLocalUnitsH2_finite_card_le K E
  let : Finite (groupCohomology (liftedGaloisUnitsRep K E) 2) := hfinite
  let e := continuousRelativeUnitsH2Equiv K E
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, (Nat.card_congr e.toEquiv).le.trans hcard⟩

end ClassFieldTheory.Brauer
