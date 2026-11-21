/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Sylow
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CyclicIdeleClassFundamental
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassH2Tower
public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupTransfer
public import Nyll.GaloisCohomology.GroupTheory.FiniteExactSequence
public import Nyll.ProCGroups.ProP.FinitePGroupMaximal

/-!
# The second inequality on the actual idèle class cohomology

A cyclic quotient of a finite `p`-group and degree-two inflation–restriction
give the divisibility bound by induction. The product of Sylow restrictions
then gives finiteness and divisibility for every finite Galois extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IntegralGroupCohomology.Universe
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

private theorem natCard_dvd_mul_of_ker_le_range
    {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (f : X →+ Y) (g : Y →+ Z) (h : g.ker ≤ f.range) :
    Nat.card Y ∣ Nat.card X * Nat.card Z := by
  rw [← g.ker.card_mul_index, AddSubgroup.index_ker]
  exact mul_dvd_mul ((AddSubgroup.card_dvd_of_le h).trans (AddSubgroup.card_range_dvd f))
    (AddSubgroup.card_addSubgroup_dvd_card g.range)

private theorem standardIdeleClassH2_card_cyclic
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    Finite (groupCohomology (standardIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (standardIdeleClassRep K L) 2) = Module.finrank K L := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e := cyclicGlobalIdeleClassH2EquivArtin K L g hg
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, (Nat.card_congr e.toEquiv).trans ?_⟩
  exact IsGalois.card_aut_eq_finrank K L

private theorem standardIdeleClassH2_dvd_pGroup_aux {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    IsPGroup p Gal(L/K) → Module.finrank K L = n →
      Finite (groupCohomology (standardIdeleClassRep K L) 2) ∧
        Nat.card (groupCohomology (standardIdeleClassRep K L) 2) ∣ Module.finrank K L := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro K L _ _ _ _ _ _ _ hP hDegree
    by_cases hcyc : IsCyclic Gal(L/K)
    · let : IsCyclic Gal(L/K) := hcyc
      obtain ⟨hf, hc⟩ := standardIdeleClassH2_card_cyclic K L
      exact ⟨hf, hc.dvd⟩
    let : Nontrivial Gal(L/K) := not_subsingleton_iff_nontrivial.mp (fun h => by
      let : Subsingleton Gal(L/K) := h
      exact hcyc inferInstance)
    obtain ⟨S, hS⟩ := IsCoatomic.exists_coatom (Subgroup Gal(L/K))
    let : S.Normal := ClassFieldTower.ProP.isCoatom_normal_of_isPGroup hP hS
    let E := IntermediateField.fixedField S
    let : NumberField E := NumberField.of_module_finite K E
    let : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite K E L
    let : IsGalois K E := IsGalois.of_fixedField_normal_subgroup S
    let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
    let : IsCyclic (Gal(L/K) ⧸ S) := ClassFieldTower.ProP.quotient_isCyclic_of_isCoatom hS
    let e := IsGalois.normalAutEquivQuotient S
    let : IsCyclic Gal(E/K) := isCyclic_of_surjective e.toMonoidHom e.surjective
    obtain ⟨hFinBot, hCardBot⟩ := standardIdeleClassH2_card_cyclic K E
    have hTopDegree : Module.finrank E L < n := by
      rw [IntermediateField.finrank_fixedField_eq_card S, ← hDegree,
        ← IsGalois.card_aut_eq_finrank K L,
        ← Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup Gal(L/K)) ≃* Gal(L/K)).toEquiv]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hS.ne_top)
    obtain ⟨hFinTop, hDvdTop⟩ := ih _ hTopDegree E L
      ((hP.to_subgroup S).of_equiv (IntermediateField.subgroupEquivAlgEquiv S)) rfl
    let : Finite (groupCohomology (standardIdeleClassRep K E) 2) := hFinBot
    let : Finite (groupCohomology (standardIdeleClassRep E L) 2) := hFinTop
    let f := (standardIdeleClassH2Inflate K L E).hom.toAddMonoidHom
    let g := (standardIdeleClassH2Restrict K L E).hom.toAddMonoidHom
    have h := standardIdeleClassH2Restrict_ker_le_inflate_range K L E
    refine ⟨(f.finite_natCard_le_mul_of_ker_le_range g h).1, ?_⟩
    exact (natCard_dvd_mul_of_ker_le_range f g h).trans
      ((mul_dvd_mul hCardBot.dvd hDvdTop).trans (Module.finrank_mul_finrank K E L).dvd)

/-- The second inequality for every finite Galois number-field extension.
Degree-two cohomology of the standard idèle classes is finite, and its order
divides the degree of the extension. -/
theorem standardIdeleClassH2_finite_card_dvd
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Finite (groupCohomology (standardIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (standardIdeleClassRep K L) 2) ∣ Module.finrank K L := by
  classical
  let G := Gal(L/K)
  let A := standardIdeleClassRep K L
  let I := (Nat.card G).primeFactors
  let P (p : I) : Sylow p.val G := by
    let : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    exact Classical.choice inferInstance
  let B (p : I) := Rep.res (P p).1.subtype A
  let T (p : I) := tate (B p) 2
  have hLocal (p : I) : Finite (T p) ∧
      Nat.card (T p) ∣ p.val ^ (Nat.card G).factorization p.val := by
    let : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    let E := IntermediateField.fixedField (P p).1
    let : NumberField E := NumberField.of_module_finite K E
    let : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite K E L
    let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
    let e := IntermediateField.subgroupEquivAlgEquiv (P p).1
    let c := groupCohomology.mapIso (A := standardIdeleClassRep E L) (B := B p) e
      (LinearEquiv.refl ℤ (standardIdeleClassRep E L)) (fun _ => rfl) 2
    let t : T p ≅ groupCohomology (standardIdeleClassRep E L) 2 :=
      tatePositiveIsoCohomology (B p) 2 ≪≫ cohomologyIsoOriginal (B p) 2 ≪≫ c
    obtain ⟨hf, hc⟩ := standardIdeleClassH2_dvd_pGroup_aux (Module.finrank E L) E L
      ((P p).isPGroup.of_equiv e) rfl
    let : Finite (groupCohomology (standardIdeleClassRep E L) 2) := hf
    have hdeg : Module.finrank E L = p.val ^ (Nat.card G).factorization p.val :=
      (IntermediateField.finrank_fixedField_eq_card (P p).1).trans (P p).card_eq_multiplicity
    refine ⟨Finite.of_equiv _ t.symm.toLinearEquiv.toEquiv, ?_⟩
    exact (Nat.card_congr t.toLinearEquiv.toEquiv).dvd.trans (hc.trans hdeg.dvd)
  let : ∀ p : I, Finite (T p) := fun p => (hLocal p).1
  let res (p : I) : tate A 2 →ₗ[ℤ] T p := by
    let : Fintype (G ⧸ (P p).1) := Fintype.ofFinite _
    exact tateRestrict (P p).1 A 2
  let f : tate A 2 →+ ∀ p : I, T p :=
    { toFun := fun x p => res p x
      map_zero' := funext fun p => map_zero (res p)
      map_add' := fun x y => funext fun p => map_add (res p) x y }
  have hkill (x : tate A 2) : Nat.card G • x = 0 := by
    let S := (⊥ : Subgroup G)
    let : Fintype (G ⧸ S) := Fintype.ofFinite _
    let D := Rep.res S.subtype A
    let t := tatePositiveIsoCohomology D 2 ≪≫ cohomologyIsoOriginal D 2
    have hzero : IsZero (groupCohomology D 2) :=
      isZero_groupCohomology_succ_of_subsingleton D 1
    let : Subsingleton (tate D 2) := ModuleCat.subsingleton_of_isZero (hzero.of_iso t)
    have hz : tateRestrict S A 2 x = 0 := Subsingleton.elim _ _
    rw [← Subgroup.index_bot, ← tateCorestrict_restrict S 2 A x, hz, map_zero]
  have hInjective : Function.Injective f := by
    apply (AddMonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    change x = 0
    by_contra hne
    have hn : addOrderOf x ≠ 1 := fun h => hne (AddMonoid.addOrderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hn
    let q : I := ⟨p, Nat.mem_primeFactors.mpr
      ⟨hp, hd.trans (addOrderOf_dvd_of_nsmul_eq_zero (hkill x)), Nat.card_pos.ne'⟩⟩
    let : Fact q.val.Prime := ⟨hp⟩
    let : Fintype (G ⧸ (P q).1) := Fintype.ofFinite _
    have hz : tateRestrict (P q).1 A 2 x = 0 := congrFun hx q
    have hindex : (P q).index • x = 0 := by
      rw [← tateCorestrict_restrict (P q).1 2 A x, hz, map_zero]
    exact (P q).not_dvd_index (hd.trans (addOrderOf_dvd_of_nsmul_eq_zero hindex))
  let : Finite (tate A 2) := Finite.of_injective f hInjective
  let t : tate A 2 ≅ groupCohomology A 2 :=
    tatePositiveIsoCohomology A 2 ≪≫ cohomologyIsoOriginal A 2
  refine ⟨Finite.of_equiv _ t.toLinearEquiv.toEquiv, ?_⟩
  rw [← Nat.card_congr t.toLinearEquiv.toEquiv, ← IsGalois.card_aut_eq_finrank K L]
  apply (AddSubgroup.card_dvd_of_injective f hInjective).trans
  rw [Nat.card_pi, Nat.prod_primeFactors_coe_pow_factorization (Nat.card_pos (α := G)).ne']
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun p _ => (hLocal p).2)

end GlobalClassFieldTheory.Cohomology
