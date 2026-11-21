/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Ring.GeomSum
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalWildRestriction
public import Nyll.GaloisCohomology.GroupTheory.ModularTameMonomial
public import Nyll.GaloisCohomology.GroupTheory.MonomialInduction
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianNormality
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationCharacterization
public import Nyll.ValuedFieldTheory.Ramification.LocalField.Solvable
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
public import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness

/-! # Monomial representations of tame finite local Galois groups -/

@[expose] public section

noncomputable section

open scoped ValuativeRel
open Polynomial LocalFieldTheory
open RamificationTheory.HilbertRamification.CompleteDVF
open RamificationTheory.HilbertRamification.ValuationSubring

namespace ClassFieldTheory.Brauer

private theorem isCyclic_valuationQuotient {L Γ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) [v.IsRankOneDiscrete] :
    IsCyclic (Lˣ ⧸ v.valuationSubring.unitGroup) := by
  let ν : Lˣ →* Γˣ := Units.map v.toMonoidWithZeroHom.toMonoidHom
  have hker : ν.ker = v.valuationSubring.unitGroup := by
    ext x
    rw [MonoidHom.mem_ker, v.mem_unitGroup_iff]
    exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩
  have hvalue : ν.range ≤ v.valueGroup := by
    rintro _ ⟨x, rfl⟩
    exact MonoidWithZeroHom.mem_valueGroup _ ⟨x.val, rfl⟩
  let : IsCyclic ν.range := Subgroup.isCyclic_of_le hvalue
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange ν)).isCyclic.mpr inferInstance

private theorem isCyclic_monoidHom {A B : Type*} [Group A] [IsCyclic A]
    [CommGroup B] [IsCyclic B] : IsCyclic (A →* B) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  let e : (A →* B) →* B := {
    toFun := fun f => f a
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  apply isCyclic_of_injective e
  intro f g hfg
  change f a = g a at hfg
  apply MonoidHom.ext
  intro x
  obtain ⟨m, hm⟩ := (Subgroup.mem_zpowers_iff.mp (ha x))
  rw [← hm, map_zpow, map_zpow, hfg]

private theorem localInertiaQuotient_isCyclic (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    let A := (localCompleteDVF L).valuation.valuationSubring
    IsCyclic ((inertiaGroup K A) ⧸ ramificationGroup K A) := by
  let target := localCompleteDVF L
  let A := target.valuation.valuationSubring
  let I := inertiaGroup K A
  let W := ramificationGroup K A
  let U := valueTrivialInertiaGroup K A
  let Q := ramificationGroupInValueTrivialInertiaGroup K A
  let χ := valueTrivialInertiaCharacterHom K A
  let : IsCyclic (Lˣ ⧸ A.unitGroup) := isCyclic_valuationQuotient target.valuation
  let : IsCyclic ((Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A) :=
    isCyclic_of_surjective _ (QuotientGroup.mk'_surjective _)
  let : Finite (IsLocalRing.ResidueField A) := by
    change Finite 𝓀[L]
    infer_instance
  let : IsCyclic ((Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A →*
      (IsLocalRing.ResidueField A)ˣ) := isCyclic_monoidHom
  let : IsCyclic χ.range := inferInstance
  let e : U ≃* I :=
    (MulEquiv.subgroupCongr (valueTrivialInertiaGroup_eq_top_of_finite K A)).trans Subgroup.topEquiv
  have hmap : Q.map e.toMonoidHom = W := by
    ext i
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hi
      obtain ⟨j, rfl⟩ := e.surjective i
      exact ⟨j, hi, rfl⟩
  let q := valueTrivialInertiaQuotientRamificationEquivCharacterRange K A
  let : IsCyclic (U ⧸ Q) := q.isCyclic.mpr inferInstance
  exact (QuotientGroup.congr Q W e hmap).isCyclic.mp inferInstance

/-- Every simple representation on which actual wild inertia acts trivially admits a
monomial basis over a field splitting the group order power polynomial. -/
theorem exists_localTameMonomialBasis_of_wildFixed (K L k V : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k Gal(L/K) V) [Representation.IsIrreducible ρ]
    (hfix : ∀ g : ramificationGroupInAut K (localCompleteDVF L).valuation.valuationSubring,
      ∀ x : V, ρ g.val x = x)
    (hsplit : Splits ((X : k[X]) ^ Nat.card Gal(L/K) - C 1)) :
    ∃ S : Set k, ∃ b : Module.Basis S k V,
      ∀ g : Gal(L/K), ∀ j : S, ∃ j' : S, ∃ c : k, c ≠ 0 ∧ ρ g (b j) = c • b j' := by
  let base := localCompleteDVF K
  let target := localCompleteDVF L
  let : base.valuation.HasExtension target.valuation := localCompleteDVFValuation_hasExtension K L
  let A := target.valuation.valuationSubring
  let I := inertiaGroup K A
  let W := ramificationGroup K A
  let WD := ramificationGroupInDecomposition K A
  let : WD.Normal := ramificationGroup_map_inertiaSubtype_normal K A
  let e := galEquivDecompositionGroup (base := base) (target := target)
  let P := WD.comap e.toMonoidHom
  let r₀ := decompositionResidueAction (K := K) (base := base) (target := target)
  let r := r₀.comp e.toMonoidHom
  let J := r.ker
  have hJ : J = I.comap e.toMonoidHom := by
    change (r₀.comp e.toMonoidHom).ker = I.comap e.toMonoidHom
    change r₀.ker.comap e.toMonoidHom = I.comap e.toMonoidHom
    rw [show r₀.ker = I from decompositionResidueAction_ker (base := base) (target := target)]
  have hPJ : P ≤ J := by
    rw [hJ]
    intro g hg
    change e g ∈ WD at hg
    obtain ⟨i, _, hi⟩ := hg
    change e g ∈ I
    rw [← hi]
    exact i.property
  have hP : P ≤ ρ.ker := by
    intro g hg
    change e g ∈ WD at hg
    obtain ⟨i, hi, hgi⟩ := hg
    have hgW : g ∈ ramificationGroupInAut K A :=
      ⟨i, hi, congrArg Subtype.val hgi⟩
    exact MonoidHom.mem_ker.mpr (LinearMap.ext (hfix ⟨g, hgW⟩))
  let q := QuotientGroup.mk' P
  let i := q.comp J.subtype
  let T := i.range
  let : T.Normal := by
    change (q.comp J.subtype).range.Normal
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact (inferInstance : J.Normal).map q (QuotientGroup.mk'_surjective P)
  let rbar := QuotientGroup.lift P r hPJ
  have hT : T = rbar.ker := by
    ext x
    obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective P) x
    constructor
    · rintro ⟨z, hz⟩
      change q z.val = q g at hz
      change rbar (q g) = 1
      rw [← hz]
      exact (QuotientGroup.lift_mk' P (φ := r) hPJ z.val).trans z.property
    · intro hg
      have hgJ : g ∈ J := (QuotientGroup.lift_mk' P (φ := r) hPJ g).symm.trans hg
      exact ⟨⟨g, hgJ⟩, rfl⟩
  let : Finite target.residueField := by
    change Finite 𝓀[L]
    infer_instance
  let : IsCyclic ((Gal(L/K) ⧸ P) ⧸ T) :=
    ((QuotientGroup.quotientMulEquivOfEq hT).trans
      (QuotientGroup.quotientKerEquivRange rbar)).isCyclic.mpr inferInstance
  let j : J ≃* I := (MulEquiv.subgroupCongr hJ).trans
    (MulEquiv.ofBijective (e.toMonoidHom.subgroupComap I)
      ⟨e.toMonoidHom.subgroupComap_injective I e.injective,
        e.toMonoidHom.subgroupComap_surjective I e.surjective⟩)
  have hj (z : J) : z ∈ i.ker ↔ j z ∈ W := by
    change ((z.val : Gal(L/K)) : Gal(L/K) ⧸ P) = 1 ↔ j z ∈ W
    rw [QuotientGroup.eq_one_iff]
    have hz : (j z).val = e z.val := rfl
    change e z.val ∈ WD ↔ j z ∈ W
    constructor
    · rintro ⟨a, ha, ham⟩
      have haj : a = j z := Subtype.ext (ham.trans hz.symm)
      exact haj ▸ ha
    · intro hzW
      exact ⟨j z, hzW, hz⟩
  have hW : i.ker.map j.toMonoidHom = W := by
    ext a
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hj z).mp hz
    · intro ha
      obtain ⟨z, rfl⟩ := j.surjective a
      exact ⟨z, (hj z).mpr ha, rfl⟩
  let : IsCyclic (I ⧸ W) := localInertiaQuotient_isCyclic K L
  let : IsCyclic T := ((QuotientGroup.quotientKerEquivRange i).symm.trans
    (QuotientGroup.congr i.ker W j hW)).isCyclic.mpr inferInstance
  have hdiv : (X : k[X]) ^ Nat.card (Gal(L/K) ⧸ P) - C 1 ∣
      (X : k[X]) ^ Nat.card Gal(L/K) - C 1 := by
    simpa only [Polynomial.C_1] using
      dvd_pow_sub_one_of_dvd (r := (X : k[X])) (Subgroup.card_quotient_dvd_card P)
  exact Representation.exists_tameMonomialBasis_of_ker_le ρ P hP T
    (hsplit.of_dvd (X_pow_sub_C_ne_zero Nat.card_pos 1) hdiv)

/-- A simple representation on which wild inertia acts trivially is literally
induced from a one-dimensional character over an actual intermediate local field. -/
theorem exists_localTameInducedCharacter_of_wildFixed (K L k V : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k Gal(L/K) V) [Representation.IsIrreducible ρ]
    (hfix : ∀ g : ramificationGroupInAut K (localCompleteDVF L).valuation.valuationSubring,
      ∀ x : V, ρ g.val x = x)
    (hsplit : Splits ((X : k[X]) ^ Nat.card Gal(L/K) - C 1)) :
    ∃ E : IntermediateField K L, ∃ χ : E.fixingSubgroup →* k,
      Nonempty (Representation.Equiv
        (Representation.ind E.fixingSubgroup.subtype ((Algebra.lsmul k k k).toMonoidHom.comp χ))
        ρ) := by
  obtain ⟨S, b, hmonomial⟩ := exists_localTameMonomialBasis_of_wildFixed K L k V ρ hfix hsplit
  obtain ⟨j₀⟩ := b.index_nonempty
  obtain ⟨H, χ, e⟩ := Representation.exists_induced_of_simple_monomial ρ b j₀ hmonomial
  refine ⟨IntermediateField.fixedField H, ?_⟩
  rw [IntermediateField.fixingSubgroup_fixedField H]
  exact ⟨χ, e⟩

private theorem localCompleteDVFValuationSubring_hasExtension (K L : Type*) [Field K] [Field L]
    [Algebra K L] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    (localCompleteDVF K).valuation.valuationSubring.valuation.HasExtension
      (localCompleteDVF L).valuation.valuationSubring.valuation := by
  let v := (localCompleteDVF K).valuation
  let w := (localCompleteDVF L).valuation
  let : v.HasExtension w := localCompleteDVFValuation_hasExtension K L
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change w.valuationSubring.valuation (algebraMap K L x) ≤ 1 ↔
    v.valuationSubring.valuation x ≤ 1
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
  exact Valuation.HasExtension.val_map_le_one_iff v w x

/-- When the inflated action fixes every element of actual absolute wild inertia,
the original finite representation is induced from a scalar character of an
actual intermediate local field. -/
theorem exists_localTameInducedCharacter_of_absoluteWildFixed
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    (W : ValuationSubring (SeparableClosure K))
    [(localCompleteDVF K).valuation.valuationSubring.valuation.HasExtension W.valuation]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField W) p]
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k Gal(E/K) V) [Representation.IsIrreducible ρ]
    (hfix : ∀ g : ramificationGroupInAut K W, ∀ x : V, ρ (finiteGaloisRestriction E g.val) x = x)
    (hsplit : Splits ((X : k[X]) ^ Nat.card Gal(E/K) - C 1)) :
    ∃ F : IntermediateField K E, ∃ χ : F.fixingSubgroup →* k,
      Nonempty (Representation.Equiv
        (Representation.ind F.fixingSubgroup.subtype ((Algebra.lsmul k k k).toMonoidHom.comp χ))
        ρ) := by
  let A := (localCompleteDVF K).valuation.valuationSubring
  let B := (localCompleteDVF E).valuation.valuationSubring
  let : HenselianRing A (IsLocalRing.maximalIdeal A) := (localCompleteDVF K).henselianRing
  let : A.valuation.HasExtension B.valuation := localCompleteDVFValuationSubring_hasExtension K E
  let w := W.valuation.comap E.toIntermediateField.val.toRingHom
  let : A.valuation.HasExtension w :=
    _root_.DiscreteValuationField.Valuation.comap_to_middle_hasExtension_of_top_hasExtension
      A.valuation W.valuation
  have hw : w.valuationSubring = W.comap E.toIntermediateField.val.toRingHom := by
    ext x
    change W.valuation (E.toIntermediateField.val x) ≤ 1 ↔ E.toIntermediateField.val x ∈ W
    exact W.valuation_le_one_iff (E.val x)
  have hB : W.comap E.toIntermediateField.val.toRingHom = B :=
    hw.symm.trans ((ValuationTheory.Henselian.valuationSubring_eq_of_henselianRing
      A w B.valuation).trans
      (ValuationSubring.valuationSubring_valuation B))
  have hmap := localWild_finiteGaloisRestriction_map A W E p
  rw [hB] at hmap
  apply exists_localTameInducedCharacter_of_wildFixed K E k V ρ _ hsplit
  intro g x
  have hg : g.val ∈ (ramificationGroupInAut K W).map (finiteGaloisRestriction E).toMonoidHom := by
    rw [hmap]
    exact g.property
  obtain ⟨σ, hσ, hσg⟩ := hg
  exact (congrArg (fun τ => ρ τ x) hσg).symm.trans (hfix ⟨σ, hσ⟩ x)

private theorem localWild_fixed_in_residueChar (K L k V : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Field k] [Finite k] [CharP k (ringChar 𝓀[L])]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k Gal(L/K) V) [Representation.IsIrreducible ρ] :
    ∀ g : ramificationGroupInAut K (localCompleteDVF L).valuation.valuationSubring,
      ∀ x : V, ρ g.val x = x := by
  let base := localCompleteDVF K
  let target := localCompleteDVF L
  let A := target.valuation.valuationSubring
  let B := base.valuation.valuationSubring
  let : HenselianRing B (IsLocalRing.maximalIdeal B) := base.henselianRing
  let : B.valuation.HasExtension A.valuation := localCompleteDVFValuationSubring_hasExtension K L
  let P := ramificationGroupInAut K A
  let : P.Normal := ramificationGroupInAut_normal_of_henselianRing K B A
  let p := ringChar 𝓀[L]
  let : Fact p.Prime := ⟨CharP.prime_ringChar 𝓀[L]⟩
  let : CharP target.residueField p := ringChar.charP target.residueField
  let : Finite V := Module.finite_of_finite k
  have hP : IsPGroup p P :=
    (ramificationGroup_isPGroup_of_residueChar K A p).of_surjective
      (ramificationGroupEquivInAut K A).toMonoidHom (ramificationGroupEquivInAut K A).surjective
  exact Representation.isTrivial_restrict_of_normal_isPGroup_charP ρ P hP

/-- Every simple representation of the original finite local Galois group in
residue characteristic admits a monomial basis over a splitting field. -/
theorem exists_localTameMonomialBasis (K L k V : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Field k] [Finite k] [CharP k (ringChar 𝓀[L])]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k Gal(L/K) V) [Representation.IsIrreducible ρ]
    (hsplit : Splits ((X : k[X]) ^ Nat.card Gal(L/K) - C 1)) :
    ∃ S : Set k, ∃ b : Module.Basis S k V,
      ∀ g : Gal(L/K), ∀ j : S, ∃ j' : S, ∃ c : k, c ≠ 0 ∧ ρ g (b j) = c • b j' :=
  exists_localTameMonomialBasis_of_wildFixed K L k V ρ
    (localWild_fixed_in_residueChar K L k V ρ) hsplit

/-- A simple representation in residue characteristic is literally induced
from a one-dimensional character over an actual intermediate local field. -/
theorem exists_localTameInducedCharacter (K L k V : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Field k] [Finite k] [CharP k (ringChar 𝓀[L])]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k Gal(L/K) V) [Representation.IsIrreducible ρ]
    (hsplit : Splits ((X : k[X]) ^ Nat.card Gal(L/K) - C 1)) :
    ∃ E : IntermediateField K L, ∃ χ : E.fixingSubgroup →* k,
      Nonempty (Representation.Equiv
        (Representation.ind E.fixingSubgroup.subtype ((Algebra.lsmul k k k).toMonoidHom.comp χ))
        ρ) :=
  exists_localTameInducedCharacter_of_wildFixed K L k V ρ
    (localWild_fixed_in_residueChar K L k V ρ) hsplit

end ClassFieldTheory.Brauer
