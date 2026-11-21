/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteInflation
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle

/-! # The finite Galois stage of a prime-order additive character -/

@[expose] public section

noncomputable section

open ClassFieldTower.Cohomology

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K] {p : ℕ}

/-- A nonzero character with values in a cyclic group of prime order is onto. -/
theorem primeCharacter_surjective {G : Type*} [Group G] (hp : p.Prime)
    (χ : G →* Multiplicative (ZMod p)) (hχ : ∃ σ, χ σ ≠ 1) :
    Function.Surjective χ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ⟩ := hχ
  intro z
  have hz : (χ σ).toAdd ≠ 0 := fun h => hσ (Multiplicative.toAdd.injective h)
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (z.toAdd / (χ σ).toAdd)
  refine ⟨σ ^ m, Multiplicative.toAdd.injective ?_⟩
  rw [map_zpow]
  change m • (χ σ).toAdd = z.toAdd
  rw [zsmul_eq_mul, hm, div_mul_cancel₀ _ hz]

/-- A cyclic coordinate agrees with the given group equivalence when its
chosen generator is the preimage of one. -/
theorem exists_primeCoordinate_of_mulEquiv {G : Type*} [Group G] [Fintype G]
    (hp : p.Prime) (e : G ≃* Multiplicative (ZMod p)) :
    ∃ (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hd : Nat.card G = p),
      ∀ x, ZMod.castHom (show p ∣ Nat.card G by rw [hd]) (ZMod p)
        (finiteCyclicGeneratorCoordinate g hg x) = (e x).toAdd := by
  let : Fact p.Prime := ⟨hp⟩
  let g := e.symm (Multiplicative.ofAdd (1 : ZMod p))
  have hg (x : G) : x ∈ Subgroup.zpowers g := by
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (e x).toAdd
    refine ⟨m, e.injective (Multiplicative.toAdd.injective ?_)⟩
    rw [map_zpow, e.apply_symm_apply]
    change m • (1 : ZMod p) = (e x).toAdd
    simpa only [zsmul_eq_mul, mul_one] using hm
  have hd : Nat.card G = p := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod p)
  refine ⟨g, hg, hd, ?_⟩
  intro x
  obtain ⟨m, hm⟩ := hg x
  rw [← hm, finiteCyclicGeneratorCoordinate_zpow, map_intCast, map_zpow, e.apply_symm_apply]
  change (m : ZMod p) = m • (1 : ZMod p)
  rw [zsmul_eq_mul, mul_one]

/-- A nontrivial prime-order character cuts out a degree-prime cyclic stage,
and its value is the original cyclic coordinate for the lift of one. -/
theorem exists_primeCharacterStage (hp : p.Prime)
    (χ : Gal(SeparableClosure K/K) →* Multiplicative (ZMod p))
    (hN : IsOpen (χ.ker : Set Gal(SeparableClosure K/K)))
    (hχ : ∃ σ, χ σ ≠ 1) :
    ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (g : Gal(E/K))
      (hg : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers g)
      (hd : Nat.card Gal(E/K) = p),
      ∀ σ, (ZMod.castHom (show p ∣ Nat.card Gal(E/K) by rw [hd]) (ZMod p))
        (finiteCyclicGeneratorCoordinate g hg (finiteGaloisRestriction E σ)) = (χ σ).toAdd := by
  let N := χ.ker
  let C : ClosedSubgroup Gal(SeparableClosure K/K) := ⟨N, (⟨N, hN⟩ : OpenSubgroup _).isClosed⟩
  let F := IntermediateField.fixedField N
  have hfix : F.fixingSubgroup = N := InfiniteGalois.fixingSubgroup_fixedField C
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := F
      finiteDimensional := (InfiniteGalois.isOpen_iff_finite F).mp (hfix.symm ▸ hN)
      isGalois := (InfiniteGalois.normal_iff_isGalois F).mp (hfix.symm ▸ inferInstanceAs N.Normal) }
  let : FiniteDimensional K E := E.finiteDimensional
  let : Fintype Gal(E/K) := inferInstance
  let : C.toSubgroup.Normal := inferInstanceAs N.Normal
  let q : (Gal(SeparableClosure K/K) ⧸ N) ≃* Gal(E/K) :=
    InfiniteGalois.normalAutEquivQuotient C
  have hq (σ : Gal(SeparableClosure K/K)) :
      q (QuotientGroup.mk' N σ) = finiteGaloisRestriction E σ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    rw [finiteGaloisRestriction_commutes]
    change ((InfiniteGalois.normalAutEquivQuotient C σ) x : SeparableClosure K) = σ x
    rw [InfiniteGalois.normalAutEquivQuotient_apply]
    exact AlgEquiv.restrictNormalHom_apply F σ x
  have hsurj := primeCharacter_surjective hp χ hχ
  let e : Gal(E/K) ≃* Multiplicative (ZMod p) :=
    q.symm.trans (QuotientGroup.quotientKerEquivOfSurjective χ hsurj)
  have he (σ : Gal(SeparableClosure K/K)) : e (finiteGaloisRestriction E σ) = χ σ := by
    rw [← hq]
    change QuotientGroup.quotientKerEquivOfSurjective χ hsurj
      (q.symm (q (QuotientGroup.mk' N σ))) = _
    rw [q.symm_apply_apply]
    rfl
  obtain ⟨g, hg, hd, hs⟩ := exists_primeCoordinate_of_mulEquiv hp e
  exact ⟨E, g, hg, hd, fun σ => (hs (finiteGaloisRestriction E σ)).trans
    (congrArg Multiplicative.toAdd (he σ))⟩

end ClassFieldTheory.Brauer
