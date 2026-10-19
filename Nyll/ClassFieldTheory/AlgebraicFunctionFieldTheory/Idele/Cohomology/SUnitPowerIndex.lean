/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnitHerbrandFormula
import Nyll.GaloisCohomology.Cyclic.Herbrand.TrivialAction

/-!
# Power index of actual S-units

S-units are saturated with respect to taking roots in the base field.
Their power kernel is the actual group of roots of unity. The established
S-unit Herbrand formula, applied to the trivial cyclic action, computes the
power index without adding a second proof of the S-unit rank theorem.
-/

noncomputable section

namespace FunctionField.SUnits

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- A root in the base field of an S-unit is again an S-unit. -/
theorem mem_units_of_pow_mem (S : Finset (Place k K)) (n : ℕ) (hn : n ≠ 0)
    (a : Kˣ) (ha : a ^ n ∈ units k K S) : a ∈ units k K S := by
  intro v hv
  have h := ha v hv
  rw [Units.val_pow_eq_pow_val, ← zpow_natCast, v.ord_zpow] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr hn)

/-- The power kernel of actual S-units is exactly the roots of unity of the field. -/
def powerKernelEquivRootsOfUnity (S : Finset (Place k K)) (n : ℕ) (hn : n ≠ 0) :
    (powMonoidHom (α := units k K S) n).ker ≃* rootsOfUnity n K where
  toFun a := ⟨a.val.val, (mem_rootsOfUnity n a.val.val).mpr
    (congrArg Subtype.val a.property)⟩
  invFun a := ⟨⟨a.val, mem_units_of_pow_mem S n hn a.val (by
    rw [(mem_rootsOfUnity n a.val).mp a.property]
    exact (units k K S).one_mem)⟩, Subtype.ext ((mem_rootsOfUnity n a.val).mp a.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- If the required roots of unity are in the field, the S-unit power kernel has order n. -/
theorem card_powerKernel (S : Finset (Place k K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card (powMonoidHom (α := units k K S) (n : ℕ)).ker = (n : ℕ) := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hmu
  exact (Nat.card_congr (powerKernelEquivRootsOfUnity S n n.ne_zero).toEquiv).trans
    (isPrimitiveRoot_of_mem_primitiveRoots hζ).card_rootsOfUnity

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- The S-unit power quotient is finite, and its order is determined by
the actual power kernel and the number of places in S. -/
theorem finite_card_powerQuotient (S : Finset (Place k K)) (hS : S.Nonempty) (n : ℕ+) :
    Finite (units k K S ⧸ (powMonoidHom (α := units k K S) (n : ℕ)).range) ∧
      Nat.card (units k K S ⧸ (powMonoidHom (α := units k K S) (n : ℕ)).range) * (n : ℕ) =
        (n : ℕ) ^ S.card * Nat.card (powMonoidHom (α := units k K S) (n : ℕ)).ker := by
  classical
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let G := Multiplicative (ZMod (n : ℕ))
  let ρ : G →* stabilizer k K S := 1
  let hPlace : MulAction G S := MulAction.compHom S ρ
  let hUnits : MulDistribMulAction G (units k K S) := unitsAction S ρ
  let hOrbits : Fintype (MulAction.orbitRel.Quotient G S) := Fintype.ofFinite _
  have hGcard : Fintype.card G = (n : ℕ) := by
    simp only [G, Fintype.card_multiplicative, ZMod.card]
  have hGcardNat : Nat.card G = (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hGcard]
  have hplace (g : G) (v : S) : g • v = v := by
    change (1 : stabilizer k K S) • v = v
    exact one_smul _ v
  have hunits (g : G) (a : units k K S) : g • a = a := by
    change (1 : stabilizer k K S) • a = a
    exact one_smul _ a
  let eOrbits : S ≃ MulAction.orbitRel.Quotient G S :=
    Equiv.ofBijective Quotient.mk'' ⟨by
      intro x y h
      obtain ⟨g, hg⟩ := Quotient.exact h
      exact hg.symm.trans (hplace g y),
      Quotient.mk''_surjective⟩
  have hOrbitCard : Fintype.card (MulAction.orbitRel.Quotient G S) = S.card := by
    rw [← Fintype.card_congr eOrbits, Fintype.card_coe]
  have hStabCard (ω : MulAction.orbitRel.Quotient G S) :
      Nat.card (permutationOrbitStabilizer ω) = (n : ℕ) := by
    have htop : permutationOrbitStabilizer ω = ⊤ := by
      ext g
      exact ⟨fun _ => trivial, fun _ => hplace g ω.out⟩
    exact (Nat.card_congr ((MulEquiv.subgroupCongr htop).trans
      Subgroup.topEquiv).toEquiv).trans hGcardNat
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨hU, hformula⟩ := units_herbrandQuotient S hS ρ σ hgen
  have hU0 : Finite (HerbrandH0 G (units k K S)) := hU.1
  have hUm : Finite (HerbrandHMinusOne G (units k K S) σ) := hU.2
  have h0 : Nat.card (HerbrandH0 G (units k K S)) =
      Nat.card (units k K S ⧸ (powMonoidHom (α := units k K S) (n : ℕ)).range) := by
    rw [Nat.card_congr (herbrandH0EquivPowQuotient_of_trivial hunits).toEquiv, hGcard]
  have hm : Nat.card (HerbrandHMinusOne G (units k K S) σ) =
      Nat.card (powMonoidHom (α := units k K S) (n : ℕ)).ker := by
    rw [Nat.card_congr (herbrandHMinusOneEquivPowKernel_of_trivial hunits σ).toEquiv,
      hGcard]
  have hprod : (∏ ω : MulAction.orbitRel.Quotient G S,
      (Nat.card (permutationOrbitStabilizer ω) : ℚ)) = (n : ℚ) ^ S.card := by
    simp only [hStabCard, Finset.prod_const, Finset.card_univ, hOrbitCard]
  have hf : herbrandQuotient (G := G) (A := units k K S) σ =
      (∏ ω : MulAction.orbitRel.Quotient G S,
        (Nat.card (permutationOrbitStabilizer ω) : ℚ)) / (Nat.card G : ℚ) := hformula
  rw [herbrandQuotient_eq_card_ratio, h0, hm, hprod, hGcardNat] at hf
  have hkerpos : 0 < Nat.card (powMonoidHom (α := units k K S) (n : ℕ)).ker := by
    rw [← hm]
    exact Nat.card_pos
  have hquotpos : 0 < Nat.card
      (units k K S ⧸ (powMonoidHom (α := units k K S) (n : ℕ)).range) := by
    rw [← h0]
    exact Nat.card_pos
  refine ⟨Nat.finite_of_card_ne_zero hquotpos.ne', ?_⟩
  have h := (div_eq_div_iff
    (Nat.cast_ne_zero.mpr hkerpos.ne' : (Nat.card
      (powMonoidHom (α := units k K S) (n : ℕ)).ker : ℚ) ≠ 0)
    (Nat.cast_ne_zero.mpr n.ne_zero : (n : ℚ) ≠ 0)).mp hf
  exact_mod_cast h

/-- For nonempty S and a field containing the n-th roots of unity, the actual
S-unit power quotient has order n raised to the number of places in S. -/
theorem card_powerQuotient (S : Finset (Place k K)) (hS : S.Nonempty) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card (units k K S ⧸ (powMonoidHom (α := units k K S) (n : ℕ)).range) =
      (n : ℕ) ^ S.card := by
  have h := (finite_card_powerQuotient S hS n).2
  rw [card_powerKernel S n hmu] at h
  exact Nat.eq_of_mul_eq_mul_right n.pos h

/-- In characteristic p the power kernel is trivial, leaving S.card - 1
independent p-power classes. -/
theorem card_primePowerQuotient (S : Finset (Place k K)) (hS : S.Nonempty)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card (units k K S ⧸ (powMonoidHom (α := units k K S) p).range) =
      p ^ (S.card - 1) := by
  have hkernel : Nat.card (powMonoidHom (α := units k K S) p).ker = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, fun u => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply (frobenius K p).injective
    change (u.val.val : K) ^ p = (1 : K) ^ p
    have hu := congrArg (fun z : units k K S => (z.val : K)) u.property
    change ((u.val.val : K) ^ p) = 1 at hu
    simpa only [one_pow] using hu
  have h := (finite_card_powerQuotient S hS ⟨p, (Fact.out : p.Prime).pos⟩).2
  change Nat.card (units k K S ⧸ (powMonoidHom (α := units k K S) p).range) * p =
    p ^ S.card * Nat.card (powMonoidHom (α := units k K S) p).ker at h
  rw [hkernel, mul_one] at h
  apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
  rw [h, ← pow_succ, Nat.sub_add_cancel (Finset.card_pos.mpr hS)]

end FunctionField.SUnits
