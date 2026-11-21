/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralNormKernelVanishing
public import Nyll.GaloisCohomology.Cyclic.IntegralTateAbelianization
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInflation
public import Nyll.GaloisCohomology.ProP.H1NormalSubgroupDescent

/-!
# The degree-one Tate criterion on a normal quotient

The actual integral degree-one cohomology class vanishes exactly when the
same original cocycle has a primitive. This comparison lets ordinary
degree-one descent operate on the original Tate groups in every universe.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits groupCohomology ClassFieldTower.Cohomology

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- Vanishing of integral Tate degree one is the primitive criterion for
each original crossed homomorphism of the actual representation. -/
theorem tateOne_isZero_iff_hasH1Primitives (A : Rep.{v} ℤ G) :
    IsZero (tate A 1) ↔ HasH1Primitives A := by
  let M := (nativeFunctor G).obj A
  let e := tatePositiveIsoCohomology A 1
  constructor
  · intro h z hz
    have hs : Subsingleton (H1 M) := ModuleCat.subsingleton_of_isZero
      (M := cohomology A 1) (h.of_iso e.symm)
    let z' : cocycles₁ M := ⟨fun g => ULift.up (z g.down), (mem_cocycles₁_iff _).mpr (fun g₁ g₂ =>
      ULift.ext (hz g₁.down g₂.down))⟩
    obtain ⟨a, ha⟩ := (H1π_eq_zero_iff z').mp (@Subsingleton.elim _ hs _ _)
    exact ⟨a.down, fun g => congrArg (fun x : M => x.down) (congrFun ha (ULift.up g))⟩
  · intro h
    have hz (x : H1 M) : x = 0 := by
      refine H1_induction_on x (fun z => ?_)
      let z₀ : G → A := fun g => (z (ULift.up g)).down
      obtain ⟨a, ha⟩ := h z₀ (fun g₁ g₂ => congrArg (fun w : M => w.down)
        ((mem_cocycles₁_iff z).mp z.2 (ULift.up g₁) (ULift.up g₂)))
      apply (H1π_eq_zero_iff z).mpr
      refine ⟨ULift.up a, ?_⟩
      funext g
      apply ULift.down_injective
      exact ha g.down
    have : Subsingleton (cohomology A 1) := ⟨fun x y => (hz x).trans (hz y).symm⟩
    exact (ModuleCat.isZero_of_subsingleton (cohomology A 1)).of_iso e

/-- For a cyclic group, the original cyclic comparison identifies the
vanishing of Tate degrees one and minus one. -/
theorem tateOne_isZero_iff_negOne_of_cyclic (A : Rep.{v} ℤ G) [IsCyclic G] :
    IsZero (tate A 1) ↔ IsZero (tate A (-1)) := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  have hg' (x : G) : x ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top x
  let e := tatePositiveIsoCohomology A 1 ≪≫ IntegralGroupCohomology.integerScalars.mapIso
    (CyclicCohomology.finiteCyclicH1IsoTateHMinusOne ((nativeFunctor G).obj A)
      (ULift.up g) (ulift_generator g hg'))
  exact e.isZero_iff

/-- A finite group has zero degree-one Tate cohomology with the original
trivial integer coefficients. An integral cocycle vanishes on each element
because that element has finite order. -/
theorem tateTrivialInteger_one_isZero : IsZero (tate (integralTrivialInteger.{u, v} G) 1) := by
  apply (tateOne_isZero_iff_hasH1Primitives _).mpr
  intro z hz
  have h₀ : z 1 = 0 := by
    have h := hz 1 1
    rw [one_mul] at h
    change z 1 = z 1 + z 1 at h
    exact (add_left_cancel (show z 1 + 0 = z 1 + z 1 from (add_zero _).trans h)).symm
  have hp (g : G) (n : ℕ) : z (g ^ n) = n • z g := by
    induction n with
    | zero => simpa only [pow_zero, zero_nsmul] using h₀
    | succ n ih =>
      rw [pow_succ, hz]
      change z g + z (g ^ n) = (n + 1) • z g
      rw [ih, add_nsmul, one_nsmul, add_comm]
  refine ⟨0, fun g => ?_⟩
  have h := hp g (orderOf g)
  rw [pow_orderOf_eq_one, h₀] at h
  have hd := congrArg (fun a : ULift.{v} ℤ => a.down) h
  change (0 : ℤ) = orderOf g • (z g).down at hd
  rw [nsmul_eq_mul] at hd
  have hpos : (orderOf g : ℤ) ≠ 0 := by exact_mod_cast (orderOf_pos g).ne'
  apply ULift.down_injective
  change (0 : ℤ) - 0 = (z g).down
  rw [sub_self, (mul_eq_zero.mp hd.symm).resolve_left hpos]

variable (N : Subgroup G) [N.Normal] [Fintype N] [Fintype (G ⧸ N)]

/-- The ordinary degree-one primitive descent gives Tate degree-one vanishing. -/
theorem tateOne_isZero_of_normalSubgroup (A : Rep.{v} ℤ G)
    (hN : IsZero (tate (Rep.res N.subtype A) 1))
    (hQ : IsZero (tate (A.quotientToInvariants N) 1)) : IsZero (tate A 1) :=
  (tateOne_isZero_iff_hasH1Primitives A).mpr (hasH1Primitives_of_normalSubgroup A N
    ((tateOne_isZero_iff_hasH1Primitives _).mp hN) ((tateOne_isZero_iff_hasH1Primitives _).mp hQ))

omit [Fintype N] in
/-- Degree-one Tate vanishing passes to the quotient on the actual invariants. -/
theorem tateOne_quotient_isZero_of_isZero (A : Rep.{v} ℤ G) (h : IsZero (tate A 1)) :
    IsZero (tate (A.quotientToInvariants N) 1) :=
  (tateOne_isZero_iff_hasH1Primitives _).mpr
    (hasH1Primitives_quotient_of A N ((tateOne_isZero_iff_hasH1Primitives A).mp h))

end IntegralGroupCohomology.Universe
