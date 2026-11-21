/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants
public import Nyll.GaloisCohomology.Topology.ContinuousH1CoprimeNormalImage
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicRamificationProP
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianNormality

/-! # The wild-invariants-zero case of first cohomology -/

@[expose] public section

noncomputable section

open ContinuousCohomology ProCGroups.ProC
open RamificationTheory.HilbertRamification.ValuationSubring

namespace Representation

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]

/-- The invariant vectors of a normal subgroup form a subrepresentation. In
a simple module they are zero or the entire module. -/
theorem noInvariants_or_trivial_of_normal_isIrreducible
    (ρ : Representation k G V) [IsIrreducible ρ] (N : Subgroup G) [N.Normal] :
    (∀ a : V, (∀ h : N, ρ h.val a = a) → a = 0) ∨ (∀ (h : N) (a : V), ρ h.val a = a) := by
  let W : Subrepresentation ρ :=
    ⟨Representation.invariants (ρ.comp N.subtype),
      by
        intro g a ha
        exact Representation.le_comap_invariants ρ N g ha⟩
  rcases eq_bot_or_eq_top W with hbot | htop
  · left
    intro a ha
    have hw : a ∈ W := ha
    rw [hbot] at hw
    exact (Submodule.mem_bot (R := k)).mp hw
  · right
    intro h a
    have hw : a ∈ W := by
      rw [htop]
      exact Submodule.mem_top
    have ha : ∀ g : N, ρ g.val a = a := hw
    exact ha h

end Representation

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)

/-- Every finite locally constant image of the literal absolute ramification
subgroup is primary at the residue characteristic. -/
theorem localWild_locallyConstant_range_isPGroup (W : ValuationSubring Ω)
    (q : ℕ) [Fact q.Prime] [CharP (IsLocalRing.ResidueField W) q]
    {D : Type u} [Group D] [Finite D] (f : ramificationGroupInAut K W →* D)
    (hf : IsLocallyConstant f) : IsPGroup q f.range := by
  let N := ramificationGroupInAut K W
  have hbasis := ramificationGroupInAut_hasOpenNormalBasisInClass_of_isGalois_residueChar K W q
  obtain ⟨U, hU, hq⟩ := hbasis {σ : N | f σ = 1} (hf.isOpen_fiber 1) (map_one f)
  let φ := f.rangeRestrict
  have hker : (U : Subgroup N) ≤ φ.ker := fun _ hg => Subtype.ext (hU hg)
  let fbar : N ⧸ (U : Subgroup N) →* f.range := QuotientGroup.lift _ φ hker
  have hs : Function.Surjective fbar := by
    intro y
    obtain ⟨σ, hσ⟩ := MonoidHom.rangeRestrict_surjective f y
    refine ⟨QuotientGroup.mk' (U : Subgroup N) σ, ?_⟩
    exact (QuotientGroup.lift_mk' (U : Subgroup N) hker σ).trans hσ
  exact hq.2.of_surjective fbar hs

/-- For finite discrete prime coefficients away from the residue
characteristic, zero invariants under actual wild inertia force continuous
first cohomology to vanish. -/
theorem localH1_eq_zero_of_wild_noInvariants (V : ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)] (W : ValuationSubring Ω)
    [V.valuation.HasExtension W.valuation]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [CharP (IsLocalRing.ResidueField W) q] (hpq : p ≠ q)
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A] (hpA : ∀ a : A, p • a = 0)
    (hcont : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (hfix : ∀ a : A, (∀ g : ramificationGroupInAut K W, A.ρ g.val a = a) → a = 0)
    (x : continuousCohomology 1 A) : x = 0 := by
  let N := ramificationGroupInAut K W
  let : N.Normal := ramificationGroupInAut_normal_of_henselianRing K V W
  apply continuousH1_eq_zero_of_normal_primaryImages A N p q hpq hpA hcont hfix _ x
  intro D _ _ f hf
  exact localWild_locallyConstant_range_isPGroup K W q f hf

end ClassFieldTheory.Brauer
