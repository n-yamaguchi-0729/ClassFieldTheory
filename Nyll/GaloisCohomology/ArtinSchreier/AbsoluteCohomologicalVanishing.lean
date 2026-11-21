/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ArtinSchreier.OpenCohomologyVanishing
public import Nyll.GaloisCohomology.Topology.ContinuousCoinducedDimensionShift
public import Nyll.GaloisCohomology.Topology.ContinuousH2FiniteIndexTrace
public import Nyll.GaloisCohomology.Topology.FiniteCoefficientCochains
public import Nyll.GaloisCohomology.Topology.FinitePGroupCoefficientVanishing

/-! # Artin–Schreier vanishing on the actual continuous complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousCohomology TopRep ClassFieldTower.Cohomology

noncomputable section

namespace ArtinSchreierTheory

universe u

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p]

local notation "G" => Gal(Ω/K)

private theorem openTrivialIntegralH2_isZero (H : OpenSubgroup G) :
    IsZero (((continuousModuleComplexFunctor ↥(H : Subgroup G)).obj
      (trivialIntegralZModPLifted p ↥(H : Subgroup G))).homology 2) := by
  let F := ↥(H : Subgroup G)
  let T := trivialIntegralZModPLifted p F
  let : DiscreteTopology T := inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))
  apply continuousModuleComplex_isZero_of_cohomology_eq_zero F T 2
  apply TrivialDegreeTwoCocycles.continuousH2_eq_zero_of_primitive T (fun _ _ => rfl)
  intro c hc
  let z (a b : F) := (show ULift.{u} (ZMod p) from c (a, b)).down
  have hz (a b d : F) : z a (b * d) + z b d = z (a * b) d + z a b := by
    have h := congrArg (ULift.down : ULift.{u} (ZMod p) → ZMod p) (hc a b d).symm
    change z b d + z a (b * d) = z (a * b) d + z a b at h
    exact (add_comm _ _).trans h
  have hloc : IsLocallyConstant (fun t : F × F => z t.1 t.2) :=
    ((IsLocallyConstant.iff_continuous c).mpr c.continuous).comp ULift.down
  obtain ⟨d, hdloc, hd⟩ := exists_zmod_primitive_of_two_cocycle_open p H z hz hloc
  refine ⟨⟨fun a => ULift.up (d a), (hdloc.comp ULift.up).continuous⟩, fun a b => ?_⟩
  apply ULift.ext
  change d b + d a - d (a * b) = z a b
  calc
    _ = d b - d (a * b) + d a := by abel
    _ = _ := hd a b

/-- A finite module annihilated by the characteristic has trivial continuous H². -/
theorem finiteIntegralH2_isZero_of_charP (X : TopRep.{u} ℤ G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) (hpX : ∀ x : X, p • x = 0) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology 2) := by
  let : Module ℤ X := X.hV2
  obtain ⟨H, hindex, hρ⟩ := exists_openSubgroup_primeToIndex_pGroup_image ℤ G X hX p
  let F := ↥(H : Subgroup G)
  let Y := TopRep.res H.toSubgroup.subtype X
  have hY : Continuous (fun fy : F × Y => Y.ρ fy.1 fy.2) :=
    hX.comp (continuous_subtype_val.prodMap continuous_id)
  have h := continuousModuleH2_isZero_of_pGroup_image F p
    (openTrivialIntegralH2_isZero p H) Y hY hpX hρ
  apply continuousModuleComplex_isZero_of_cohomology_eq_zero G X 2
  exact H2_eq_zero_of_primeToIndex_open_restriction X H p hpX hindex
    (cohomology_eq_zero_of_continuousModuleComplex_isZero F Y 2 h)

/-- All degrees at least two vanish for actual discrete coefficients
annihilated by the characteristic. -/
theorem integralCohomology_isZero_of_charP (X : TopRep.{u} ℤ G) [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) (hpX : ∀ x : X, p • x = 0)
    (n : ℕ) : IsZero (((continuousModuleComplexFunctor G).obj X).homology (n + 2)) := by
  have h := (Fact.out : p.Prime).ne_zero
  have hpX' (x : X) : (p : ℤ) • x = 0 := by
    rw [natCast_zsmul]
    exact hpX x
  apply continuousModule_isZero_of_degreeTwo G X (p : ℤ) ?_ hX hpX' n
  intro Y hdisc hY hpY
  apply continuousModule_isZero_of_finite_coefficients G Y hY (p : ℤ)
    (Int.natCast_ne_zero.mpr h) hpY 1
  intro V hfin hdisc hV hpV
  apply finiteIntegralH2_isZero_of_charP p V hV
  intro x
  have hx := hpV x
  rwa [natCast_zsmul] at hx

end ArtinSchreierTheory
