/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.H2FiniteIndexTrace
public import Nyll.GaloisCohomology.Topology.ContinuousSubgroupPrimitiveExtension
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousRepresentationUniverseLift

/-!
# Finite-index detection of actual continuous degree-two cohomology

A subgroup primitive is extended by the actual continuous coset retraction
and the prism correction. The existing algebraic coefficient trace then
averages this continuous primitive, so the subgroup index kills the class.
-/

@[expose] public section

noncomputable section
open CategoryTheory ContRepresentation TopRep
open ReidemeisterSchreier.Profinite

namespace ContinuousCohomology

universe r u v

variable {R : Type r} [CommRing R] [TopologicalSpace R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable (X : TopRep.{u} R G) (H : OpenSubgroup G)

omit [CompactSpace G] in
private theorem restricted_degreeTwo_value
    (z : cocycles X 2) (a b c : ↥(H : Subgroup G)) :
    (((homogeneousCochains (TopRep.res H.toSubgroup.subtype X)).iCycles 2).hom
        (cocyclesMap (⟨H.toSubgroup.subtype, continuous_subtype_val⟩ :
          ↥(H : Subgroup G) →ₜ* G) (𝟙 _) 2 z)).1 a b c =
      (((homogeneousCochains X).iCycles 2).hom z).1 a b c := by
  let ι : ↥(H : Subgroup G) →ₜ* G :=
    ⟨H.toSubgroup.subtype, continuous_subtype_val⟩
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap ι (𝟙 _)) 2) z
  exact congrArg
    (fun t : (homogeneousCochains (TopRep.res H.toSubgroup.subtype X)).X 2 =>
      t.1 a b c) h

/-- If degree-two continuous cohomology vanishes on an open subgroup,
its index kills ambient classes for arbitrary continuous coefficients. -/
theorem index_nsmul_H2_eq_zero_of_open_restriction
    (hH : ∀ w : continuousCohomology 2 (TopRep.res H.toSubgroup.subtype X), w = 0)
    (v : continuousCohomology 2 X) : H.toSubgroup.index • v = 0 := by
  have : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let Y := TopRep.res H.toSubgroup.subtype X
  let ι : ↥(H : Subgroup G) →ₜ* G :=
    ⟨H.toSubgroup.subtype, continuous_subtype_val⟩
  let C := homogeneousCochains X
  let D := homogeneousCochains Y
  obtain ⟨z, rfl⟩ := π_surjective X 2 v
  let z₀ : C.X 2 := (C.iCycles 2).hom z
  let zH := cocyclesMap ι (𝟙 Y) 2 z
  obtain ⟨b, hb⟩ := exists_boundary_of_π_eq_zero Y 1 zH (hH _)
  let b₀ : C(↥(H : Subgroup G), C(↥(H : Subgroup G), X)) := b.1
  have hb₀ (a b' c : ↥(H : Subgroup G)) :
      b₀ b' c - b₀ a c + b₀ a b' = z₀.1 a b' c := by
    have he := congrArg (fun t : D.X 2 => t.1 a b' c) hb
    have hd := homogeneousCochains.d_apply Y 1 b
    have hd' := congrArg (fun t => t a b' c) hd
    rw [hd'] at he
    change b₀ b' c - (b₀ a c - b₀ a b') =
      ((D.iCycles 2).hom zH).1 a b' c at he
    calc
      _ = b₀ b' c - (b₀ a c - b₀ a b') := by abel
      _ = ((D.iCycles 2).hom zH).1 a b' c := he
      _ = z₀.1 a b' c := restricted_degreeTwo_value X H z a b' c
  have hbEq (h a c : ↥(H : Subgroup G)) :
      X.ρ (h : G) (b₀ a c) = b₀ (h * a) (h * c) := by
    have ht := congrArg (fun t => t (h * a) (h * c)) (b.2 h)
    change X.ρ (h : G) (b₀ (h⁻¹ * (h * a)) (h⁻¹ * (h * c))) =
      b₀ (h * a) (h * c) at ht
    simpa only [inv_mul_cancel_left] using ht
  let q := openSubgroupPrimitiveExtension H z₀.1 b₀
  let A := Rep.of (resolutionX X 2).ρ.toRepresentation
  let B := Rep.of (resolutionX X 3).ρ.toRepresentation
  let d : A ⟶ B := Rep.ofHom (TopRep.d X 2).hom.toIntertwiningMap
  have hq (h : ↥(H : Subgroup G)) : A.ρ (h : G) q = q := by
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro c
    change X.ρ (h : G) (q ((h : G)⁻¹ * a) ((h : G)⁻¹ * c)) = q a c
    have ht := openSubgroupPrimitiveExtension_equivariant X.ρ H z₀.1
      (fun h a b c => degreeTwo_equivariant X z (h : G) a b c)
      b₀ hbEq h ((h : G)⁻¹ * a) ((h : G)⁻¹ * c)
    simpa only [mul_inv_cancel_left] using ht
  have hdq : d.hom q = z₀.1 := by
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b'
    apply ContinuousMap.ext
    intro c
    change q b' c - (q a c - q a b') = z₀.1 a b' c
    calc
      _ = q b' c - q a c + q a b' := by abel
      _ = z₀.1 a b' c := openSubgroupPrimitiveExtension_boundary H z₀.1
        (degreeTwo_cocycle_equation X z) b₀ hb₀ a b' c
  obtain ⟨w, hw, hdw⟩ :=
    ClassFieldTower.Cohomology.exists_invariant_index_preimage
      (H := H.toSubgroup) A d q hq (by
        intro g
        rw [hdq]
        exact z₀.2 g)
  let t : C.X 1 := ⟨w, hw⟩
  have ht : (C.d 1 2).hom t = H.toSubgroup.index • z₀ := by
    apply Subtype.ext
    change d.hom w = H.toSubgroup.index • z₀.1
    exact hdw.trans (congrArg (fun a => H.toSubgroup.index • a) hdq)
  have hi : Function.Injective (C.iCycles 2) :=
    (ModuleCat.mono_iff_injective
      ((forget₂ (TopModuleCat R) (ModuleCat R)).map (C.iCycles 2))).mp inferInstance
  have ht' : (C.toCycles 1 2).hom t = H.toSubgroup.index • z := by
    apply hi
    calc
      _ = (C.d 1 2).hom t := ConcreteCategory.congr_hom (C.toCycles_i 1 2) t
      _ = H.toSubgroup.index • z₀ := ht
      _ = (C.iCycles 2).hom (H.toSubgroup.index • z) := by rw [map_nsmul]
  calc
    H.toSubgroup.index • π X 2 z = π X 2 (H.toSubgroup.index • z) := by
      rw [map_nsmul]
    _ = π X 2 ((C.toCycles 1 2).hom t) := congrArg (π X 2) ht'.symm
    _ = 0 := ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) t

omit [CompactSpace G] in
/-- An integer annihilating the coefficients annihilates actual continuous H². -/
theorem nsmul_H2_eq_zero_of_coefficients (m : ℕ)
    (hm : ∀ x : X, m • x = 0) (v : continuousCohomology 2 X) :
    m • v = 0 := by
  let C := homogeneousCochains X
  obtain ⟨z, rfl⟩ := π_surjective X 2 v
  have hi : Function.Injective (C.iCycles 2) :=
    (ModuleCat.mono_iff_injective
      ((forget₂ (TopModuleCat R) (ModuleCat R)).map (C.iCycles 2))).mp inferInstance
  have hz : m • z = 0 := by
    apply hi
    rw [map_nsmul, map_zero]
    apply Subtype.ext
    ext a b c
    exact hm _
  calc
    m • π X 2 z = π X 2 (m • z) := by rw [map_nsmul]
    _ = 0 := by rw [hz]; exact map_zero (π X 2).hom

/-- For coefficients killed by p, vanishing on an open subgroup of
index prime to p implies ambient continuous H² vanishing. -/
theorem H2_eq_zero_of_primeToIndex_open_restriction
    (p : ℕ) [Fact p.Prime] (hpX : ∀ x : X, p • x = 0)
    (hindex : ¬ p ∣ H.toSubgroup.index)
    (hH : ∀ w : continuousCohomology 2 (TopRep.res H.toSubgroup.subtype X), w = 0)
    (v : continuousCohomology 2 X) : v = 0 := by
  by_contra hv
  have hpv := nsmul_H2_eq_zero_of_coefficients X p hpX v
  have ho : addOrderOf v = p := addOrderOf_eq_prime hpv hv
  have hi := index_nsmul_H2_eq_zero_of_open_restriction X H hH v
  exact hindex (ho ▸ addOrderOf_dvd_of_nsmul_eq_zero hi)

/-- The same actual continuous trace applies to independently sized input
coefficients, using their lifted homogeneous cochains and original subgroup index. -/
theorem index_nsmul_universeLiftH2_eq_zero_of_open_restriction
    (X : TopRep.{v} R G)
    (hH : ∀ w : continuousCohomology 2
      (TopRep.res (TopRep.universeLiftOpenSubgroup.{u, v} H).toSubgroup.subtype
        (TopRep.universeLift X)), w = 0)
    (a : TopRep.universeLiftCohomology X 2) : H.toSubgroup.index • a = 0 := by
  have h := index_nsmul_H2_eq_zero_of_open_restriction
    (TopRep.universeLift X) (TopRep.universeLiftOpenSubgroup H) hH a
  rw [TopRep.universeLiftOpenSubgroup_index] at h
  exact h

end ContinuousCohomology
