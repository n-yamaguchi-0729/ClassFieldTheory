/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteCyclicH2CoefficientNorm

/-!
# Norms kill cyclic H² after a group pullback

A norm preimage of the image of the unit coefficient kills every class with
trivial rank-one coefficients after pullback to a finite cyclic group.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

/-- The image of the unit coefficient suffices to kill a pulled-back rank-one H² map. -/
theorem finiteCyclicH2_rankOneMap_eq_zero_of_norm
    {R G H : Type u} [CommRing R] [Group G] [CommGroup H] [Fintype H]
    (B : Rep R H) (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (f : H →* G) (φ : Rep.res f (Rep.trivial R G R) ⟶ B)
    (b : B) (hb : B.norm.hom b = φ.hom 1) :
    groupCohomology.map f φ 2 = 0 := by
  let ψ : Rep.trivial R H R ⟶ B := φ
  have hnorm : ∀ a : LinearMap.ker
      (Rep.applyAsHom (Rep.trivial R H R) h - 𝟙 _).hom.toLinearMap,
      ∃ y : B, B.norm.hom y = ψ.hom a.1 := by
    intro a
    refine ⟨a.1 • b, ?_⟩
    rw [map_smul, hb]
    exact (map_smul ψ.hom (a.1 : R) (1 : R)).symm.trans
      (congrArg ψ.hom (mul_one (a.1 : R)))
  have hz := finiteCyclicH2_coefficientMap_eq_zero_of_norm
    (Rep.trivial R H R) B h hh ψ hnorm
  have hcomp := groupCohomology.map_comp
    (A := Rep.trivial R G R) (B := Rep.trivial R H R) (C := B)
    f (MonoidHom.id H) (𝟙 (Rep.trivial R H R)) ψ 2
  rw [hz, Limits.comp_zero] at hcomp
  refine (groupCohomology.map_congr (by ext x; rfl) ?_ 2).trans hcomp
  apply LinearMap.ext
  intro r
  rfl

/-- A norm preimage kills a specified cyclic carry class after an arbitrary
group homomorphism and an equivariant change of coefficients. -/
theorem finiteCyclicCarry_pullbackMap_eq_zero_of_norm
    {R G H : Type u} [CommRing R] [CommGroup G] [Fintype G]
    [CommGroup H] [Fintype H]
    (A : Rep R G) (B : Rep R H)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (f : H →* G) (φ : Rep.res f A ⟶ B)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (b : B) (hb : B.norm.hom b = φ.hom a.1) :
    groupCohomology.map f φ 2
      (groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a)) = 0 := by
  have hag : A.ρ g a.1 = a.1 := by
    have hz := a.2
    change A.ρ g a.1 - a.1 = 0 at hz
    exact sub_eq_zero.mp hz
  have ha : ∀ σ : G, A.ρ σ a.1 = a.1 :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg a.1).mpr hag
  let ι : Rep.trivial R G R ⟶ A := Rep.ofHom
    ⟨LinearMap.toSpanSingleton R A a.1, by
      intro σ
      apply LinearMap.ext
      intro r
      change r • a.1 = A.ρ σ (r • a.1)
      rw [map_smul, ha]⟩
  let ψ : Rep.res f (Rep.trivial R G R) ⟶ B := (Rep.resFunctor f).map ι ≫ φ
  have hb' : B.norm.hom b = ψ.hom 1 := by
    change B.norm.hom b = φ.hom ((1 : R) • a.1)
    rw [one_smul]
    exact hb
  have hzero := finiteCyclicH2_rankOneMap_eq_zero_of_norm B h hh f ψ b hb'
  let oneCycle : LinearMap.ker
      (Rep.applyAsHom (Rep.trivial R G R) g - 𝟙 _).hom.toLinearMap :=
    ⟨1, by
      change (1 : R) - 1 = 0
      exact sub_self 1⟩
  have hcarry : groupCohomology.mapCocycles₂ (MonoidHom.id G) ι
      (finiteCyclicCarryTwoCocycle (Rep.trivial R G R) g hg oneCycle) =
        finiteCyclicCarryTwoCocycle A g hg a := by
    apply Subtype.ext
    funext st
    change ι.hom (finiteCyclicCarry g hg st.1 st.2 • (1 : R)) =
      finiteCyclicCarry g hg st.1 st.2 • a.1
    rw [map_nsmul]
    change finiteCyclicCarry g hg st.1 st.2 • ((1 : R) • a.1) = _
    rw [one_smul]
  have hcomp := groupCohomology.map_comp
    (A := Rep.trivial R G R) (B := A) (C := B) (MonoidHom.id G) f ι φ 2
  have hclass := groupCohomology.H2π_comp_map_apply (MonoidHom.id G) ι
    (finiteCyclicCarryTwoCocycle (Rep.trivial R G R) g hg oneCycle)
  rw [hcarry] at hclass
  let c := groupCohomology.H2π (Rep.trivial R G R)
    (finiteCyclicCarryTwoCocycle (Rep.trivial R G R) g hg oneCycle)
  have heval : groupCohomology.map f ψ 2 c =
      groupCohomology.map f φ 2 (groupCohomology.map (MonoidHom.id G) ι 2 c) :=
    congrArg (fun (m : groupCohomology (Rep.trivial R G R) 2 ⟶ groupCohomology B 2) => m c) hcomp
  have hz : groupCohomology.map f ψ 2 c = 0 :=
    congrArg (fun (m : groupCohomology (Rep.trivial R G R) 2 ⟶ groupCohomology B 2) => m c) hzero
  exact (congrArg (fun z => groupCohomology.map f φ 2 z) hclass).symm.trans
    (heval.symm.trans hz)

end
end ClassFieldTower.Cohomology
