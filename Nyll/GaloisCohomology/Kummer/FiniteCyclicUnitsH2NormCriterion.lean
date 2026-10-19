/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormClass

/-!
# The actual norm criterion for a cyclic unit H² class

The class of a base-field unit is zero exactly when the unit is an actual
field norm. The periodic resolution is compared with the carry representative
and with the product of Galois conjugates defining the field norm.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

/-- A base-unit cyclic H² class vanishes exactly for actual field norms. -/
theorem finiteCyclicBaseUnitH2Class_eq_zero_iff_norm
    (K M : Type) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)]
    (g : Gal(M/K)) (hg : ∀ σ : Gal(M/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    finiteCyclicBaseUnitH2Class K M g hg a = 0 ↔
      ∃ x : M, Algebra.norm K x = (a : K) := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let T := Rep.trivial ℤ Gal(M/K) (Additive Kˣ)
  let A := Rep.ofAlgebraAutOnUnits K M
  let φ : T ⟶ A := finiteGaloisBaseUnitsRepHom K M
  let a₀ : LinearMap.ker (Rep.applyAsHom T g - 𝟙 _).hom.toLinearMap :=
    ⟨Additive.ofMul a, by
      change Additive.ofMul a - Additive.ofMul a = 0
      exact sub_self _⟩
  let a₁ : LinearMap.ker (Rep.applyAsHom A g - 𝟙 _).hom.toLinearMap :=
    ⟨φ.hom a₀.1, by
      change A.ρ g (φ.hom a₀.1) - φ.hom a₀.1 = 0
      rw [← Rep.hom_comm_apply φ g a₀.1]
      exact sub_self _⟩
  have hcarry : groupCohomology.mapCocycles₂ (MonoidHom.id Gal(M/K)) φ
      (finiteCyclicCarryTwoCocycle T g hg a₀) = finiteCyclicCarryTwoCocycle A g hg a₁ := by
    apply Subtype.ext
    funext st
    change φ.hom (finiteCyclicCarry g hg st.1 st.2 • a₀.1) =
      finiteCyclicCarry g hg st.1 st.2 • φ.hom a₀.1
    exact map_nsmul φ.hom _ _
  have hclass : finiteCyclicBaseUnitH2Class K M g hg a =
      Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide) a₁ := by
    have h := groupCohomology.H2π_comp_map_apply (MonoidHom.id Gal(M/K)) φ
      (finiteCyclicCarryTwoCocycle T g hg a₀)
    rw [hcarry] at h
    exact h.trans (H2π_finiteCyclicCarryTwoCocycle A g hg a₁)
  rw [hclass, Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    let u : Mˣ := (show Additive Mˣ from b).toMul
    refine ⟨(u : M), (algebraMap K M).injective ?_⟩
    have h := congrArg (fun z : A => ((show Additive Mˣ from z).toMul : M)) hb
    exact (groupCohomology.norm_ofAlgebraAutOnUnits_eq (K := K) (L := M) u).symm.trans h
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro hz
      apply a.ne_zero
      rw [← hx, hz, Algebra.norm_zero]
    refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
    apply Units.ext
    exact (groupCohomology.norm_ofAlgebraAutOnUnits_eq
      (K := K) (L := M) (Units.mk0 x hx0)).trans (congrArg (algebraMap K M) hx)

end
end ClassFieldTower.Cohomology
