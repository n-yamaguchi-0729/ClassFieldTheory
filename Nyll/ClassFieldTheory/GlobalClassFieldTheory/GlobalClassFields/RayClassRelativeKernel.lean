/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassModulusProjection
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus

/-!
# Kernels of modulus-change maps

For `m ≤ n`, the kernel of the existing projection `Cl_n → Cl_m` is the
image of the `m`-congruence ideles. The kernel of that map from `U_m` is
`U_n · (U_m ∩ principal)`. In particular the principal-unit correction is
retained; the relative congruence quotient alone need not be the ray kernel.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

variable (K : Type*) [Field K] [NumberField K]

/-- Modulus change preserves the representative in the idele class group. -/
@[simp]
theorem originalRayClassModulusProjection_mk
    {m n : RayClass.Modulus K} (hmn : m ≤ n) (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    originalRayClassModulusProjection K hmn
        (QuotientGroup.mk' n.congruenceSubgroup c) =
      QuotientGroup.mk' m.congruenceSubgroup c :=
  rfl

/-- The smaller-modulus congruence subgroup maps onto the projection kernel. -/
theorem originalRayClassModulusProjection_ker
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    (originalRayClassModulusProjection K hmn).ker =
      m.congruenceSubgroup.map (QuotientGroup.mk' n.congruenceSubgroup) := by
  ext q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective n.congruenceSubgroup q
  constructor
  · intro hc
    exact ⟨c, (QuotientGroup.eq_one_iff c).mp hc, rfl⟩
  · rintro ⟨d, hd, hdc⟩
    rw [← hdc]
    change QuotientGroup.mk' m.congruenceSubgroup d = 1
    exact (QuotientGroup.eq_one_iff d).mpr hd

/-- Insert an `m`-congruence idele into the ray class group for `n`. -/
noncomputable def rayCongruenceToRayClass
    (m n : RayClass.Modulus K) : m.ideleCongruenceSubgroup →* RayClass.RayClassGroup n :=
  (QuotientGroup.mk' n.congruenceSubgroup).comp
    ((IdeleGroup.toStandardClass K).comp
      m.ideleCongruenceSubgroup.subtype)

/-- Evaluation of the relative congruence map on an actual idele. -/
@[simp]
theorem rayCongruenceToRayClass_apply
    (m n : RayClass.Modulus K) (a : m.ideleCongruenceSubgroup) :
    rayCongruenceToRayClass K m n a =
      QuotientGroup.mk' n.congruenceSubgroup
        (IdeleGroup.toStandardClass K (a : IdeleGroup K)) :=
  rfl

/-- The image of `U_m` is the kernel of the existing modulus projection. -/
theorem rayCongruenceToRayClass_range
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    (rayCongruenceToRayClass K m n).range =
      (originalRayClassModulusProjection K hmn).ker := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    change QuotientGroup.mk' m.congruenceSubgroup
      (IdeleGroup.toStandardClass K (a : IdeleGroup K)) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨a, Subgroup.mem_sup_left a.property, rfl⟩
  · intro hq
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective n.congruenceSubgroup q
    have hc : c ∈ m.congruenceSubgroup := (QuotientGroup.eq_one_iff c).mp hq
    obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨u, hu, p, hp, rfl⟩ := Subgroup.mem_sup.mp ha
    refine ⟨⟨u, hu⟩, ?_⟩
    change QuotientGroup.mk' n.congruenceSubgroup
        (IdeleGroup.toStandardClass K u) =
      QuotientGroup.mk' n.congruenceSubgroup
        (IdeleGroup.toStandardClass K (u * p))
    rw [map_mul, (IdeleGroup.toStandardClass_eq_one_iff K p).mpr hp]
    exact congrArg (QuotientGroup.mk' n.congruenceSubgroup)
      (mul_one (IdeleGroup.toStandardClass K u)).symm

/-- The kernel inside `U_m` is `U_n` together with the principal ideles that
already lie in `U_m`. The principal correction cannot in general be omitted. -/
theorem rayCongruenceToRayClass_ker
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    (rayCongruenceToRayClass K m n).ker =
      n.ideleCongruenceSubgroup.comap m.ideleCongruenceSubgroup.subtype ⊔
        (IdeleGroup.principalSubgroup K).comap m.ideleCongruenceSubgroup.subtype := by
  ext a
  change rayCongruenceToRayClass K m n a = 1 ↔ _
  have heval : RayClass.rayClassGroupEquivIdeleQuotient n
      (rayCongruenceToRayClass K m n a) =
        QuotientGroup.mk' (n.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) (a : IdeleGroup K) :=
    RayClass.rayClassGroupEquivIdeleQuotient_mk_mk n a
  rw [← (RayClass.rayClassGroupEquivIdeleQuotient n).map_eq_one_iff,
    heval]
  refine (QuotientGroup.eq_one_iff
    (N := n.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K)
    (a : IdeleGroup K)).trans ?_
  constructor
  · rintro ha
    obtain ⟨u, hu, p, hp, hup⟩ := Subgroup.mem_sup.mp ha
    have hum : u ∈ m.ideleCongruenceSubgroup :=
      GlobalClassFieldTheory.GlobalClassFields.rayClassIdeleCongruenceSubgroup_antitone hmn hu
    have hpm : p ∈ m.ideleCongruenceSubgroup := by
      have hmem := m.ideleCongruenceSubgroup.mul_mem
        (m.ideleCongruenceSubgroup.inv_mem hum) a.property
      have heq : u⁻¹ * (a : IdeleGroup K) = p := by
        rw [← hup, inv_mul_cancel_left]
      rw [heq] at hmem
      exact hmem
    exact Subgroup.mem_sup.mpr
      ⟨⟨u, hum⟩, hu, ⟨p, hpm⟩, hp, Subtype.ext hup⟩
  · intro ha
    obtain ⟨u, hu, p, hp, hup⟩ := Subgroup.mem_sup.mp ha
    exact Subgroup.mem_sup.mpr
      ⟨u, hu, p, hp, congrArg (fun x : m.ideleCongruenceSubgroup => (x : IdeleGroup K)) hup⟩

/-- The relative ray kernel is the quotient by both deeper congruences and
principal ideles in `U_m`, using the standard first isomorphism theorem. -/
noncomputable def rayRelativeKernelEquiv
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    m.ideleCongruenceSubgroup ⧸
        (n.ideleCongruenceSubgroup.comap m.ideleCongruenceSubgroup.subtype ⊔
          (IdeleGroup.principalSubgroup K).comap m.ideleCongruenceSubgroup.subtype) ≃*
      (originalRayClassModulusProjection K hmn).ker :=
  (QuotientGroup.quotientMulEquivOfEq (rayCongruenceToRayClass_ker K hmn).symm).trans
    ((QuotientGroup.quotientKerEquivRange (rayCongruenceToRayClass K m n)).trans
      (MulEquiv.subgroupCongr (rayCongruenceToRayClass_range K hmn)))

end ClassFieldTheory
