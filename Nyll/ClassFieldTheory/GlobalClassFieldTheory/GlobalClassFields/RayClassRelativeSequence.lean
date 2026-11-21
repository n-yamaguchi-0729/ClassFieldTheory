/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassRelativeKernel

/-!
# The relative ray exact sequence

For `m ≤ n`, put `E_m = principal⁻¹(U_m)`. The maps in
`1 → E_m / E_n → U_m / U_n → Cl_n → Cl_m → 1`
are induced by the same principal and ray quotient maps. Their kernels and
images below retain the principal correction in the relative ray kernel.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

variable (K : Type*) [Field K] [NumberField K]

/-- Field units whose principal ideles satisfy the full modulus condition. -/
def rayPrincipalCongruenceUnits (m : RayClass.Modulus K) : Subgroup Kˣ :=
  m.ideleCongruenceSubgroup.comap (IdeleGroup.principalIdele K)

/-- The principal embedding restricted to the full congruence condition. -/
noncomputable def rayPrincipalCongruenceHom (m : RayClass.Modulus K) :
    rayPrincipalCongruenceUnits K m →* m.ideleCongruenceSubgroup where
  toFun x := ⟨IdeleGroup.principalIdele K x.1, x.2⟩
  map_one' := Subtype.ext (map_one (IdeleGroup.principalIdele K))
  map_mul' x y := Subtype.ext (map_mul (IdeleGroup.principalIdele K) x.1 y.1)

/-- Principal congruences map to the relative idele congruence quotient. -/
noncomputable def principalToRelativeRayCongruence (m n : RayClass.Modulus K) :
    rayPrincipalCongruenceUnits K m →*
      m.ideleCongruenceSubgroup ⧸ n.ideleCongruenceSubgroup.subgroupOf
        m.ideleCongruenceSubgroup :=
  (QuotientGroup.mk' (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup)).comp
    (rayPrincipalCongruenceHom K m)

/-- The left-hand kernel is exactly the deeper principal congruence subgroup. -/
theorem principalToRelativeRayCongruence_ker (m n : RayClass.Modulus K) :
    (principalToRelativeRayCongruence K m n).ker =
      (rayPrincipalCongruenceUnits K n).subgroupOf (rayPrincipalCongruenceUnits K m) := by
  ext x
  exact QuotientGroup.eq_one_iff (rayPrincipalCongruenceHom K m x)

/-- The first nontrivial map of the relative ray exact sequence. -/
noncomputable def principalRelativeRayCongruenceMap (m n : RayClass.Modulus K) :
    rayPrincipalCongruenceUnits K m ⧸
        (rayPrincipalCongruenceUnits K n).subgroupOf (rayPrincipalCongruenceUnits K m) →*
      m.ideleCongruenceSubgroup ⧸ n.ideleCongruenceSubgroup.subgroupOf
        m.ideleCongruenceSubgroup :=
  QuotientGroup.lift
    ((rayPrincipalCongruenceUnits K n).subgroupOf (rayPrincipalCongruenceUnits K m))
    (principalToRelativeRayCongruence K m n) (by
      rw [principalToRelativeRayCongruence_ker])

/-- The first map sends the class of a principal congruence to its principal
idele class in the relative congruence quotient. -/
@[simp]
theorem principalRelativeRayCongruenceMap_mk
    (m n : RayClass.Modulus K) (x : rayPrincipalCongruenceUnits K m) :
    principalRelativeRayCongruenceMap K m n
        (QuotientGroup.mk'
          ((rayPrincipalCongruenceUnits K n).subgroupOf (rayPrincipalCongruenceUnits K m)) x) =
      principalToRelativeRayCongruence K m n x :=
  rfl

/-- The relative principal congruence quotient embeds into the relative idele
congruence quotient. -/
theorem principalRelativeRayCongruenceMap_injective (m n : RayClass.Modulus K) :
    Function.Injective (principalRelativeRayCongruenceMap K m n) := by
  apply (MonoidHom.ker_eq_bot_iff (f := principalRelativeRayCongruenceMap K m n)).mp
  apply le_antisymm
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      ((rayPrincipalCongruenceUnits K n).subgroupOf (rayPrincipalCongruenceUnits K m)) q
    change QuotientGroup.mk'
      ((rayPrincipalCongruenceUnits K n).subgroupOf (rayPrincipalCongruenceUnits K m)) x = 1
    apply (QuotientGroup.eq_one_iff x).mpr
    rw [← principalToRelativeRayCongruence_ker K m n]
    exact hq
  · exact bot_le

/-- Quotienting the source of the principal map does not change its image. -/
theorem principalRelativeRayCongruenceMap_range (m n : RayClass.Modulus K) :
    (principalRelativeRayCongruenceMap K m n).range =
      (principalToRelativeRayCongruence K m n).range := by
  ext q
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      ((rayPrincipalCongruenceUnits K n).subgroupOf (rayPrincipalCongruenceUnits K m)) x
    exact ⟨a, hx⟩
  · rintro ⟨a, rfl⟩
    exact ⟨QuotientGroup.mk'
      ((rayPrincipalCongruenceUnits K n).subgroupOf (rayPrincipalCongruenceUnits K m)) a, rfl⟩

/-- The relative idele congruence quotient maps to the larger-modulus ray group. -/
noncomputable def relativeRayCongruenceMap
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    m.ideleCongruenceSubgroup ⧸ n.ideleCongruenceSubgroup.subgroupOf
        m.ideleCongruenceSubgroup →* RayClass.RayClassGroup n :=
  QuotientGroup.lift
    (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup)
    (rayCongruenceToRayClass K m n) (by
      rw [rayCongruenceToRayClass_ker K hmn]
      exact le_sup_left)

/-- The middle map sends a relative congruence class to the same ray class. -/
@[simp]
theorem relativeRayCongruenceMap_mk
    {m n : RayClass.Modulus K} (hmn : m ≤ n) (a : m.ideleCongruenceSubgroup) :
    relativeRayCongruenceMap K hmn
        (QuotientGroup.mk'
          (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup) a) =
      rayCongruenceToRayClass K m n a :=
  rfl

/-- Exactness at the relative congruence quotient: its ray-trivial classes are
precisely the principal congruence classes from `E_m / E_n`. -/
theorem principalRelativeRayCongruenceMap_range_eq_ker
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    (principalRelativeRayCongruenceMap K m n).range =
      (relativeRayCongruenceMap K hmn).ker := by
  rw [principalRelativeRayCongruenceMap_range]
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change QuotientGroup.mk' n.congruenceSubgroup
      (IdeleGroup.toStandardClass K (IdeleGroup.principalIdele K x.1)) = 1
    rw [IdeleGroup.toStandardClass_principalIdele, map_one]
  · intro hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup) q
    have ha : a ∈ (rayCongruenceToRayClass K m n).ker := hq
    rw [rayCongruenceToRayClass_ker K hmn] at ha
    obtain ⟨u, hu, p, hp, hup⟩ := Subgroup.mem_sup.mp ha
    obtain ⟨x, hx⟩ := hp
    have hxmem : x ∈ rayPrincipalCongruenceUnits K m := by
      change IdeleGroup.principalIdele K x ∈ m.ideleCongruenceSubgroup
      rw [hx]
      exact p.property
    refine ⟨⟨x, hxmem⟩, ?_⟩
    have hprincipal : rayPrincipalCongruenceHom K m ⟨x, hxmem⟩ = p := Subtype.ext hx
    change QuotientGroup.mk'
        (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup)
        (rayPrincipalCongruenceHom K m ⟨x, hxmem⟩) =
      QuotientGroup.mk'
        (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup) a
    let mk := QuotientGroup.mk'
      (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup)
    have hu1 : mk u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    calc
      _ = mk p := congrArg mk hprincipal
      _ = mk (1 * p) := congrArg mk (one_mul p).symm
      _ = mk 1 * mk p := map_mul mk 1 p
      _ = 1 * mk p := congrArg (fun q => q * mk p) (map_one mk)
      _ = mk u * mk p := congrArg (fun q => q * mk p) hu1.symm
      _ = mk (u * p) := (map_mul mk u p).symm
      _ = mk a := congrArg mk hup

/-- Exactness at the larger ray group uses the existing modulus projection. -/
theorem relativeRayCongruenceMap_range_eq_ker
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    (relativeRayCongruenceMap K hmn).range =
      (originalRayClassModulusProjection K hmn).ker := by
  rw [← rayCongruenceToRayClass_range K hmn]
  ext q
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup) x
    exact ⟨a, hx⟩
  · rintro ⟨a, rfl⟩
    exact ⟨QuotientGroup.mk'
      (n.ideleCongruenceSubgroup.subgroupOf m.ideleCongruenceSubgroup) a, rfl⟩

end ClassFieldTheory
