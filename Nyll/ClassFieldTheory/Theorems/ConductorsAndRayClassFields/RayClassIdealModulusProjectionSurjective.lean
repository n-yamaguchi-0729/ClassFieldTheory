/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealModulusProjection
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealModulusProjectionPrime
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupHomExtFinitePrime
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

/-!
# Surjectivity of the ideal-theoretic modulus projection

The direct ideal-quotient projection agrees with the natural idelic quotient
projection because both preserve every prime class outside the larger modulus.
The latter projection is directly surjective since both ray class groups are
quotients of the same idèle class group.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

private local instance rayClassGroupCommGroup
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) : CommGroup (RayClassGroup m) :=
  { (inferInstance : Group (RayClassGroup m)) with mul_comm := mul_comm' }

private theorem rayClassGroup_hom_ext_of_prime
    (K : Type u) [Field K] [NumberField K]
    (n m : RayClassModulus K)
    (f g : RayClassGroup n →* RayClassGroup m)
    (hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ n.finitePart.support),
        f (rayClassOfFinitePrime n v hv) =
          g (rayClassOfFinitePrime n v hv)) :
    f = g :=
  rayClassGroup_hom_ext_finitePrime K n f g hprime

/-- Reducing a ray modulus gives a surjection of ideal-theoretic ray class
groups. -/
theorem rayClassIdealModulusProjection_surjective
    (K : Type u) [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    Function.Surjective (rayClassIdealModulusProjection K hmn) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let n' := GlobalClassFieldComparison.rayClassModulusToOriginal K n
  have hmn' : m' ≤ n' := hmn
  let : IsMulCommutative (IdeleClassGroup K) :=
    ⟨⟨fun a b => mul_comm a b⟩⟩
  let : (RayClass.Modulus.congruenceSubgroup m').Normal :=
    Subgroup.normal_of_isMulCommutative _
  let : (RayClass.Modulus.congruenceSubgroup n').Normal :=
    Subgroup.normal_of_isMulCommutative _
  let projection : RayClass.RayClassGroup n' →* RayClass.RayClassGroup m' :=
    QuotientGroup.map
      (RayClass.Modulus.congruenceSubgroup n')
      (RayClass.Modulus.congruenceSubgroup m')
      (MonoidHom.id (IdeleClassGroup K))
      (RayClass.Modulus.congruenceSubgroup_antitone hmn')
  have hprojection : Function.Surjective projection := by
    intro q
    obtain ⟨c, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (RayClass.Modulus.congruenceSubgroup m') q
    exact
      ⟨QuotientGroup.mk' (RayClass.Modulus.congruenceSubgroup n') c, rfl⟩
  let eM := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m
  let eN := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n
  let transported : RayClassGroup n →* RayClassGroup m :=
    eM.symm.toMonoidHom.comp (projection.comp eN.toMonoidHom)
  have htransported : Function.Surjective transported := by
    intro y
    obtain ⟨z, hz⟩ := eM.symm.surjective y
    obtain ⟨w, hw⟩ := hprojection z
    obtain ⟨x, hx⟩ := eN.surjective w
    refine ⟨x, ?_⟩
    change eM.symm (projection (eN x)) = y
    rw [hx, hw, hz]
  have hmap : rayClassIdealModulusProjection K hmn = transported := by
    apply rayClassGroup_hom_ext_of_prime K n m
    intro v hvn
    rw [rayClassIdealModulusProjection_prime K hmn v hvn]
    apply eM.injective
    change
      eM (rayClassOfFinitePrime m v _) =
        eM (eM.symm (projection (eN (rayClassOfFinitePrime n v hvn))))
    rw [eM.apply_symm_apply,
      GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K m v,
      GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K n v hvn]
    rfl
  rw [hmap]
  exact htransported

end ClassFieldTheory
