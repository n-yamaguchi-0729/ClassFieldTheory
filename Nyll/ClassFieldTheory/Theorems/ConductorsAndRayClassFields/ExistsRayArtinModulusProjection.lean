/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayArtinModulusProjection
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayArtin
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealModulusProjection
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

/-!
# Existence of a modulus-compatible ray class field embedding

Reducing the modulus yields an embedding of ray class field realizations
that intertwines their Artin maps.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u

namespace ClassFieldTheory

private theorem rayClassFieldRealization_norm_range
    {K : Type u} [Field K] [NumberField K]
    {m : RayClassModulus K} (R : RayClassFieldRealization K m) :
    (_root_.ideleClassNorm K R.extension).range =
      (GlobalClassFieldComparison.rayClassModulusToOriginal K m).congruenceSubgroup := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let e : RayClass.RayClassGroup m' ≃*
      (R.extension ≃ₐ[K] R.extension) :=
    (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm.trans
      R.artinEquiv
  apply (open _root_.GlobalClassFieldTheory.GlobalClassFields in
    rayModulus_normSubgroup_eq_of_arithmeticPrimeArtinEquiv m' e)
  intro v hv
  have hvm : v ∉ m.finitePart.support := hv
  calc
    e (QuotientGroup.mk' m'.congruenceSubgroup
        (IdeleGroup.toStandardClass K
          (IdeleGroup.finitePrimeIdele v))) =
        R.rayArtin (rayClassOfFinitePrime m v hvm) := by
      change R.artinEquiv
        ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
          (QuotientGroup.mk' m'.congruenceSubgroup
            (IdeleGroup.toStandardClass K
              (IdeleGroup.finitePrimeIdele v)))) = _
      rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K m v hvm]
      exact congrArg R.artinEquiv
        ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm_apply_apply _)
    _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := R.extension) v :=
      rayArtin_prime_eq_arithmeticPrimeArtin R v hvm

/-- A reduction of the modulus yields an embedding of any two ray-class-field
realizations, and this embedding intertwines their Artin maps. -/
theorem exists_rayArtin_modulusProjection
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n)
    (Rm : RayClassFieldRealization K m)
    (Rn : RayClassFieldRealization K n) :
    ∃ f : Rm.extension →ₐ[K] Rn.extension,
      ∀ (x : RayClassGroup n) (y : Rm.extension),
        Rn.rayArtin x (f y) =
          f (Rm.rayArtin (rayClassIdealModulusProjection K hmn x) y) := by
  have hnorm : (_root_.ideleClassNorm K Rn.extension).range ≤
      (_root_.ideleClassNorm K Rm.extension).range := by
    rw [rayClassFieldRealization_norm_range Rn,
      rayClassFieldRealization_norm_range Rm]
    exact RayClass.Modulus.congruenceSubgroup_antitone hmn
  obtain ⟨f⟩ :=
    GlobalClassFieldTheory.GlobalClassFields.finiteAbelianExtension_nonempty_algHom_of_normRange_le
      (K := K) Rm.extension Rn.extension hnorm
  exact ⟨f, rayArtin_modulusProjection hmn Rm Rn f⟩

end ClassFieldTheory
