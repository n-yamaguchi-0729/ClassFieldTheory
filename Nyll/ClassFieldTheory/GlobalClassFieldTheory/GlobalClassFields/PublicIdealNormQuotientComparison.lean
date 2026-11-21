/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNormCore
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal

/-!
# Comparing source and public ideal-norm subgroups

The source ideal norm is defined before quotienting by principal ray ideals.
The public ideal-norm image is its image in the ideal ray class group.  This
file records the exact comparison, including the principal-ray kernel.
-/

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

universe u v

namespace ClassFieldTheory.GlobalClassFieldComparison

/-- The preimage of the public ideal-norm image under the ray quotient is
exactly the original norm subgroup, including principal ray ideals. -/
theorem publicIdealNormImage_comap_rayQuotient
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (m : RayClassModulus K) :
    (rayClassIdealNormImage K L m).comap
        (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)) =
      RayClass.idealNormSubgroup (K := K) (L := L)
        (rayClassModulusToOriginal K m) := by
  let m' := rayClassModulusToOriginal K m
  let q : RayClass.primeToModulusIdeals m' →* RayClassGroup m :=
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
  let N := (RayClass.primeToModulusIdealNorm (K := K) (L := L) m').range
  have hnorm : rayClassIdealNormImage K L m = N.map q :=
    MonoidHom.range_comp q (RayClass.primeToModulusIdealNorm (K := K) (L := L) m')
  rw [hnorm]
  change (N.map q).comap q = N ⊔
    RayClass.principalRayIdealSubgroup m'
  rw [Subgroup.comap_map_eq]
  rw [show q.ker = rayPrincipalIdealSubgroupInPrimeTo m by
    exact QuotientGroup.ker_mk' (rayPrincipalIdealSubgroupInPrimeTo m)]
  rw [rayPrincipalIdealSubgroup_eq]

end ClassFieldTheory.GlobalClassFieldComparison
