/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.GaloisAction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.GaloisDescent
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormProduct
import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic

/-!
# Actual function-field norms and the Tate norm

The Galois product formula identifies the actual all-place norm, followed by
base change, with the existing Tate norm. Injectivity of base change identifies
their kernels. The norm images correspond under base change, while the base
idele groups map into the actual fixed subgroups.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

namespace IdeleGroup

/-- Base ideles give fixed points for the actual extension action. -/
def baseChangeToFixed :
    IdeleGroup k K →* fixedSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) where
  toFun a := ⟨baseChange (k := k) (K := K) (L := L) a,
    fun σ => algAut_smul_baseChange σ a⟩
  map_one' := Subtype.ext (map_one (baseChange (k := k) (K := K) (L := L)))
  map_mul' a b := Subtype.ext (map_mul (baseChange (k := k) (K := K) (L := L)) a b)

omit [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] in
/-- The map from base ideles to the fixed subgroup is injective. -/
theorem baseChangeToFixed_injective :
    Function.Injective (baseChangeToFixed (k := k) (K := K) (L := L)) := by
  intro a b h
  exact baseChange_injective (k := k) (K := K) (L := L)
    (congrArg Subtype.val h)

variable [IsGalois K L]

/-- The actual idele norm becomes the existing Tate norm after base change. -/
theorem baseChange_norm_eq_tateNorm (a : IdeleGroup k L) :
    baseChange (k := k) (K := K) (L := L) (norm (k := k) (K := K) (L := L) a) =
      tateNorm (L ≃ₐ[K] L) (IdeleGroup k L) a :=
  baseChange_norm_eq_prod_algAut a

/-- Equality of the actual composite norm homomorphism and the Tate norm. -/
theorem baseChange_comp_norm_eq_tateNormHom :
    (baseChange (k := k) (K := K) (L := L)).comp (norm (k := k) (K := K) (L := L)) =
      tateNormHom (G := L ≃ₐ[K] L) (A := IdeleGroup k L) := by
  apply MonoidHom.ext
  intro a
  exact baseChange_norm_eq_tateNorm (k := k) (K := K) (L := L) a

/-- A completed idele has actual norm one exactly when its Tate norm is one. -/
theorem norm_eq_one_iff_tateNorm_eq_one (a : IdeleGroup k L) :
    norm (k := k) (K := K) (L := L) a = 1 ↔
      tateNorm (L ≃ₐ[K] L) (IdeleGroup k L) a = 1 := by
  rw [← baseChange_norm_eq_tateNorm]
  exact (map_eq_one_iff (baseChange (k := k) (K := K) (L := L))
    (baseChange_injective (k := k) (K := K) (L := L))).symm

/-- The actual norm kernel is the kernel used in low-degree Tate cohomology. -/
theorem norm_ker_eq_normKernelSubgroup :
    (norm (k := k) (K := K) (L := L)).ker =
      normKernelSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) := by
  ext a
  exact norm_eq_one_iff_tateNorm_eq_one a

/-- Base change carries the actual norm image to the Tate norm subgroup. -/
theorem norm_range_map_baseChange_eq_tateNormSubgroup :
    (norm (k := k) (K := K) (L := L)).range.map
        (baseChange (k := k) (K := K) (L := L)) =
      tateNormSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) := by
  rw [MonoidHom.map_range, baseChange_comp_norm_eq_tateNormHom]
  rfl

end IdeleGroup

namespace IdeleClassGroup

/-- Base idele classes map to the fixed subgroup for the completed Galois action. -/
def baseChangeToFixed :
    IdeleClassGroup k K →* fixedSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) where
  toFun c := ⟨baseChange (k := k) (K := K) (L := L) c,
    fun σ => algAut_smul_baseChange σ c⟩
  map_one' := Subtype.ext (map_one (baseChange (k := k) (K := K) (L := L)))
  map_mul' c d := Subtype.ext (map_mul (baseChange (k := k) (K := K) (L := L)) c d)

variable [IsGalois K L]

/-- The norm on the principal-idele quotient is the Tate norm after base change. -/
theorem baseChange_norm_eq_tateNorm (c : IdeleClassGroup k L) :
    baseChange (k := k) (K := K) (L := L) (norm (k := k) (K := K) (L := L) c) =
      tateNorm (L ≃ₐ[K] L) (IdeleClassGroup k L) c :=
  baseChange_norm_eq_prod_algAut c

/-- The actual norm composite on classes is the existing Tate norm homomorphism. -/
theorem baseChange_comp_norm_eq_tateNormHom :
    (baseChange (k := k) (K := K) (L := L)).comp (norm (k := k) (K := K) (L := L)) =
      tateNormHom (G := L ≃ₐ[K] L) (A := IdeleClassGroup k L) := by
  apply MonoidHom.ext
  intro c
  exact baseChange_norm_eq_tateNorm (k := k) (K := K) (L := L) c

/-- The actual class norm image gives the Tate norm subgroup under base change. -/
theorem norm_range_map_baseChange_eq_tateNormSubgroup :
    (norm (k := k) (K := K) (L := L)).range.map
        (baseChange (k := k) (K := K) (L := L)) =
      tateNormSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) := by
  rw [MonoidHom.map_range, baseChange_comp_norm_eq_tateNormHom]
  rfl

/-- Galois descent makes the map from base classes to fixed classes injective. -/
theorem baseChangeToFixed_injective :
    Function.Injective (baseChangeToFixed (k := k) (K := K) (L := L)) := by
  intro c d h
  exact baseChange_injective (k := k) (K := K) (L := L)
    (congrArg Subtype.val h)

/-- The actual class norm is one exactly when its Tate norm is one. -/
theorem norm_eq_one_iff_tateNorm_eq_one (c : IdeleClassGroup k L) :
    norm (k := k) (K := K) (L := L) c = 1 ↔
      tateNorm (L ≃ₐ[K] L) (IdeleClassGroup k L) c = 1 := by
  rw [← baseChange_norm_eq_tateNorm]
  exact (map_eq_one_iff (baseChange (k := k) (K := K) (L := L))
    (baseChange_injective (k := k) (K := K) (L := L))).symm

/-- The actual norm kernel on idele classes is the low-degree Tate norm kernel. -/
theorem norm_ker_eq_normKernelSubgroup :
    (norm (k := k) (K := K) (L := L)).ker =
      normKernelSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) := by
  ext c
  exact norm_eq_one_iff_tateNorm_eq_one c

end IdeleClassGroup

end FunctionField
