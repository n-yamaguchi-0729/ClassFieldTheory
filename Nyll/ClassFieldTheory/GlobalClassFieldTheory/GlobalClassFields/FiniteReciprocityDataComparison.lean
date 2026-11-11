/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction

/-!
# The actual idèle-class value of finite reciprocity data

Every Frobenius-normalized finite reciprocity datum gives the same arithmetic
norm-residue value on every idèle class. The proof uses its prime values and
the existing ray Frobenius rigidity theorem, including at ramified places.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory.GlobalClassFieldComparison
open GlobalClassFieldTheory.GlobalClassFields

noncomputable section

namespace ClassFieldTheory.FiniteAbelianReciprocityData

universe u v

variable {K : Type u} {L : Type v}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  (D : FiniteAbelianReciprocityData K L)

omit [FiniteDimensional K L] in
/-- The given finite Artin map has the original arithmetic prime value after
the actual ideal-to-idèle ray-class comparison. -/
theorem originalArtin_prime (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ D.modulus.finitePart.support) :
    (D.artin.comp (rayClassGroupEquivOriginalIdele K D.modulus).symm.toMonoidHom)
        (QuotientGroup.mk'
          (rayClassModulusToOriginal K D.modulus).congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele p))) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) p := by
  let e := rayClassGroupEquivOriginalIdele K D.modulus
  change D.artin (e.symm (QuotientGroup.mk'
    (rayClassModulusToOriginal K D.modulus).congruenceSubgroup
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (IdeleGroup.finitePrimeIdele p)))) = _
  rw [← rayClassGroupEquivOriginalIdele_prime K D.modulus p hp]
  have hFrob : D.artin (rayClassOfFinitePrime D.modulus p hp) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) p := by
    let w₀ := _root_.chosenFinitePlaceExtension (L := L) p
    let w := _root_.finitePlaceExtensionCentre (K := K) (L := L) p w₀
    have hw : w.asIdeal.LiesOver p.asIdeal :=
      _root_.finitePlaceExtensionCentre_liesOver (K := K) (L := L) p w₀
    have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
      (D.unramifiedOutsideModulus.1 p hp) w.asIdeal inferInstance hw
    calc
      D.artin (rayClassOfFinitePrime D.modulus p hp) =
          arithmeticFrobeniusAt (K := K) w := D.artin_frobenius p hp w hw
      _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) p :=
        (arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
          (K := K) (L := L) p w hw hunram).symm
  simpa only [e, MulEquiv.symm_apply_apply] using hFrob

/-- Pull the given ray Artin map back along the original idèle-class quotient.
No Artin map or reciprocity datum is chosen again. -/
noncomputable def ideleClassArtin : IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  D.artin.comp
    ((rayClassGroupEquivOriginalIdele K D.modulus).symm.toMonoidHom.comp
      (QuotientGroup.mk'
        (rayClassModulusToOriginal K D.modulus).congruenceSubgroup))

/-- Prime normalization determines the actual value on every idèle class. -/
theorem ideleClassArtin_apply (x : IdeleClassGroup K) :
    D.ideleClassArtin x =
      GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L x := by
  exact rayArtin_comp_ideleClass_eq_arithmeticGlobalNormResidue
      (rayClassModulusToOriginal K D.modulus)
      (D.artin.comp (rayClassGroupEquivOriginalIdele K D.modulus).symm.toMonoidHom)
      (D.originalArtin_prime) x

/-- The equality is of the same homomorphisms, not only their kernels. -/
theorem ideleClassArtin_eq_arithmeticGlobalNormResidue :
    D.ideleClassArtin =
      GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L := by
  apply MonoidHom.ext
  exact D.ideleClassArtin_apply

end ClassFieldTheory.FiniteAbelianReciprocityData
