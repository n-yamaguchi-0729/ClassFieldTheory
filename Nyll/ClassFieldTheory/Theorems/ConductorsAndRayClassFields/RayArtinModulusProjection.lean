/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayArtin
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealModulusProjection
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealModulusProjectionPrime
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupHomExtFinitePrime
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin

/-!
# Naturality of ray Artin maps under reduction of the modulus

An embedding between two realizations of ray class fields intertwines the
Artin action with the canonical projection of ray class groups.  The
statement uses only Mathlib and public Definitions vocabulary; the idelic
implementation appears only in the proof.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v w z

namespace ClassFieldTheory

private local instance rayClassGroupCommGroup
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) : CommGroup (RayClassGroup m) :=
  { (inferInstance : Group (RayClassGroup m)) with mul_comm := mul_comm' }

private theorem rayArtin_prime_eq_arithmeticPrimeArtin
    {K : Type u} [Field K] [NumberField K]
    {m : RayClassModulus K} (R : RayClassFieldRealization K m)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    R.rayArtin (rayClassOfFinitePrime m v hv) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := R.extension) v := by
  let w₀ := _root_.chosenFinitePlaceExtension (L := R.extension) v
  let w := _root_.finitePlaceExtensionCentre (K := K) (L := R.extension) v w₀
  have hw : w.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := R.extension) v w₀
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (R.unramifiedOutsideModulus.1 v hv) w.asIdeal inferInstance hw
  calc
    R.rayArtin (rayClassOfFinitePrime m v hv) =
        arithmeticFrobeniusAt (K := K) w := R.artin_frobenius v hv w hw
    _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := R.extension) v :=
      (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := R.extension) v w hw hunram).symm

private theorem arithmeticPrimeArtin_restrict_tower
    {K : Type u} {E : Type v} {L : Type w}
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Field L] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    AlgEquiv.restrictNormalHom E
        (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := E) v := by
  open GlobalClassFieldTheory.GlobalClassFields in
  rw [arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := L) v,
    arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := E) v, map_inv]
  simpa only [GlobalClassFieldTheory.GlobalClassFields.finitePlacePrimeArtin,
    MonoidHom.comp_apply] using
    congrArg Inv.inv
      (DFunLike.congr_fun
        (GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_restrict_tower
          (K := K) (L := L) (E := E))
        (IdeleGroup.finitePrimeIdele v))

private theorem rayClassGroup_hom_ext_of_prime
    {K : Type u} [Field K] [NumberField K]
    {G : Type z} [Monoid G]
    (n : RayClassModulus K)
    (f g : RayClassGroup n →* G)
    (hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ n.finitePart.support),
        f (rayClassOfFinitePrime n v hv) =
          g (rayClassOfFinitePrime n v hv)) :
    f = g :=
  rayClassGroup_hom_ext_finitePrime K n f g hprime

/-- Artin reciprocity commutes with reduction of the modulus along any
embedding of the corresponding ray class field realizations. -/
theorem rayArtin_modulusProjection
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n)
    (Rm : RayClassFieldRealization K m)
    (Rn : RayClassFieldRealization K n)
    (f : Rm.extension →ₐ[K] Rn.extension)
    (x : RayClassGroup n) (y : Rm.extension) :
    Rn.rayArtin x (f y) =
      f (Rm.rayArtin (rayClassIdealModulusProjection K hmn x) y) := by
  let : Algebra Rm.extension Rn.extension := f.toRingHom.toAlgebra
  let : IsScalarTower K Rm.extension Rn.extension :=
    IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm
  let : CommGroup (Rm.extension ≃ₐ[K] Rm.extension) :=
    { (inferInstance : Group (Rm.extension ≃ₐ[K] Rm.extension)) with
      mul_comm := mul_comm' }
  have hnat :
      (AlgEquiv.restrictNormalHom Rm.extension).comp Rn.rayArtin =
        Rm.rayArtin.comp (rayClassIdealModulusProjection K hmn) := by
    apply rayClassGroup_hom_ext_of_prime n
    intro v hvn
    have hvm : v ∉ m.finitePart.support := by
      intro hv
      exact hvn (Finsupp.support_mono hmn.1 hv)
    change AlgEquiv.restrictNormalHom Rm.extension
      (Rn.rayArtin (rayClassOfFinitePrime n v hvn)) =
      Rm.rayArtin
        (rayClassIdealModulusProjection K hmn
          (rayClassOfFinitePrime n v hvn))
    rw [rayClassIdealModulusProjection_prime K hmn v hvn,
      rayArtin_prime_eq_arithmeticPrimeArtin Rn v hvn,
      rayArtin_prime_eq_arithmeticPrimeArtin Rm v hvm]
    exact arithmeticPrimeArtin_restrict_tower v
  have hx := DFunLike.congr_fun hnat x
  change AlgEquiv.restrictNormalHom Rm.extension (Rn.rayArtin x) =
    Rm.rayArtin (rayClassIdealModulusProjection K hmn x) at hx
  have hy := congrArg (fun σ : Rm.extension ≃ₐ[K] Rm.extension => f (σ y)) hx
  exact (AlgEquiv.restrictNormal_commutes (Rn.rayArtin x) Rm.extension y).symm.trans hy

/-- The identity modulus and identity field embedding preserve the same
Artin value. -/
theorem rayArtin_modulusProjection_refl
    {K : Type u} [Field K] [NumberField K]
    {m : RayClassModulus K} (R : RayClassFieldRealization K m)
    (x : RayClassGroup m) (y : R.extension) :
    R.rayArtin x (AlgHom.id K R.extension y) =
      AlgHom.id K R.extension
        (R.rayArtin (rayClassIdealModulusProjection K (le_refl m) x) y) :=
  rayArtin_modulusProjection (le_refl m) R R (AlgHom.id K R.extension) x y

/-- Successive field embeddings intertwine the Artin action with the two
actual modulus projections. -/
theorem rayArtin_modulusProjection_comp
    {K : Type u} [Field K] [NumberField K]
    {m n p : RayClassModulus K} (hmn : m ≤ n) (hnp : n ≤ p)
    (Rm : RayClassFieldRealization K m)
    (Rn : RayClassFieldRealization K n)
    (Rp : RayClassFieldRealization K p)
    (f : Rm.extension →ₐ[K] Rn.extension)
    (g : Rn.extension →ₐ[K] Rp.extension)
    (x : RayClassGroup p) (y : Rm.extension) :
    Rp.rayArtin x ((g.comp f) y) =
      (g.comp f) (Rm.rayArtin
        (rayClassIdealModulusProjection K hmn
          (rayClassIdealModulusProjection K hnp x)) y) := by
  change Rp.rayArtin x (g (f y)) = g (f (Rm.rayArtin _ y))
  rw [rayArtin_modulusProjection hnp Rn Rp g,
    rayArtin_modulusProjection hmn Rm Rn f]

end ClassFieldTheory
