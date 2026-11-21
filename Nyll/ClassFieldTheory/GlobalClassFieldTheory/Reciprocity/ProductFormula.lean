/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteLocalFamily
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation

/-!
# The local--global norm-symbol bridge

The standard idèle-class embedding sends the chosen local norm group into
the determinant-norm range. The induced homomorphism on norm quotients gives
the finite-support and principal-idèle product identities.
-/

open scoped NumberField BigOperators
open NumberField IsDedekindDomain
open IdeleGroup

noncomputable section

universe u v

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

local notation "NormQuotient" =>
  NumberField.IdeleClassGroup (𝓞 K) K ⧸ MonoidHom.range (NumberField.IdeleClassGroup.norm K L)

private theorem finitePlace_mem_standardNormRange
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ)
    (hx : x ∈ chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v) :
    NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x ∈
      (NumberField.IdeleClassGroup.norm K L).range := by
  have h := (finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
    (K := K) (L := L) v x).2 hx
  change finitePlaceIdele v x ∈ (IdeleGroup.norm K L).range at h
  obtain ⟨a, ha⟩ := h
  refine ⟨IdeleGroup.toStandardClass L a, ?_⟩
  rw [_root_.ideleClassNorm_mk, ha, IdeleGroup.toStandardClass_finitePlaceIdele]

/-- The finite-place insertion descends to the quotient by the standard
idèle-class norm. -/
noncomputable def finitePlaceNormQuotientToGlobalClass
    (v : HeightOneSpectrum (𝓞 K)) :
    ChosenFinitePlaceNormQuotient (K := K) (L := L) v →* NormQuotient :=
  QuotientGroup.lift (chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v)
    ((QuotientGroup.mk' (NumberField.IdeleClassGroup.norm K L).range).comp
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v))
    (fun x hx => (QuotientGroup.eq_one_iff _).2 (finitePlace_mem_standardNormRange v x hx))

/-- Exact local--global compatibility on representatives. -/
@[simp]
theorem finitePlaceNormQuotientToGlobalClass_localClass
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    finitePlaceNormQuotientToGlobalClass (K := K) (L := L) v
        (finitePlaceTensorNormClass (K := K) (L := L) v a) =
      QuotientGroup.mk' (NumberField.IdeleClassGroup.norm K L).range
        (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v a) :=
  rfl

/-- A character of the standard class norm quotient, evaluated at the
one-place class at `v`. -/
noncomputable def finitePlaceGlobalSymbol
    {A : Type*} [CommGroup A]
    (chi : NormQuotient →* A) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* A :=
  chi.comp
    ((QuotientGroup.mk' (NumberField.IdeleClassGroup.norm K L).range).comp
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v))

/-- The one-place global symbol is the character of the transported local norm class. -/
@[simp]
theorem finitePlaceGlobalSymbol_eq_localNormClass
    {A : Type*} [CommGroup A]
    (chi : NormQuotient →* A)
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    finitePlaceGlobalSymbol (K := K) (L := L) chi v a =
      chi (finitePlaceNormQuotientToGlobalClass (K := K) (L := L) v
        (finitePlaceTensorNormClass (K := K) (L := L) v a)) :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Finite-support form of the product formula for a standard norm-quotient character. -/
theorem finitePlaceGlobalSymbol_finiteLocalFamily
    {A : Type*} [CommGroup A]
    (chi : NormQuotient →* A)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    ∏ v : ↥S, finitePlaceGlobalSymbol (K := K) (L := L) chi v.1 (a v) =
      chi (globalNormClassFromIdele K L (IdeleGroup.ideleOfFiniteLocalFamily S a)) := by
  let : CommGroup (NumberField.IdeleClassGroup (𝓞 K) K) :=
    QuotientGroup.Quotient.commGroup (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
  rw [globalNormClass_finiteLocalFamily, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact congrArg chi (globalNormClassFromIdele_finitePlaceIdele K L v.1 (a v)).symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A global norm-quotient character is trivial on a principal idèle. -/
theorem globalNormQuotientCharacter_principal
    {A : Type*} [CommGroup A]
    (chi : NormQuotient →* A)
    (x : Kˣ) :
  chi
        (globalNormClassFromIdele K L
          (IdeleGroup.principalIdele K x)) = 1 := by
  rw [globalNormClassFromIdele_principalIdele, map_one]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Exact bridge from a finite local representative of a principal global
norm class to the product-one identity.  The premise is a concrete equality
in `C_K / N C_L`, not a product-formula assumption. -/
theorem finitePlaceGlobalSymbol_product_eq_one_of_eq_principal
    {A : Type*} [CommGroup A]
    (chi : NormQuotient →* A)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (x : Kˣ)
    (hprincipal :
      globalNormClassFromIdele K L
          (IdeleGroup.ideleOfFiniteLocalFamily S a) =
        globalNormClassFromIdele K L
          (IdeleGroup.principalIdele K x)) :
    ∏ v : ↥S,
        finitePlaceGlobalSymbol (K := K) (L := L) chi v.1 (a v) = 1 := by
  rw [finitePlaceGlobalSymbol_finiteLocalFamily]
  rw [hprincipal]
  exact globalNormQuotientCharacter_principal chi x

end Reciprocity
end GlobalClassFieldTheory
