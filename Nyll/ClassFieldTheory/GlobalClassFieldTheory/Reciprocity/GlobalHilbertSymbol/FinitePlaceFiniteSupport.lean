/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceCharacterComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
public import Mathlib.Algebra.FiniteSupport.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Finite support of finite-place Hilbert symbols

The finite-place Hilbert-symbol family is obtained by applying the Kummer
root character to the finite-place Artin factors of a principal idele.  Its
finite support therefore follows directly from the existing finite-support
theorem for those Artin factors; no second ramification-support construction
is needed here.
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open Function

variable (K : Type) [Field K] [NumberField K]

private theorem finitePlaceKummerRootCharacter_eq_chosenArtin
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    let L := chosenSimpleKummerExtension K n hnK b
    let : FiniteDimensional K L := chosenSimpleKummerExtension_finiteDimensional K n hnK b
    let : IsAbelianGalois K L := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    let : NumberField L := NumberField.of_module_finite K L
    let aᵥ := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a
    finitePlaceKummerRootCharacter K n hnK hmu v a b =
      (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm
        (chosenSimpleKummerRootCharacter K n hnK hmu b
          (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v aᵥ)) := by
  intro L fin ab nf aᵥ
  dsimp only [finitePlaceKummerRootCharacter, finitePlaceKummerRootCharacterOfExtension,
    chosenFinitePlaceArtinMonoidHom]

private theorem principalIdele_finiteComponent_eq_unitsMap
    (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
        (v.adicCompletion K)ˣ) =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
  apply Units.ext
  calc
    ((IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
        (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        ((a : K) : v.adicCompletion K) :=
      IdeleGroup.finiteComponent_principalIdele a v
    _ = algebraMap K (v.adicCompletion K) (a : K) := by
      symm
      have hmap := congrFun
        (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
          (R := 𝓞 K) (S := K) (K := K) (v := v)) (a : K)
      simpa using hmap

private theorem finitePlaceHilbertSymbol_eq_one_of_chosenUnitsArtin_eq_one
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    let L := chosenSimpleKummerExtension K n hnK b
    let : FiniteDimensional K L := chosenSimpleKummerExtension_finiteDimensional K n hnK b
    let : IsAbelianGalois K L := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    let : NumberField L := NumberField.of_module_finite K L
    let artin := chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
    artin (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a) = 1 →
      finitePlaceHilbertSymbol K n hnK hmu v a b = 1 := by
  intro L fin ab nf artin hOne
  have hArtin :
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a) = 1 := hOne
  rw [← finitePlaceKummerRootCharacter_localGlobal K n hnK hmu v a b,
    finitePlaceKummerRootCharacter_eq_chosenArtin K n hnK hmu v a b]
  rw [hArtin, map_one, map_one]

private def finitePlaceKummerArtinOnIdele
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ) (x : IdeleGroup K) :
    HeightOneSpectrum (𝓞 K) → Gal((chosenSimpleKummerExtension K n hnK b)/K) :=
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L := chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L := NumberField.of_module_finite K L
  fun v => chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v (IdeleGroup.finiteComponent v x)

private theorem finitePlaceKummerArtinOnIdele_hasFiniteMulSupport
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) (x : IdeleGroup K) :
    HasFiniteMulSupport (finitePlaceKummerArtinOnIdele K n hnK hmu b x) := by
  unfold finitePlaceKummerArtinOnIdele
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L := chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L := NumberField.of_module_finite K L
  with_reducible exact finitePlaceArtinFactors_hasFiniteMulSupport (K := K) (L := L) x

private theorem finitePlaceKummerArtinOnIdele_principal_eq
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    let L := chosenSimpleKummerExtension K n hnK b
    let : FiniteDimensional K L := chosenSimpleKummerExtension_finiteDimensional K n hnK b
    let : IsAbelianGalois K L := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    let : NumberField L := NumberField.of_module_finite K L
    finitePlaceKummerArtinOnIdele K n hnK hmu b (IdeleGroup.principalIdele K a) v =
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a) := by
  intro L fin ab nf
  unfold finitePlaceKummerArtinOnIdele
  rw [principalIdele_finiteComponent_eq_unitsMap K a v]

private theorem finitePlaceHilbertSymbol_eq_one_of_principalArtin_eq_one
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hOne : finitePlaceKummerArtinOnIdele K n hnK hmu b (IdeleGroup.principalIdele K a) v = 1) :
    finitePlaceHilbertSymbol K n hnK hmu v a b = 1 := by
  apply finitePlaceHilbertSymbol_eq_one_of_chosenUnitsArtin_eq_one K n hnK hmu a b v
  rw [finitePlaceKummerArtinOnIdele_principal_eq K n hnK hmu a b v] at hOne
  with_reducible exact hOne

/-- For fixed global units `a` and `b`, the finite-place Hilbert symbols are
nontrivial at only finitely many finite places. -/
theorem finitePlaceHilbertSymbol_hasFiniteMulSupport
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) =>
        finitePlaceHilbertSymbol K n hnK hmu v a b) := by
  have h := finitePlaceKummerArtinOnIdele_hasFiniteMulSupport K n hnK hmu b
    (IdeleGroup.principalIdele K a)
  refine h.subset ?_
  intro v hv hOne
  exact hv (finitePlaceHilbertSymbol_eq_one_of_principalArtin_eq_one K n hnK hmu a b v hOne)

end Reciprocity
end GlobalClassFieldTheory
