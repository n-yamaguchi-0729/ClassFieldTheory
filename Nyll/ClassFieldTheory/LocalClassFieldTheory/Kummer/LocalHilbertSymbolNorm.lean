/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteGeneration

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtensionBaseChange
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters

/-!
# Norm and base-change formulas for the actual local Hilbert symbol

The same chosen simple Kummer extensions are joined by a field embedding.
Actual norm--restriction naturality then identifies their Artin root
quotients. Only separability of the finite base extension is required.
-/

@[expose] public section

namespace LocalClassFieldTheory.Kummer

open KummerTheory LocalFieldTheory

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- The Hilbert symbol of a norm is the symbol over the extension, with its
second argument and roots of unity sent by the actual algebra map. The finite
separable extension `L/K` need not be Galois. -/
theorem localHilbertSymbol_norm
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hnL : ((n : ℕ) : L) ≠ 0)
    (hmuK : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmuL : (primitiveRoots (n : ℕ) L).Nonempty) (a : Lˣ) (b : Kˣ) :
    nthRootsSubgroupMap K L (n : ℕ)
        (localHilbertSymbol K n hnK hmuK (normUnits K L a) b) =
      localHilbertSymbol L n hnL hmuL a
        (Units.map (algebraMap K L).toMonoidHom b) := by
  let bL : Lˣ := Units.map (algebraMap K L).toMonoidHom b
  let E := chosenSimpleKummerExtension K n hnK b
  let F := chosenSimpleKummerExtension L n hnL bL
  let : Algebra K F := ((algebraMap L F).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq' rfl
  let e : E →ₐ[K] F := Classical.choice
    (chosenSimpleKummerExtension_baseChange_nonempty K L n hnK hnL hmuL b)
  let : Algebra E F := e.toRingHom.toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (e.commutes x).symm)
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmuK b
  let : FiniteDimensional L F :=
    chosenSimpleKummerExtension_finiteDimensional L n hnL bL
  let : IsAbelianGalois L F :=
    chosenSimpleKummerExtension_isAbelianGalois L n hnL hmuL bL
  let betaE : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  let betaF : Fˣ := chosenSimpleKummerRootUnit L n hnL bL
  let sigma : Gal(F/L) := chosenSimpleKummerNormResidueAutomorphism L n hnL hmuL bL a
  have hnat : AlgEquiv.restrictNormalHom E (sigma.restrictScalars K) =
      chosenSimpleKummerNormResidueAutomorphism K n hnK hmuK b (normUnits K L a) := by
    exact DFunLike.congr_fun (LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction
        K L E F) a
  have hpow : (Units.map (algebraMap E F).toMonoidHom betaE) ^ (n : ℕ) =
      Units.map (algebraMap L F).toMonoidHom bL := by
    rw [← map_pow, chosenSimpleKummerRootUnit_pow]
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply K E F (b : K)).symm.trans
      (IsScalarTower.algebraMap_apply K L F (b : K))
  have hK := congrArg Subtype.val
    (localHilbertSymbol_map_eq_rootQuotient K n hnK hmuK (normUnits K L a) b)
  have hL := congrArg Subtype.val
    (localHilbertSymbol_map_eq_rootQuotient L n hnL hmuL a bL)
  apply nthRootsSubgroupMap_injective L F (n : ℕ)
  apply Subtype.ext
  change Units.map (algebraMap L F).toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom
        (localHilbertSymbol K n hnK hmuK (normUnits K L a) b).1) =
    Units.map (algebraMap L F).toMonoidHom
      (localHilbertSymbol L n hnL hmuL a bL).1
  calc
    _ = Units.map (algebraMap E F).toMonoidHom
        (Units.map (algebraMap K E).toMonoidHom
          (localHilbertSymbol K n hnK hmuK (normUnits K L a) b).1) := by
      apply Units.ext
      exact (IsScalarTower.algebraMap_apply K L F _).symm.trans
        (IsScalarTower.algebraMap_apply K E F _)
    _ = Units.map (algebraMap E F).toMonoidHom
        (rootQuotient (K := K) (L := E) betaE
          (chosenSimpleKummerNormResidueAutomorphism K n hnK hmuK b
            (normUnits K L a))) := congrArg (Units.map (algebraMap E F).toMonoidHom) hK
    _ = rootQuotient (K := K) (L := F)
        (Units.map (algebraMap E F).toMonoidHom betaE) (sigma.restrictScalars K) := by
      rw [← hnat]
      exact (rootQuotient_map_restrictNormal betaE (sigma.restrictScalars K)).symm
    _ = rootQuotient (K := L) (L := F) betaF sigma := by
      change rootQuotient (K := L) (L := F)
        (Units.map (algebraMap E F).toMonoidHom betaE) sigma = _
      exact rootQuotient_eq_of_same_pow_of_primitiveRoots L n hmuL bL
        (Units.map (algebraMap E F).toMonoidHom betaE) betaF hpow
        (chosenSimpleKummerRootUnit_pow L n hnL bL) sigma
    _ = _ := hL.symm

/-- On two base-field arguments, extension of scalars raises the actual
Hilbert symbol to the degree of the finite separable extension. -/
theorem localHilbertSymbol_baseChange
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hnL : ((n : ℕ) : L) ≠ 0)
    (hmuK : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmuL : (primitiveRoots (n : ℕ) L).Nonempty) (a b : Kˣ) :
    localHilbertSymbol L n hnL hmuL
        (Units.map (algebraMap K L).toMonoidHom a)
        (Units.map (algebraMap K L).toMonoidHom b) =
      nthRootsSubgroupMap K L (n : ℕ)
        (localHilbertSymbol K n hnK hmuK a b ^ Module.finrank K L) := by
  have hnorm : normUnits K L (Units.map (algebraMap K L).toMonoidHom a) =
      a ^ Module.finrank K L := by
    apply Units.ext
    change Algebra.norm K (algebraMap K L (a : K)) = (a : K) ^ Module.finrank K L
    exact Algebra.norm_algebraMap (a : K)
  rw [← localHilbertSymbol_norm K L n hnK hnL hmuK hmuL, hnorm]
  exact congrArg (nthRootsSubgroupMap K L (n : ℕ))
    ((localHilbertSymbolHom K n hnK hmuK b).map_pow a (Module.finrank K L))

end LocalClassFieldTheory.Kummer
