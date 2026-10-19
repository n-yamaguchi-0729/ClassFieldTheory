/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.ExtensionRepresentation
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormComparison

/-!
# Actual Galois products of abstract norm values

The actual fixed-field action comparison reindexes each abstract norm sum
by the relative Galois group.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology
open IdeleClassGroup.FiniteExtensionLimit
open scoped BigOperators

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- The abstract norm value is the actual relative Galois product in the limit. -/
theorem abstractFixedClassEquiv_relativeNormValue (H J : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup) (hnormal : (extensionSubgroup H J hJH).Normal)
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) J (le_baseField J)))
    [Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)] :
    let _ : FiniteDimensional K (abstractFixedField K Ω J) :=
      abstractFixedField_finiteDimensional K Ω J hfinite
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ := hnormal
    let _ : FiniteDimensional (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      FiniteDimensional.right K _ _
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω J)),
      (relativeNorm (ideleClassRepresentation k K Ω) H J hJH
          (abstractFixedClassEquiv k K Ω J hfinite c)).1 =
        Additive.ofMul (ofIntermediate (k := k) (abstractFixedField K Ω J)
          (∏ σ : Gal((abstractFixedField K Ω J)/(abstractFixedField K Ω H)),
            AlgebraicCurve.SemilinearAut.ofAlgAut (σ.restrictScalars k) • c.toMul)) := by
  intro hEfinite aFE hKFE hkFE hnorm hFEfinite c
  let r : (H.toSubgroup ⧸ extensionSubgroup H J hJH) ≃*
      Gal((abstractFixedField K Ω J)/(abstractFixedField K Ω H)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hnormal
  let i : Additive (IdeleClassGroup k (abstractFixedField K Ω J)) →+ Additive (Limit k K Ω) :=
    MonoidHom.toAdditive (ofIntermediate (k := k) (abstractFixedField K Ω J))
  change _ = i (∑ σ : Gal((abstractFixedField K Ω J)/(abstractFixedField K Ω H)),
    Additive.ofMul (AlgebraicCurve.SemilinearAut.ofAlgAut (σ.restrictScalars k) • c.toMul))
  exact relativeNorm_eq_mapped_sum (ideleClassRepresentation k K Ω) H J hJH
    (abstractFixedClassEquiv k K Ω J hfinite c) i r.toEquiv
    (fun σ => Additive.ofMul
      (AlgebraicCurve.SemilinearAut.ofAlgAut (σ.restrictScalars k) • c.toMul))
    (fun q => abstractFixedClassEquiv_relativeCosetAction k K Ω H J hJH hnormal hfinite q c)

end FunctionField
