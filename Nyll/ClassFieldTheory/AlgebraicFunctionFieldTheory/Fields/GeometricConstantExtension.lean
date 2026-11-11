/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionGeneration
public import Nyll.AlgebraicCurves.FunctionFields.Tsen.ConstantTsen
public import Mathlib.FieldTheory.IsSepClosed

/-!
# The actual geometric constant extension and Tsen

Adjoin all algebraic constants inside the given separably closed ambient field.
The supplied scalar structure and actual generation theorem give a separating
parameter, so Tsen applies to this actual field and all of its finite extensions.
-/

@[expose] public section

universe u v w x

noncomputable section

namespace FunctionField

open AlgebraicCurve AlgebraicGeometry CategoryTheory

section Algebraic

variable (k : Type u) (K : Type v) (Ω : Type w) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- The actual compositum of the original function field and all algebraic constants. -/
abbrev geometricConstantExtension : IntermediateField K Ω :=
  IntermediateField.adjoin K (separableClosure k Ω : Set Ω)

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The actual geometric constant extension is a curve field over its extended constants. -/
theorem geometricConstantExtension_isCurveOver :
    let _ : Algebra (separableClosure k Ω) (geometricConstantExtension k K Ω) :=
      constantAlgebra (K := K) (separableClosure k Ω)
    IsCurveOver (separableClosure k Ω) (geometricConstantExtension k K Ω) := by
  intro algC
  have hcurve : IsCurveOver k K := isCurveOver k K
  have hft : Algebra.EssFiniteType k K := essFiniteType k K
  have htower : IsScalarTower k (separableClosure k Ω) (geometricConstantExtension k K Ω) :=
    constantScalarTower (K := K) (separableClosure k Ω)
  exact isCurveOver_constantBaseChange (k := k)
    (constantExtension_adjoin_originalField (K := K) (separableClosure k Ω))

variable [IsSepClosed Ω]

/-- Every finite field norm over the actual geometric constant extension is surjective. -/
theorem geometricConstantExtension_norm_surjective
    (L : Type x) [Field L] [Algebra (geometricConstantExtension k K Ω) L]
    [FiniteDimensional (geometricConstantExtension k K Ω) L] :
    Function.Surjective (Algebra.norm (geometricConstantExtension k K Ω) : L →*
      geometricConstantExtension k K Ω) := by
  let algC : Algebra (separableClosure k Ω) (geometricConstantExtension k K Ω) :=
    constantAlgebra (K := K) (separableClosure k Ω)
  have hcurve : IsCurveOver k K := isCurveOver k K
  have hft : Algebra.EssFiniteType k K := essFiniteType k K
  have htower : IsScalarTower k (separableClosure k Ω) (geometricConstantExtension k K Ω) :=
    constantScalarTower (K := K) (separableClosure k Ω)
  have hclosed : IsAlgClosed (separableClosure k Ω) :=
    IsAlgClosure.isAlgClosed (R := k) (K := separableClosure k Ω)
  exact norm_surjective_constantBaseChange (k := k)
    (constantExtension_adjoin_originalField (K := K) (separableClosure k Ω)) L

end Algebraic

section NativeCohomology

variable (k K Ω : Type) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

variable [IsSepClosed Ω]

/-- Actual finite Galois unit H² vanishes over the constructed geometric constant extension. -/
theorem geometricConstantExtension_galoisUnitsH2_eq_zero
    (L : Type) [Field L] [Algebra (geometricConstantExtension k K Ω) L]
    [FiniteDimensional (geometricConstantExtension k K Ω) L]
    [IsGalois (geometricConstantExtension k K Ω) L]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits (geometricConstantExtension k K Ω) L) 2) :
    c = 0 := by
  let algC : Algebra (separableClosure k Ω) (geometricConstantExtension k K Ω) :=
    constantAlgebra (K := K) (separableClosure k Ω)
  have hcurve : IsCurveOver k K := isCurveOver k K
  have hft : Algebra.EssFiniteType k K := essFiniteType k K
  have htower : IsScalarTower k (separableClosure k Ω) (geometricConstantExtension k K Ω) :=
    constantScalarTower (K := K) (separableClosure k Ω)
  have hclosed : IsAlgClosed (separableClosure k Ω) :=
    IsAlgClosure.isAlgClosed (R := k) (K := separableClosure k Ω)
  exact galoisUnitsH2_eq_zero_constantBaseChange (k := k)
    (constantExtension_adjoin_originalField (K := K) (separableClosure k Ω)) L c

/-- Actual finite constant-coefficient étale cohomology of the constructed
geometric function field vanishes above degree one. The original finite-field
function-field data supply the extension and the separating parameter. -/
theorem geometricConstantExtension_constantFinite_etaleCohomology_eq_zero
    (A : AddCommGrpCat.{0}) [Finite A] (n : ℕ)
    (v : Sheaf.H.{0}
      ((constantSheaf (Spec (.of (geometricConstantExtension k K Ω))).smallEtaleTopology
        AddCommGrpCat.{0}).obj A) (n + 2)) : v = 0 := by
  let algC : Algebra (separableClosure k Ω) (geometricConstantExtension k K Ω) :=
    constantAlgebra (K := K) (separableClosure k Ω)
  have hcurve : IsCurveOver k K := isCurveOver k K
  have hft : Algebra.EssFiniteType k K := essFiniteType k K
  have htower : IsScalarTower k (separableClosure k Ω) (geometricConstantExtension k K Ω) :=
    constantScalarTower (K := K) (separableClosure k Ω)
  have hclosed : IsAlgClosed (separableClosure k Ω) :=
    IsAlgClosure.isAlgClosed (R := k) (K := separableClosure k Ω)
  exact fieldEtale_constantFinite_cohomology_eq_zero_constantBaseChange (k := k)
    (constantExtension_adjoin_originalField (K := K) (separableClosure k Ω)) A n v

end NativeCohomology

end FunctionField
