/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
public import Nyll.ValuedFieldTheory.LocalField.NormUnits
public import Nyll.ClassFieldTheory.Definitions.NormTheorems.IsEverywhereLocalNorm
public import Nyll.ClassFieldTheory.Definitions.NormTheorems.IsNormAtFinitePlace
public import Nyll.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.GlobalNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment

/-!
# Mathlib-facing Hasse norm theorem

This module translates the idele-theoretic implementation of the cyclic
Hasse norm theorem into the implementation-independent predicates in
`ClassFieldTheory.Definitions.NormTheorems`.
-/



@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

universe u v

namespace GlobalClassFieldTheory.ClassFieldAxiom

/-- Implementation bridge for Hasse's norm theorem for finite cyclic
extensions. -/
theorem cyclicHasseNormTheorem
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (x : Kˣ) :
    ClassFieldTheory.IsFieldNorm K L x ↔
      ClassFieldTheory.IsEverywhereLocalNorm K L x := by
  rw [isFieldNorm_iff_mem_globalFieldNormSubgroup,
    isEverywhereLocalNorm_iff_mem_everywhereLocalFieldNormSubgroup,
    GlobalClassFieldTheory.ClassFieldAxiom.hasseNormPrinciple_cyclic K L]

end GlobalClassFieldTheory.ClassFieldAxiom
