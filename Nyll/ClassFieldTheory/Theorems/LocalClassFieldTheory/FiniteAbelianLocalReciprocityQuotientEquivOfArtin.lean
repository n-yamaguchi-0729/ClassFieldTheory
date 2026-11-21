/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# The norm quotient induced by a specified finite local Artin map

The first isomorphism theorem determines the quotient equivalence from any
specified continuous surjective homomorphism with the field-norm kernel.
This is distinct from uniqueness of the Artin map itself.
-/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Any specified continuous surjective homomorphism with the field-norm
kernel induces one and only one continuous equivalence of the norm quotient.
The equivalence evaluates to the specified map on every quotient class. -/
theorem finiteAbelianLocalReciprocity_quotientEquiv_of_artin
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (artin : Kˣ →ₜ* (L ≃ₐ[K] L))
    (hsurj : Function.Surjective artin)
    (hker : artin.ker = localNormSubgroup K L) :
    ∃! e : FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L),
      ∀ x : Kˣ, e (QuotientGroup.mk' (localNormSubgroup K L) x) = artin x :=
  ProCGroups.QuotientGroup.existsUnique_quotientContinuousMulEquiv_of_surjective
    artin (localNormSubgroup K L) hsurj hker

end ClassFieldTheory
