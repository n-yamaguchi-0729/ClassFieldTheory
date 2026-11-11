/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Quotient form of finite abelian local reciprocity

This module states the quotient formulation of local reciprocity for a
finite abelian extension `L / K` of a nonarchimedean local field.  Under the
finite-dimensional, abelian-Galois, valuative, and topological assumptions,
the conclusion identifies `Kˣ / N_{L/K}(Lˣ)` with the ordinary Galois group
by a continuous multiplicative equivalence.
The equivalence is induced by the same specified universe-polymorphic
Artin map, using its quotient universal property.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The field-norm quotient is continuously multiplicatively equivalent to
the finite abelian Galois group. -/
theorem finiteAbelianLocalReciprocity_quotient
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nonempty
      (FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L)) := by
  obtain ⟨e, _, _⟩ := LocalClassFieldTheory.Universe.quotientEquiv_existsUnique K L
  exact ⟨e⟩

end ClassFieldTheory
