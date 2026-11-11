/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IdeleClassConnectedQuotient
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibTopologicalGlobalReciprocity
public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# Topological global reciprocity

For a number field `K`, the idèle class group modulo its identity component
is topologically isomorphic to the maximal abelian quotient of the absolute
Galois group. The statement uses Mathlib's groups on both sides.
-/

@[expose] public section

open scoped NumberField

namespace ClassFieldTheory

universe u

open _root_.GlobalClassFieldTheory.Reciprocity in
/-- The topological form of global class field theory. -/
theorem topologicalGlobalReciprocity
    (K : Type u) [Field K] [NumberField K] :
    Nonempty (IdeleClassConnectedQuotient K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K) :=
  ⟨mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K⟩

end ClassFieldTheory
