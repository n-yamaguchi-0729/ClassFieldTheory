/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.Frobenius
import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry

/-!
# Actual Frobenius over a finite field

The existing section-algebra instances of a scheme over a field supply the
algebras used in Frobenius. Since every base-field element is fixed by its
cardinality power, this morphism is over the actual finite base.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (k : Type u) [Field k] [Fintype k]
    [X.Over (Spec (.of k))]

/-- The genuine finite-field Frobenius preserves the structure morphism. -/
theorem finiteFieldFrobenius_comp_over :
    X.finiteFieldFrobenius k ≫ (X ↘ Spec (.of k)) = X ↘ Spec (.of k) := by
  apply ext_of_isAffine
  rw [Hom.comp_appTop]
  apply CommRingCat.hom_ext
  ext a
  change ((X ↘ Spec (.of k)).appTop a) ^ Fintype.card k = (X ↘ Spec (.of k)).appTop a
  rw [← map_pow ((X ↘ Spec (.of k)).appTop).hom]
  congr 1
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  apply e.injective
  rw [map_pow, FiniteField.pow_card]

/-- Frobenius is an actual endomorphism over the finite field. -/
instance finiteFieldFrobenius_isOver : (X.finiteFieldFrobenius k).IsOver (Spec (.of k)) :=
  ⟨finiteFieldFrobenius_comp_over X k⟩

end AlgebraicGeometry.Scheme
