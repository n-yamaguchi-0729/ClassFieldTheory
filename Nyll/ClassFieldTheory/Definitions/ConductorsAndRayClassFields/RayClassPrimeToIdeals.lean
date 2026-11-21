/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup
public import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization

/-!
# Fractional ideals prime to a ray modulus
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- The subgroup of nonzero fractional ideals prime to the finite part of a
ray modulus. -/
def rayClassPrimeToIdeals
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) :
    Subgroup (NumberFieldFractionalIdealGroup K) :=
  FractionalIdealFactorization.primeTo (F := K) m.finitePart.support

end ClassFieldTheory
