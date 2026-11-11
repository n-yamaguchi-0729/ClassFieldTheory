/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassPrimeToIdeals
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Ideal-theoretic ray class groups
-/



@[expose] public section

namespace ClassFieldTheory

universe u

/-- The ideal-theoretic ray class group of a modulus. -/
abbrev RayClassGroup
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) :=
  rayClassPrimeToIdeals m ⧸ rayPrincipalIdealSubgroupInPrimeTo m

/-- Ray class groups are multiplicatively commutative. -/
instance instIsMulCommutativeRayClassGroup
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) : IsMulCommutative (RayClassGroup m) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

end ClassFieldTheory
