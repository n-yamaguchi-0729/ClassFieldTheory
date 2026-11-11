/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteLimits
public import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
public import Mathlib.CategoryTheory.Extensive

/-!
# Disjoint finite coproducts of finite etale schemes

Extensivity is inherited from schemes through the actual forgetful functor,
which preserves pullbacks and finite coproducts and reflects isomorphisms.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

/-- Finite etale schemes over a base form a finitary extensive category. -/
instance finitaryExtensive (X : Scheme) : FinitaryExtensive (FiniteEtale X) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism
    (FiniteEtale.forget X ⋙ Over.forget X)

end AlgebraicGeometry.FiniteEtale
