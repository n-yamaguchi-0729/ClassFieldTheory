/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.KroneckerWeber.Core

/-!
# Kronecker--Weber theorem

Let `L` be a number field that is finite abelian over `ℚ`.  Kronecker--Weber
asserts that `L` is contained in a cyclotomic extension: there is a positive
integer `n` and a `ℚ`-algebra embedding of `L` into `ℚ(ζₙ)`.  The positivity
condition excludes the degenerate order-zero cyclotomic construction.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- **Kronecker--Weber.** Every finite abelian extension of `ℚ` embeds in a
cyclotomic field of positive order. -/
theorem kroneckerWeber
    (L : Type u) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  KroneckerWeber.exists_cyclotomicEmbedding L

end ClassFieldTheory
