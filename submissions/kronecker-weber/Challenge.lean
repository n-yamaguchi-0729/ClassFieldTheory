import Mathlib.NumberTheory.Cyclotomic.Basic

set_option autoImplicit false

/-!
# The global Kronecker--Weber theorem

Every finite abelian extension of the rational numbers admits a rational
algebra embedding into a cyclotomic field of some positive order.

All notions in this statement are defined in the pinned Mathlib.
NumberField L means characteristic zero and finite dimension over the rationals.
IsAbelianGalois combines the Galois property and commutativity of the automorphism
group. CyclotomicField n Q is the splitting field of the nth cyclotomic polynomial.
An algebra homomorphism between fields is injective, so this is an embedding.

The deliberate proof hole below belongs only to the statement reviewed by
Comparator. The Solution module imports the already proved declaration with
the exact same name and type from the substantive development.
-/

namespace KroneckerWeber

/-- Every number field that is abelian Galois over the rationals embeds in a
cyclotomic field of positive order. -/
theorem exists_cyclotomicEmbedding
    (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) := by
  sorry

end KroneckerWeber
