import KroneckerWeber.LocalCyclotomicEmbedding
import KroneckerWeber.RationalCyclotomicArithmeticReciprocity
import KroneckerWeber.Final
import KroneckerWeber.GlobalCompositumCyclotomicTarget
import KroneckerWeber.GlobalCompositumGlobalEmbedding
import KroneckerWeber.GlobalCompositumLeftFactors
import KroneckerWeber.GlobalCompositumLocalizationEmbedding
import KroneckerWeber.GlobalCompositumValuationInertiaBound
import KroneckerWeber.GlobalCompositumValuedEmbedding
import KroneckerWeber.GlobalPadicPrimePowInertiaBound
import KroneckerWeber.RationalRayClassFieldCyclotomic
import KroneckerWeber.RayClassComparison
import KroneckerWeber.Setup
import KroneckerWeber.UnramifiedCompositumSupport

/-!
# Kronecker--Weber

The reader-facing entry point for the local and global Kronecker--Weber
theorems.  Importing this module exposes both supported endpoints.
-/

/-!
# The global Kronecker--Weber theorem

Every finite abelian extension of `ℚ` is contained in a cyclotomic field.
The arithmetic construction and global degree estimate are kept in the
semantic support modules under `KroneckerWeber.Global`; this root exposes the
canonical theorem statement.
-/

noncomputable section

namespace KroneckerWeber

/-- **Global Kronecker--Weber.**

Every finite abelian extension of `ℚ` embeds in `ℚ(ζₙ)` for some positive
integer `n`.  Here `CyclotomicField n ℚ` is the concrete model of
`ℚ(ζₙ)`. -/
theorem exists_cyclotomicEmbedding
    (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  ⟨kroneckerWeberConductorCandidate (L := L),
    kroneckerWeberConductorCandidate_pos (L := L),
    ⟨kroneckerWeberCyclotomicEmbedding (L := L)⟩⟩

end KroneckerWeber

end
