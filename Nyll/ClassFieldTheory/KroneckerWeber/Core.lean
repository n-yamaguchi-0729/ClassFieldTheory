/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
public import Nyll.ClassFieldTheory.KroneckerWeber.RationalCyclotomicArithmeticReciprocity
public import Nyll.ClassFieldTheory.KroneckerWeber.Final
public import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumCyclotomicTarget
public import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumGlobalEmbedding
public import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors
public import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumLocalizationEmbedding
public import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuationInertiaBound
public import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuedEmbedding
public import Nyll.ClassFieldTheory.KroneckerWeber.GlobalPadicPrimePowInertiaBound
public import Nyll.ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic
public import Nyll.ClassFieldTheory.KroneckerWeber.RayClassComparison
public import Nyll.ClassFieldTheory.KroneckerWeber.Setup
public import Nyll.ClassFieldTheory.KroneckerWeber.UnramifiedCompositumSupport

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

@[expose] public section

noncomputable section

universe u

namespace KroneckerWeber

/-- **Global Kronecker--Weber.**

Every finite abelian extension of `ℚ` embeds in `ℚ(ζₙ)` for some positive
integer `n`.  Here `CyclotomicField n ℚ` is the concrete model of
`ℚ(ζₙ)`. -/
theorem exists_cyclotomicEmbedding
    (L : Type u) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) := by
  let : Small.{0} L := ClassFieldTheory.numberField_small L
  let S := Shrink.{0} L
  let : NumberField S := ClassFieldTheory.numberField_shrink L
  let e : S ≃ₐ[ℚ] L := (Shrink.ringEquiv L).toRatAlgEquiv
  let : IsAbelianGalois ℚ S := IsAbelianGalois.of_algHom e.toAlgHom
  exact ⟨kroneckerWeberConductorCandidate (L := S),
    kroneckerWeberConductorCandidate_pos (L := S),
    ⟨(kroneckerWeberCyclotomicEmbedding (L := S)).comp e.symm.toAlgHom⟩⟩

end KroneckerWeber

end
