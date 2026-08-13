import ValuationTheory.AbsoluteValue.AlgebraicLocalization
import AlgebraicNumberTheory.CompositumEmbedding
import KroneckerWeber.GlobalCompositumCyclotomicTarget
import RamificationTheory.HilbertRamification.PadicLocalizationCanonicalValuation

/-!
# The left-factor ring embedding for the global compositum

The chosen localization remains internal to the proof.  The
public statement mentions only a ring embedding from `L` to the common
local cyclotomic target, so elaborating its type never unfolds completion
or transported-algebra instances.  Rational linearity is added separately
in the global-factor file by `map_ratCast`.
-/

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory
open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- A ring embedding of `L` into the common local cyclotomic target which
pulls the canonical target absolute value back to the chosen `p`-adic place.
Its factorization through the chosen localization is retained in the proof,
without exposing that expensive localization type in this declaration. -/
noncomputable def kroneckerWeberGlobalLeftRingEmbeddingProperty
    (p : Nat.Primes) : Prop := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let N := kroneckerWeberLocalCompositumOrder (L := L) p
  have hN : 0 < N := kroneckerWeberLocalCompositumOrder_pos (L := L) p
  letI : NeZero N := ⟨hN.ne'⟩
  let T := CyclotomicField N ℚ_[p.1]
  letI : FiniteDimensional ℚ_[p.1] T :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ_[p.1] T
  let w := kroneckerWeberPadicExtension (L := L) p.1
  exact ∃ i : L →+* T, ∀ x : L,
    padicFiniteExtensionAbsoluteValue p.1 T (i x) = w.1 x

/-- The global field admits a ring embedding into the common local target
which preserves the chosen `p`-adic place. -/
theorem kroneckerWeberGlobalLeftRingEmbedding
    (p : Nat.Primes) :
    kroneckerWeberGlobalLeftRingEmbeddingProperty (L := L) p := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let w := kroneckerWeberPadicExtension (L := L) p.1
  let vK := Rat.AbsoluteValue.padic p.1
  letI hKvField : Field vK.Completion := inferInstance
  letI hwField : Field w.1.Completion := inferInstance
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  letI : SMul ℚ w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  letI hE : Field E := inferInstance
  letI hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionAlgEquiv p.1
  letI hQpE : Algebra ℚ_[p.1] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p.1] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e.toRingEquiv
  letI : Module.Finite vK.Completion E :=
    globalPadicLocalizationModuleFinite p.1 L w
  letI : Algebra ℚ_[p.1] vK.Completion := e.symm.toAlgHom.toAlgebra
  letI : IsScalarTower ℚ_[p.1] vK.Completion E :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  letI : Module.Finite ℚ_[p.1] vK.Completion :=
    FiniteDimensional.of_surjective
      (Algebra.linearMap ℚ_[p.1] vK.Completion) e.symm.surjective
  letI : Module.Finite ℚ_[p.1] E := Module.Finite.trans vK.Completion E
  let u :=
    (p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p - 1) *
      p.1 ^ kroneckerWeberLocalRamificationExponent (L := L) p
  let N := kroneckerWeberLocalCompositumOrder (L := L) p
  have hu : 0 < u := by
    apply Nat.mul_pos
    · exact Nat.sub_pos_of_lt
        (one_lt_pow₀ p.2.one_lt
          (kroneckerWeberLocalUnramifiedDegree_pos (L := L) p).ne')
    · exact pow_pos p.2.pos _
  have hN : 0 < N :=
    kroneckerWeberLocalCompositumOrder_pos (L := L) p
  letI : NeZero N := ⟨hN.ne'⟩
  letI : FiniteDimensional ℚ_[p.1] (CyclotomicField N ℚ_[p.1]) :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ_[p.1]
      (CyclotomicField N ℚ_[p.1])
  have hi := kroneckerWeberLocalCyclotomicEmbedding (L := L) p
  change Nonempty (E →ₐ[ℚ_[p.1]] CyclotomicField u ℚ_[p.1]) at hi
  obtain ⟨i⟩ := hi
  let iup : CyclotomicField u ℚ_[p.1] →ₐ[ℚ_[p.1]]
      CyclotomicField N ℚ_[p.1] :=
    cyclotomicFieldEmbeddingOfDvd ℚ_[p.1] u N hu hN
      (kroneckerWeberLocalStructuredOrder_dvd_compositumOrder
        (L := L) p)
  let ilocal : E →ₐ[ℚ_[p.1]] CyclotomicField N ℚ_[p.1] :=
    iup.comp i
  let iGlobal : L →+* CyclotomicField N ℚ_[p.1] :=
    ilocal.toRingHom.comp (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2)
  have hAbsolute := globalPadicLocalizationAbsoluteValue_eq_canonical p.1 L w
  change AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 =
    padicFiniteExtensionAbsoluteValue p.1 E at hAbsolute
  refine ⟨iGlobal, ?_⟩
  intro x
  change padicFiniteExtensionAbsoluteValue p.1
      (CyclotomicField N ℚ_[p.1])
        (ilocal (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)) = w.1 x
  calc
    padicFiniteExtensionAbsoluteValue p.1
        (CyclotomicField N ℚ_[p.1])
          (ilocal (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)) =
        padicFiniteExtensionAbsoluteValue p.1 E
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) :=
      padicFiniteExtensionAbsoluteValue_algHom p.1 ilocal _
    _ = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) := by
      rw [hAbsolute]
    _ = w.1 x :=
      AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 x

end KroneckerWeber

end
