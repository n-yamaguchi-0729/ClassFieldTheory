import ValuationTheory.AbsoluteValue.AlgebraicLocalization
import KroneckerWeber.GlobalCompositumValuedEmbedding

/-!
# Embedding the localized global compositum in the common cyclotomic target

The synchronized global embedding is an isometry for the pulled-back place.
It therefore extends to completions.  Compatibility on the completed base
identifies the restriction to the chosen localization as a genuine
`ℚ_p`-algebra embedding into the same common cyclotomic target.
-/

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The actual embedding type, named one layer before taking `Nonempty` so
later theorem declarations do not normalize the localization construction. -/
noncomputable def kroneckerWeberGlobalCompositumLocalizationAlgHom
    (p : Nat.Primes) [Fact p.1.Prime]
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) : Type := by
  let M := kroneckerWeberCompositumField L
  let wM :=
    kroneckerWeberGlobalCompositumCyclotomicPadicExtension (L := L) p hp
  let N := kroneckerWeberLocalCompositumOrder (L := L) p
  exact globalPadicLocalizationCyclotomicAlgHom p.1 M wM N

/-- The localized global compositum embeds into the common local cyclotomic
target at every ramified prime. -/
theorem kroneckerWeberGlobalCompositumLocalizationEmbedding
    (p : Nat.Primes) [Fact p.1.Prime]
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) :
    Nonempty
      (kroneckerWeberGlobalCompositumLocalizationAlgHom
        (L := L) p hp) := by
  let M := kroneckerWeberCompositumField L
  let N := kroneckerWeberLocalCompositumOrder (L := L) p
  have hN : 0 < N := kroneckerWeberLocalCompositumOrder_pos (L := L) p
  letI : NeZero N := ⟨hN.ne'⟩
  let T := CyclotomicField N ℚ_[p.1]
  letI hTField : Field T := inferInstance
  letI : FiniteDimensional ℚ_[p.1] T :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ_[p.1] T
  let W :=
    kroneckerWeberGlobalValuedCompositumEmbeddingData (L := L) p hp
  let wM :=
    kroneckerWeberGlobalCompositumCyclotomicPadicExtension (L := L) p hp
  let vK := Rat.AbsoluteValue.padic p.1
  let aT := padicFiniteExtensionAbsoluteValue p.1 T
  have hW : ∀ x : M, aT (W.embedding x) = wM.1 x := by
    intro x
    rfl
  letI : CompleteSpace (WithAbs aT) :=
    completeSpace_withAbs_of_isCompleteForAbsoluteValue aT
      (padicFiniteExtensionAbsoluteValue_complete p.1 T)
  let F : wM.1.Completion →+* WithAbs aT :=
    AbsoluteValue.completionMapToCompleteTarget
      wM.1 aT W.embedding.toRingHom hW

  letI hKvField : Field vK.Completion := inferInstance
  letI hwMField : Field wM.1.Completion := inferInstance
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) wM.1
  letI : SMul ℚ wM.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK wM.1 wM.2
  let E := AbsoluteValue.algebraicLocalization vK wM.1 wM.2
  letI hE : Field E := inferInstance
  letI hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionAlgEquiv p.1
  letI hQpE : Algebra ℚ_[p.1] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p.1] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e.toRingEquiv

  let g : vK.Completion →+* WithAbs aT :=
    (WithAbs.equiv aT).symm.toRingHom.comp
      ((algebraMap ℚ_[p.1] T).comp e.toRingEquiv.toRingHom)
  have hgNorm (x : vK.Completion) : ‖g x‖ = ‖x‖ := by
    change aT (algebraMap ℚ_[p.1] T (e x)) = ‖x‖
    rw [padicFiniteExtensionAbsoluteValue_extends]
    change ‖padicAbsoluteValueCompletionRingHom p.1 x‖ = ‖x‖
    exact
      (padicAbsoluteValueCompletionRingHom_isometry p.1).norm_map_of_map_zero
        (map_zero (padicAbsoluteValueCompletionRingHom p.1)) x
  have hg : Isometry g :=
    AddMonoidHomClass.isometry_of_norm g hgNorm

  have hbase (x : vK.Completion) :
      F (AbsoluteValue.completionMap vK wM.1 wM.2 x) = g x := by
    have hcomp :
        F.comp (AbsoluteValue.completionMap vK wM.1 wM.2) = g := by
      change
        (AbsoluteValue.completionMapToCompleteTarget
          wM.1 aT W.embedding.toRingHom hW).comp
            (AbsoluteValue.completionMap vK wM.1 wM.2) = g
      apply
        AbsoluteValue.completionMapToCompleteTarget_comp_completionMap_eq_of_coe_eq
          vK wM.1 wM.2 aT W.embedding.toRingHom hW g hg.continuous
      intro q
      dsimp only [g, RingHom.comp_apply]
      apply congrArg (WithAbs.equiv aT).symm
      change W.embedding (algebraMap ℚ M q) =
        algebraMap ℚ_[p.1] T
          (e (((WithAbs.equiv vK).symm q : WithAbs vK) :
            vK.Completion))
      rw [W.embedding.commutes,
        padicAbsoluteValueCompletionAlgEquiv_coe]
      rfl
    exact DFunLike.congr_fun hcomp x

  let iRing : E →+* T :=
    (WithAbs.equiv aT).toRingHom.comp
      (F.comp E.val.toRingHom)
  change Nonempty (E →ₐ[ℚ_[p.1]] T)
  refine ⟨
    { __ := iRing
      commutes' := ?_ }⟩
  intro q
  change (WithAbs.equiv aT)
      (F (AbsoluteValue.completionMap vK wM.1 wM.2 (e.symm q))) =
    algebraMap ℚ_[p.1] T q
  rw [hbase]
  change algebraMap ℚ_[p.1] T (e (e.symm q)) =
    algebraMap ℚ_[p.1] T q
  rw [e.apply_symm_apply]

end KroneckerWeber

end
