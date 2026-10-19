/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormGalois

/-!
# The decomposition group on the actual completion

An automorphism fixing a place induces an automorphism of its completed field
over the actual base completion. The field embedding is dense, so multiplication
of completed automorphisms follows from multiplication on the original field.
Their action is faithful because the original field embeds in its completion.

This supplies the concrete decomposition-group action needed by local Hilbert 90.
No identification with the whole completed Galois group is assumed.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- The actual decomposition group is the stabilizer of the chosen place. -/
def decompositionGroup (w : Place k L) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | SemilinearAut.ofAlgAut (σ.restrictScalars k) • w = w}
  one_mem' := by
    change (1 : SemilinearAut k L) • w = w
    exact one_smul _ _
  mul_mem' := by
    intro σ τ hσ hτ
    change (SemilinearAut.ofAlgAut (σ.restrictScalars k) *
      SemilinearAut.ofAlgAut (τ.restrictScalars k)) • w = w
    rw [mul_smul, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    change (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w = w
    exact (inv_smul_eq_iff).2 hσ.symm

omit [FiniteDimensional K L] in
/-- Membership in the decomposition group states that the actual place is fixed. -/
theorem decompositionGroup_smul_eq (w : Place k L) (σ : decompositionGroup (K := K) w) :
    SemilinearAut.ofAlgAut (σ.1.restrictScalars k) • w = w :=
  σ.2

/-- The decomposition group is a finite subgroup of the finite global automorphism group. -/
instance decompositionGroupFintype (w : Place k L) :
    Fintype (decompositionGroup (K := K) w) :=
  Fintype.ofFinite _

private theorem continuous_completionCast {u w : Place k L} (h : u = w) :
    Continuous (RingEquiv.cast (R := fun v : Place k L => v.adicCompletion) h) := by
  subst w
  exact continuous_id

private theorem completionCast_algebraMap {u w : Place k L} (h : u = w) (x : L) :
    RingEquiv.cast (R := fun v : Place k L => v.adicCompletion) h
      (algebraMap L u.adicCompletion x) = algebraMap L w.adicCompletion x := by
  subst w
  rfl

private theorem completionCast_apply_section {u w : Place k L} (h : u = w)
    (a : ∀ z : Place k L, z.adicCompletion) :
    RingEquiv.cast (R := fun z : Place k L => z.adicCompletion) h (a u) = a w := by
  subst w
  rfl

private theorem completionCast_mem_integers_iff {u w : Place k L} (h : u = w)
    (x : u.adicCompletion) :
    RingEquiv.cast (R := fun z : Place k L => z.adicCompletion) h x ∈
        w.adicCompletionIntegers ↔ x ∈ u.adicCompletionIntegers := by
  subst w
  rfl

private theorem completionCast_completionMapOver {u w : Place k L} (h : u = w)
    (v : Place k K) (hu : u.restrict K = v) (hw : w.restrict K = v)
    (x : v.adicCompletion) :
    RingEquiv.cast (R := fun z : Place k L => z.adicCompletion) h
      (completionMapOver v u hu x) = completionMapOver v w hw x := by
  subst w
  rfl

/-- A place-fixing automorphism extends to the actual completed extension. -/
def decompositionCompletionAlgEquiv (w : Place k L) (σ : decompositionGroup (K := K) w) :
    w.adicCompletion ≃ₐ[(w.restrict K).adicCompletion] w.adicCompletion where
  __ := (placeCompletionRingEquiv
    (SemilinearAut.ofAlgAut (σ.1.restrictScalars k)) w).trans
      (RingEquiv.cast (R := fun z : Place k L => z.adicCompletion) (decompositionGroup_smul_eq w σ))
  commutes' x := by
    change RingEquiv.cast (R := fun z : Place k L => z.adicCompletion)
      (decompositionGroup_smul_eq w σ)
      (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.1.restrictScalars k)) w
        (completionMapOver (w.restrict K) w rfl x)) =
      completionMapOver (w.restrict K) w rfl x
    have h := DFunLike.congr_fun
      (completionMapOver_algAut σ.1 (w.restrict K) w rfl) x
    change placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.1.restrictScalars k)) w
        (completionMapOver (w.restrict K) w rfl x) =
      completionMapOver (w.restrict K)
        (SemilinearAut.ofAlgAut (σ.1.restrictScalars k) • w)
        ((Place.restrict_ofAlgAut_smul σ.1 w).trans rfl) x at h
    rw [h, completionCast_completionMapOver]

@[simp]
theorem decompositionCompletionAlgEquiv_algebraMap (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : L) :
    decompositionCompletionAlgEquiv w σ (algebraMap L w.adicCompletion x) =
      algebraMap L w.adicCompletion (σ.1 x) := by
  change RingEquiv.cast (R := fun z : Place k L => z.adicCompletion)
    (decompositionGroup_smul_eq w σ)
    (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.1.restrictScalars k)) w
      (algebraMap L w.adicCompletion x)) = _
  rw [placeCompletionRingEquiv_algebraMap, completionCast_algebraMap]
  rfl

/-- Completed decomposition automorphisms are continuous. -/
theorem continuous_decompositionCompletionAlgEquiv (w : Place k L)
    (σ : decompositionGroup (K := K) w) :
    Continuous (decompositionCompletionAlgEquiv w σ) :=
  (continuous_completionCast (decompositionGroup_smul_eq w σ)).comp
    (continuous_placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.1.restrictScalars k)) w)

/-- Completion is a homomorphism from the actual decomposition group. -/
def decompositionCompletionAut (w : Place k L) :
    decompositionGroup (K := K) w →*
      (w.adicCompletion ≃ₐ[(w.restrict K).adicCompletion] w.adicCompletion) where
  toFun := decompositionCompletionAlgEquiv w
  map_one' := by
    apply AlgEquiv.ext
    exact congrFun ((IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
      L w.heightOneSpectrum).equalizer
      (continuous_decompositionCompletionAlgEquiv w 1) continuous_id (by
        funext x
        exact decompositionCompletionAlgEquiv_algebraMap w 1 x))
  map_mul' σ τ := by
    apply AlgEquiv.ext
    exact congrFun ((IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
      L w.heightOneSpectrum).equalizer
      (continuous_decompositionCompletionAlgEquiv w (σ * τ))
      ((continuous_decompositionCompletionAlgEquiv w σ).comp
        (continuous_decompositionCompletionAlgEquiv w τ)) (by
          funext x
          simp only [Function.comp_apply, AlgEquiv.mul_apply, Subgroup.coe_mul,
            decompositionCompletionAlgEquiv_algebraMap]))

@[simp]
theorem decompositionCompletionAut_algebraMap (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : L) :
    decompositionCompletionAut (K := K) w σ (algebraMap L w.adicCompletion x) =
      algebraMap L w.adicCompletion (σ.1 x) :=
  decompositionCompletionAlgEquiv_algebraMap w σ x

/-- Completion does not identify distinct global decomposition automorphisms. -/
theorem decompositionCompletionAut_injective (w : Place k L) :
    Function.Injective (decompositionCompletionAut (K := K) w) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L w.adicCompletion).injective
  simpa only [decompositionCompletionAut_algebraMap] using
    congrArg (fun e : w.adicCompletion ≃ₐ[(w.restrict K).adicCompletion] w.adicCompletion =>
      e (algebraMap L w.adicCompletion x)) h

/-- The actual decomposition group acts on the multiplicative group of the completion. -/
instance decompositionCompletionUnitsAction (w : Place k L) :
    MulDistribMulAction (decompositionGroup (K := K) w) w.adicCompletionˣ :=
  MulDistribMulAction.compHom w.adicCompletionˣ (decompositionCompletionAut (K := K) w)

@[simp]
theorem decomposition_smul_units_coe (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.adicCompletionˣ) :
    ((σ • x : w.adicCompletionˣ) : w.adicCompletion) =
      decompositionCompletionAut (K := K) w σ (x : w.adicCompletion) :=
  rfl

/-- The actual integral valuation ring is invariant under the decomposition group. -/
theorem decompositionCompletionAut_mem_integers_iff (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.adicCompletion) :
    decompositionCompletionAut (K := K) w σ x ∈ w.adicCompletionIntegers ↔
      x ∈ w.adicCompletionIntegers := by
  change RingEquiv.cast (R := fun z : Place k L => z.adicCompletion)
    (decompositionGroup_smul_eq w σ)
      (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.1.restrictScalars k)) w x) ∈
        w.adicCompletionIntegers ↔ x ∈ w.adicCompletionIntegers
  rw [completionCast_mem_integers_iff, placeCompletionRingEquiv_mem_integers_iff]

/-- The decomposition action preserves the actual local integral-unit subgroup. -/
theorem decomposition_smul_mem_localUnits_iff (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.adicCompletionˣ) :
    σ • x ∈ w.adicCompletionIntegers.units ↔ x ∈ w.adicCompletionIntegers.units := by
  change (decompositionCompletionAut (K := K) w σ (x : w.adicCompletion) ∈
        w.adicCompletionIntegers ∧
      decompositionCompletionAut (K := K) w σ ((x⁻¹ : w.adicCompletionˣ) : w.adicCompletion) ∈
        w.adicCompletionIntegers) ↔
    ((x : w.adicCompletion) ∈ w.adicCompletionIntegers ∧
      ((x⁻¹ : w.adicCompletionˣ) : w.adicCompletion) ∈ w.adicCompletionIntegers)
  rw [decompositionCompletionAut_mem_integers_iff,
    decompositionCompletionAut_mem_integers_iff]

/-- Evaluation at the chosen place intertwines its decomposition action with
the actual action on all-place ideles. -/
theorem decomposition_smul_component (w : Place k L)
    (σ : decompositionGroup (K := K) w) (a : IdeleGroup k L) :
    component w (SemilinearAut.ofAlgAut (σ.1.restrictScalars k) • a) =
      σ • component w a := by
  apply Units.ext
  change (placeCompletionRingEquiv
      (SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ w).symm
        (a ((SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ • w) :
          ((SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ • w).adicCompletion) =
    decompositionCompletionAut (K := K) w σ (a w : w.adicCompletion)
  apply (decompositionCompletionAut (K := K) w (σ⁻¹)).injective
  calc
    decompositionCompletionAut (K := K) w (σ⁻¹)
        ((placeCompletionRingEquiv
          (SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ w).symm
          (a ((SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ • w))) =
        RingEquiv.cast (R := fun z : Place k L => z.adicCompletion)
          (decompositionGroup_smul_eq w (σ⁻¹))
          (a ((SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ • w) :
            ((SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ • w).adicCompletion) := by
      change RingEquiv.cast (R := fun z : Place k L => z.adicCompletion)
        (decompositionGroup_smul_eq w (σ⁻¹))
        (placeCompletionRingEquiv
          (SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ w
            ((placeCompletionRingEquiv
              (SemilinearAut.ofAlgAut (σ.1.restrictScalars k))⁻¹ w).symm _)) = _
      rw [RingEquiv.apply_symm_apply]
    _ = (a w : w.adicCompletion) :=
      completionCast_apply_section (decompositionGroup_smul_eq w (σ⁻¹))
        (fun z => (a z : z.adicCompletion))
    _ = decompositionCompletionAut (K := K) w (σ⁻¹)
        (decompositionCompletionAut (K := K) w σ (a w : w.adicCompletion)) := by
      rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl

end FunctionField.IdeleGroup
