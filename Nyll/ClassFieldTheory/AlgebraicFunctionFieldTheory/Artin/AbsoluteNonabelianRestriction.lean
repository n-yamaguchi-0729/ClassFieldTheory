/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Absolute Artin restriction to arbitrary finite Galois abelianizations

The original restriction to a finite Galois field, followed by its
abelianization, kills the closed absolute commutator. It therefore descends
to the actual absolute abelian Galois group.

The kernel of that original map cuts out an actual finite abelian field.
Its Galois group is canonically the finite Galois abelianization. Restriction
of native finite Artin symbols to this field proves the absolute evaluation
formula even when the original finite Galois group is nonabelian.
-/

@[expose] public section

universe u v

noncomputable section

namespace FunctionField

open LocalClassFieldTheory
open scoped IsMulCommutative

section Restriction

variable (K : Type v) [Field K]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E]

/-- Finite Galois restriction followed by abelianization has an open and closed kernel. -/
theorem restrictionAbelianization_ker_closed_open :
    let q : Gal(SeparableClosure K/K) →* Abelianization Gal(E/K) :=
      Abelianization.of.comp (AlgEquiv.restrictNormalHom E)
    IsClosed (q.ker : Set Gal(SeparableClosure K/K)) ∧
      IsOpen (q.ker : Set Gal(SeparableClosure K/K)) := by
  intro q
  let r : Gal(SeparableClosure K/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hker : (q.ker : Set Gal(SeparableClosure K/K)) =
      r ⁻¹' (commutator Gal(E/K) : Set Gal(E/K)) := by
    ext σ
    change Abelianization.of (r σ) = 1 ↔ r σ ∈ commutator Gal(E/K)
    exact QuotientGroup.eq_one_iff (N := commutator Gal(E/K)) (r σ)
  rw [hker]
  exact ⟨(isClosed_discrete _).preimage (InfiniteGalois.restrictNormalHom_continuous E),
    (isOpen_discrete _).preimage (InfiniteGalois.restrictNormalHom_continuous E)⟩

/-- Actual finite Galois restriction, descended after abelianization. -/
def absoluteAbelianizedRestriction :
    localAbsoluteAbelianProfinite K →* Abelianization Gal(E/K) := by
  let q : Gal(SeparableClosure K/K) →* Abelianization Gal(E/K) :=
    Abelianization.of.comp (AlgEquiv.restrictNormalHom E)
  have hcomm : commutator Gal(SeparableClosure K/K) ≤ q.ker :=
    Abelianization.commutator_subset_ker q
  have hclosed : IsClosed (q.ker : Set Gal(SeparableClosure K/K)) :=
    (restrictionAbelianization_ker_closed_open K E).1
  have hclosure : (commutator Gal(SeparableClosure K/K)).topologicalClosure ≤ q.ker :=
    (commutator Gal(SeparableClosure K/K)).topologicalClosure_minimal hcomm hclosed
  exact QuotientGroup.lift (commutator Gal(SeparableClosure K/K)).topologicalClosure q
    (fun σ hσ => MonoidHom.mem_ker.mp (hclosure hσ))

/-- On an absolute automorphism, the map is literal finite restriction
followed by the ordinary abelianization quotient. -/
theorem absoluteAbelianizedRestriction_mk (σ : Gal(SeparableClosure K/K)) :
    absoluteAbelianizedRestriction K E
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) =
      Abelianization.of (AlgEquiv.restrictNormalHom E σ) := rfl

private theorem absoluteAbelianizedRestriction_factor
    (M : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K M] [IsAbelianGalois K M]
    (e : Abelianization Gal(E/K) ≃* Gal(M/K))
    (he : ∀ σ : Gal(SeparableClosure K/K),
      e (Abelianization.of (AlgEquiv.restrictNormalHom E σ)) =
        AlgEquiv.restrictNormalHom M σ) :
    e.toMonoidHom.comp (absoluteAbelianizedRestriction K E) =
      (absoluteAbelianRestriction K M).toMonoidHom := by
  apply QuotientGroup.monoidHom_ext
    (commutator (intrinsicAbsoluteGalois K)).topologicalClosure
  apply MonoidHom.ext
  intro σ
  exact ((congrArg e (absoluteAbelianizedRestriction_mk K E σ)).trans
    (he σ)).trans (absoluteAbelianRestriction_mk K M σ).symm

end Restriction

section Artin

variable (k : Type u) (K : Type v) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]

private theorem absoluteArtin_abelianizedRestriction_of_factor
    (E M : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K M] [IsAbelianGalois K M]
    [Algebra M E] [IsScalarTower K M E] [IsScalarTower M E (SeparableClosure K)]
    (e : Abelianization Gal(E/K) ≃* Gal(M/K))
    (he : ∀ σ : Gal(SeparableClosure K/K),
      e (Abelianization.of (AlgEquiv.restrictNormalHom E σ)) =
        AlgEquiv.restrictNormalHom M σ)
    (c : IdeleClassGroup k K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    absoluteAbelianizedRestriction K E (absoluteArtin k K c) = finiteArtin k K E c := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  let r : Gal(SeparableClosure K/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  let rEM : Gal(E/K) →* Gal(M/K) :=
    AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M
  have hrestrict (σ : Gal(SeparableClosure K/K)) :
      rEM (r σ) = AlgEquiv.restrictNormalHom M σ := by
    exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply M E σ).symm
  have heFinite (z : Abelianization Gal(E/K)) :
      Abelianization.of (e z) = Abelianization.map rEM z := by
    obtain ⟨τ, rfl⟩ := (show Function.Surjective
      (Abelianization.of : Gal(E/K) →* Abelianization Gal(E/K)) from
        QuotientGroup.mk_surjective) z
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := SeparableClosure K) τ
    change Abelianization.of (e (Abelianization.of (r σ))) =
      Abelianization.of (rEM (r σ))
    exact congrArg Abelianization.of ((he σ).trans (hrestrict σ).symm)
  have heAbsoluteHom := absoluteAbelianizedRestriction_factor K E M e he
  have heAbsolute (x : localAbsoluteAbelianProfinite K) :
      e (absoluteAbelianizedRestriction K E x) = absoluteAbelianRestriction K M x :=
    DFunLike.congr_fun heAbsoluteHom x
  have heArtin : e (finiteArtin k K E c) = abelianFiniteArtin k K M c := by
    apply (Abelianization.equivOfComm (H := Gal(M/K))).injective
    change Abelianization.of (e (finiteArtin k K E c)) =
      Abelianization.of (abelianFiniteArtin k K M c)
    rw [heFinite, abelianFiniteArtin_of]
    exact finiteArtin_restrictNormal k K M E c
  apply e.injective
  exact (heAbsolute (absoluteArtin k K c)).trans
    ((absoluteArtin_restriction k K M c).trans heArtin.symm)

/-- Every actual finite Galois projection of absolute reciprocity is the
native finite Artin symbol, with values in the finite Galois abelianization. -/
theorem absoluteArtin_abelianizedRestriction
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] (c : IdeleClassGroup k K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    absoluteAbelianizedRestriction K E (absoluteArtin k K c) = finiteArtin k K E c := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  let r : Gal(SeparableClosure K/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  let q : Gal(SeparableClosure K/K) →* Abelianization Gal(E/K) := Abelianization.of.comp r
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨τ, rfl⟩ := (show Function.Surjective
      (Abelianization.of : Gal(E/K) →* Abelianization Gal(E/K)) from
        QuotientGroup.mk_surjective) z
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := SeparableClosure K) τ
    exact ⟨σ, congrArg Abelianization.of hσ⟩
  have hker := restrictionAbelianization_ker_closed_open K E
  let S : ClosedSubgroup Gal(SeparableClosure K/K) :=
    { toSubgroup := q.ker
      isClosed' := hker.1 }
  have hSnormal : S.toSubgroup.Normal := by
    change q.ker.Normal
    infer_instance
  let M : IntermediateField K (SeparableClosure K) := IntermediateField.fixedField S.toSubgroup
  have hMfinite : FiniteDimensional K M := by
    apply (InfiniteGalois.isOpen_iff_finite (K := SeparableClosure K) M).mp
    change IsOpen ((IntermediateField.fixedField S.toSubgroup).fixingSubgroup :
      Set Gal(SeparableClosure K/K))
    rw [InfiniteGalois.fixingSubgroup_fixedField S]
    exact hker.2
  have hMgal : IsGalois K M := IsGalois.of_fixedField_normal_subgroup S.toSubgroup
  let eQ : (Gal(SeparableClosure K/K) ⧸ q.ker) ≃* Abelianization Gal(E/K) :=
    QuotientGroup.quotientKerEquivOfSurjective q hq
  let eG : (Gal(SeparableClosure K/K) ⧸ S.toSubgroup) ≃* Gal(M/K) :=
    InfiniteGalois.normalAutEquivQuotient S
  let e : Abelianization Gal(E/K) ≃* Gal(M/K) := eQ.symm.trans eG
  have he (σ : Gal(SeparableClosure K/K)) :
      e (q σ) = AlgEquiv.restrictNormalHom M σ := by
    change eG (eQ.symm (q σ)) = _
    have hrepresentative : q σ = eQ (QuotientGroup.mk σ) := rfl
    rw [hrepresentative, eQ.symm_apply_apply]
    exact InfiniteGalois.normalAutEquivQuotient_apply S σ
  have hMcomm : IsMulCommutative Gal(M/K) :=
    ⟨⟨fun σ τ => e.symm.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hMabelian : IsAbelianGalois K M :=
    { toIsGalois := hMgal
      toIsMulCommutative := hMcomm }
  have hfix : E.fixingSubgroup ≤ S.toSubgroup := by
    intro σ hσ
    have hr : σ ∈ r.ker := by
      change σ ∈ (AlgEquiv.restrictNormalHom E).ker
      rw [IntermediateField.restrictNormalHom_ker]
      exact hσ
    change Abelianization.of (r σ) = 1
    rw [MonoidHom.mem_ker.mp hr, map_one]
  have hME : M ≤ E :=
    (IntermediateField.fixedField_le hfix).trans
      (InfiniteGalois.fixedField_fixingSubgroup E).le
  let aME : Algebra M E := (IntermediateField.inclusion hME).toRingHom.toAlgebra
  have hKME : IsScalarTower K M E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hMEΩ : IsScalarTower M E (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact absoluteArtin_abelianizedRestriction_of_factor k K E M e he c

end Artin

end FunctionField
