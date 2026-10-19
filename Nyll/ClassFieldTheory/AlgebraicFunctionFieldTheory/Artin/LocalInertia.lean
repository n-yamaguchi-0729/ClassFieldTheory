/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalRamification
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.ConstantResidueComparison
import Nyll.ValuedFieldTheory.Ramification.LocalField.ResidueInertia
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois

/-!
# Local unit images and the actual residue inertia

The existing completed filtration is transported to the kernel of the
decomposition group's action on the original residue field.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place ValuativeRel

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [FunctionField k L] in
/-- Completing a decomposition automorphism preserves exactly the kernel of
its actual residue action. -/
theorem decompositionCompletion_mem_residue_ker_iff
    (w : Place k L) (σ : IdeleGroup.decompositionGroup (K := K) w) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    let _ : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
    let _ : (ValuativeRel.valuation (w.restrict K).adicCompletion).HasExtension
        (ValuativeRel.valuation w.adicCompletion) :=
      IdeleGroup.completionCanonical_hasExtension (K := K) w
    let _ : IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
        w.adicCompletion := IdeleGroup.completionCanonical_isIntegralClosure (K := K) w
    IdeleGroup.decompositionCompletionEquiv (K := K) w σ ∈
      (LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure
        (w.restrict K).adicCompletion w.adicCompletion).ker ↔
      σ ∈ (IdeleGroup.decompositionResidueAut (K := K) w).ker := by
  intro hbase htarget hext hclosure
  let eO : 𝒪[w.adicCompletion] ≃+* w.adicCompletionIntegers :=
    RingEquiv.subringCongr (IdeleGroup.completionInteger_eq w)
  let eR := IsLocalRing.ResidueField.mapEquiv eO
  let e0 : w.ResidueField ≃+* IsLocalRing.ResidueField w.adicCompletionIntegers :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      L w.heightOneSpectrum
  let τ := IdeleGroup.decompositionCompletionEquiv (K := K) w σ
  let ρ := LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure
    (w.restrict K).adicCompletion w.adicCompletion τ
  let ψ := IsLocalRing.ResidueField.mapEquiv
    (IdeleGroup.decompositionCompletionIntegerEquiv w σ)
  have hinteger (a : 𝒪[w.adicCompletion]) :
      eO (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
        (w.restrict K).adicCompletion w.adicCompletion τ a) =
      IdeleGroup.decompositionCompletionIntegerEquiv w σ (eO a) := by
    apply Subtype.ext
    change (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
      (w.restrict K).adicCompletion w.adicCompletion τ a : w.adicCompletion) =
      IdeleGroup.decompositionCompletionAut (K := K) w σ (a : w.adicCompletion)
    rw [LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
    rfl
  have hcomm (z : 𝓀[w.adicCompletion]) : eR (ρ z) = ψ (eR z) := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    change IsLocalRing.ResidueField.mapEquiv eO
      (IsLocalRing.residue _ (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
        (w.restrict K).adicCompletion w.adicCompletion τ a)) =
      IsLocalRing.ResidueField.mapEquiv
        (IdeleGroup.decompositionCompletionIntegerEquiv w σ)
        (IsLocalRing.ResidueField.mapEquiv eO (IsLocalRing.residue _ a))
    simp only [IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue w.adicCompletionIntegers) (hinteger a)
  have hbefore (y : w.ResidueField) :
      ψ (e0 y) = e0 (IdeleGroup.decompositionResidueAut (K := K) w σ y) :=
    IdeleGroup.decompositionCompletion_residue_comparison w σ y
  change ρ = 1 ↔ IdeleGroup.decompositionResidueAut (K := K) w σ = 1
  constructor
  · intro h
    apply AlgEquiv.ext
    intro y
    apply e0.injective
    rw [← hbefore]
    obtain ⟨z, hz⟩ := eR.surjective (e0 y)
    rw [← hz, ← hcomm, h]
    exact hz
  · intro h
    apply AlgEquiv.ext
    intro z
    apply eR.injective
    rw [hcomm]
    obtain ⟨y, hy⟩ := e0.surjective (eR z)
    rw [← hy, hbefore, h]
    exact hy

/-- The local units have image exactly the actual inertia kernel on the
original residue field. -/
theorem localDecompositionArtin_units_eq_residue_ker (w : Place k L) :
    (RayClass.localHigherUnitGroup (w.restrict K) 0).map
      (localDecompositionArtin (K := K) w).toMonoidHom =
      (IdeleGroup.decompositionResidueAut (K := K) w).ker := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  let : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  have : IsNonarchimedeanLocalField w.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField w
  have := IdeleGroup.completionCanonical_hasExtension (K := K) w
  have : IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
      w.adicCompletion := IdeleGroup.completionCanonical_isIntegralClosure (K := K) w
  have : IsNoetherian 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
    IsIntegralClosure.isNoetherian 𝒪[(w.restrict K).adicCompletion]
      (w.restrict K).adicCompletion w.adicCompletion 𝒪[w.adicCompletion]
  have : Module.Finite 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
    Module.IsNoetherian.finite _ _
  have hmap := localDecompositionArtin_higherUnits_completion (K := K) w 0
  dsimp only at hmap
  rw [Nat.cast_zero] at hmap
  rw [RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker]
    at hmap
  apply Subgroup.ext
  intro σ
  have hker := decompositionCompletion_mem_residue_ker_iff (K := K) w σ
  dsimp only at hker
  rw [← hker, ← hmap]
  exact (Subgroup.mem_map_iff_mem
    (IdeleGroup.decompositionCompletionEquiv (K := K) w).injective).symm

/-- In the global Galois group, local units have image the included inertia kernel. -/
theorem localArtin_units_eq_residue_ker_map (w : Place k L) :
    (RayClass.localHigherUnitGroup (w.restrict K) 0).map
      (localArtin (K := K) w) =
      (IdeleGroup.decompositionResidueAut (K := K) w).ker.map
        (IdeleGroup.decompositionGroup (K := K) w).subtype := by
  rw [localArtin, ← Subgroup.map_map, localDecompositionArtin_units_eq_residue_ker]

end FunctionField
