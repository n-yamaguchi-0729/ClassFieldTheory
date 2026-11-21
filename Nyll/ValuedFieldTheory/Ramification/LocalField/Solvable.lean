/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CharacterExact
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CompleteDVF
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteOrderValuation
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary

/-! # Solvability of the Galois group of a finite local extension -/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace RamificationTheory.LocalField

open LocalFieldTheory HilbertRamification.CompleteDVF HilbertRamification.ValuationSubring

/-- The actual Galois group of a finite local extension is solvable. Reduction
has cyclic target, and the inertia character has abelian target and a finite
residue-characteristic primary kernel. -/
theorem localGaloisGroup_isSolvable
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Group.IsSolvable Gal(L/K) := by
  let : NontriviallyNormedField L := finiteExtensionSpectralNormedField K L
  let : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
  let : IsNonarchimedeanLocalField L := finiteExtensionSpectralIsNonarchimedeanLocalField K L
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L) :=
    finiteExtensionSpectralValuation_hasExtension K L
  let base := localCompleteDVF K
  let target := localCompleteDVF L
  let A := target.valuation.valuationSubring
  let : base.valuation.HasExtension target.valuation := localCompleteDVFValuation_hasExtension K L
  let D := HilbertRamification.ValuationSubring.decompositionGroup K A
  let I := HilbertRamification.ValuationSubring.inertiaGroup K A
  let T := valueTrivialInertiaGroup K A
  let W := ramificationGroup K A
  let Q := ramificationGroupInValueTrivialInertiaGroup K A
  let : Finite target.residueField := by
    change Finite 𝓀[L]
    infer_instance
  let p := ringChar target.residueField
  let : Fact p.Prime := ⟨CharP.prime_ringChar target.residueField⟩
  let : CharP target.residueField p := ringChar.charP target.residueField
  let : Group.IsNilpotent ↥W := (ramificationGroup_isPGroup_of_residueChar K A p).isNilpotent
  let q : Q →* W :=
    { toFun := fun σ => ⟨σ.1.1, σ.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hq : Function.Injective q := by
    intro σ τ h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : W => (a : I)) h
  let : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective hq
  let χ := valueTrivialInertiaCharacterHom K A
  have hχ : χ.ker ≤ Q.subtype.range := by
    rw [← ramificationGroupInValueTrivialInertiaGroup_eq_characterHom_ker K A,
      Subgroup.range_subtype]
  let : Group.IsSolvable ((Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A →*
      (IsLocalRing.ResidueField A)ˣ) :=
    Group.isSolvable_of_comm (fun f g => MonoidHom.ext (fun a => mul_comm (f a) (g a)))
  let : Group.IsSolvable T := Group.isSolvable_of_ker_le_range Q.subtype χ hχ
  let e : T ≃* I :=
    (MulEquiv.subgroupCongr (valueTrivialInertiaGroup_eq_top_of_finite K A)).trans Subgroup.topEquiv
  let : Group.IsSolvable I := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : IsCyclic (target.residueField ≃ₐ[base.residueField] target.residueField) := by
    infer_instance
  let r := decompositionResidueAction (K := K) (base := base) (target := target)
  have hr : r.ker ≤ I.subtype.range := by
    have h : r.ker = I := decompositionResidueAction_ker (K := K) (base := base) (target := target)
    rw [h, Subgroup.range_subtype]
  let : Group.IsSolvable D := Group.isSolvable_of_ker_le_range I.subtype r hr
  let s : Gal(L/K) ≃* D := galEquivDecompositionGroup (base := base) (target := target)
  exact Group.isSolvable_of_isSolvable_injective (f := s.toMonoidHom) s.injective

end RamificationTheory.LocalField
