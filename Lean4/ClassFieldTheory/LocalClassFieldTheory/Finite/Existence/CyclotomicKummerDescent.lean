import Mathlib.NumberTheory.Cyclotomic.Basic
import LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
import LocalClassFieldTheory.Finite.Existence.MaximalKummerNorm
import LocalFieldTheory.NonarchimedeanLocalField.NormSubgroupFunctoriality

/-!
# Cyclotomic descent for maximal Kummer norm subgroups

For an exponent nonzero in the base field, adjoining the roots of unity,
applying maximal Kummer theory, and descending the norm inclusion produces a
finite Galois extension whose norm subgroup is contained in `Kˣⁿ`.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal ValuativeRel
open CyclicCohomology KummerTheory ClassFormation
open LocalFieldTheory.DiscreteValuationField LocalFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- There is a finite Galois extension whose local norm subgroup is contained
in the `n`-th-power subgroup, without assuming roots of unity in the base. -/
theorem exists_finiteGalois_normSubgroup_le_powMonoidHom_range
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      localNormSubgroup K (E : IntermediateField K (SeparableClosure K)) ≤
        (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  letI : NeZero ((n : ℕ) : K) := ⟨hnK⟩
  let C := CyclotomicField (n : ℕ) K
  letI : FiniteDimensional K C :=
    IsCyclotomicExtension.finiteDimensional {(n : ℕ)} K C
  letI : IsGalois K C :=
    IsCyclotomicExtension.isGalois {(n : ℕ)} K C
  obtain ⟨zeta, hzeta⟩ :=
    (CyclotomicField.isCyclotomicExtension (n : ℕ) K).exists_isPrimitiveRoot
      (Set.mem_singleton (n : ℕ)) n.ne_zero

  let j : C →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let K1 := AlgHom.fieldRange j
  let eC : C ≃ₐ[K] K1 := AlgEquiv.ofInjectiveField j
  letI : FiniteDimensional K K1 := eC.toLinearEquiv.finiteDimensional
  letI : IsGalois K K1 := IsGalois.of_algEquiv eC
  have hnK1 : ((n : ℕ) : K1) ≠ 0 := by
    intro h
    apply hnK
    apply (algebraMap K K1).injective
    simpa using h
  have hmu1 : (primitiveRoots (n : ℕ) K1).Nonempty :=
    ⟨eC zeta, (mem_primitiveRoots n.pos).2
      (hzeta.map_of_injective eC.injective)⟩

  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : Valued K (ValuativeRel.ValueGroupWithZero K) := inferInstance
  letI : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)
  letI : CompleteSpace K := inferInstance

  letI : NontriviallyNormedField K1 :=
    spectralNorm.nontriviallyNormedField K K1
  letI : NormedSpace K K1 := spectralNorm.normedSpace K K1
  letI : NormedAlgebra K K1 :=
    { (inferInstance : Algebra K K1) with
      norm_smul_le := NormedSpace.norm_smul_le }
  letI : CompleteSpace K1 := spectralNorm.completeSpace K K1
  letI : LocallyCompactSpace K1 :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K K1
  letI : IsUltrametricDist K1 :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := K1) (x - y) (y - z)⟩
  letI : Valued K1 ℝ≥0 := NormedField.toValued
  let vK1 : Valuation K1 ℝ≥0 := Valued.v
  letI : vK1.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := K1)).IsNontrivial)
  letI : ValuativeRel K1 := ValuativeRel.ofValuation vK1
  letI : vK1.Compatible := Valuation.Compatible.ofValuation vK1
  letI : ValuativeRel.IsNontrivial K1 :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vK1).2 inferInstance
  letI : IsValuativeTopology K1 :=
    isValuativeTopology_of_valued_ofValuation K1 ℝ≥0
  letI : IsNonarchimedeanLocalField K1 :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

  letI hAlgK1Omega : Algebra K1 (SeparableClosure K) :=
    K1.val.toRingHom.toAlgebra
  letI : SMul K1 (SeparableClosure K) :=
    Algebra.toSMul (self := hAlgK1Omega)
  letI : IsScalarTower K K1 (SeparableClosure K) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  letI : Algebra.IsSeparable K1 (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K K1 (SeparableClosure K)
  letI : IsSepClosure K1 (SeparableClosure K) :=
    { sep_closed := inferInstance
      separable := inferInstance }

  let Delta := KummerTheory.maximalKummerSubgroup K1 n
  let L1 := kummerRadicalExtension
    (K := K1) (Omega := SeparableClosure K) n Delta.1
  letI : IsGalois K1 L1 :=
    kummerRadicalExtension_isGalois
      (K := K1) (Omega := SeparableClosure K) n Delta.1
  letI : FiniteDimensional K1 L1 :=
    KummerTheory.maximalKummerRadicalExtension_finiteDimensional
      (K := K1) (Omega := SeparableClosure K) n hnK1 hmu1
  letI : Module.Free K1 L1 := Module.Free.of_divisionRing K1 L1
  have hnormK1 :
      localNormSubgroup K1 L1 = (powMonoidHom (n : ℕ) : K1ˣ →* K1ˣ).range := by
    change localNormSubgroup K1
        (kummerRadicalExtension
          (K := K1) (Omega := SeparableClosure K) n
            (KummerTheory.maximalKummerSubgroup K1 n).1) =
      (powMonoidHom (n : ℕ) : K1ˣ →* K1ˣ).range
    exact maximalKummerNormSubgroup_eq_powMonoidHom_range
      (K := K1) (Omega := SeparableClosure K) n hnK1 hmu1

  letI : Algebra K L1 :=
    ((algebraMap K1 L1).comp (algebraMap K K1)).toAlgebra
  letI : IsScalarTower K K1 L1 := IsScalarTower.of_algebraMap_eq' rfl
  have hnormL1 :
      localNormSubgroup K L1 ≤ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
    rintro x ⟨y, rfl⟩
    have hy : normUnits K1 L1 y ∈ (powMonoidHom (n : ℕ) : K1ˣ →* K1ˣ).range := by
      rw [← hnormK1]
      exact ⟨y, rfl⟩
    rw [MonoidHom.mem_range] at hy ⊢
    obtain ⟨a, ha⟩ := hy
    refine ⟨normUnits K K1 a, ?_⟩
    calc
      normUnits K K1 a ^ (n : ℕ) =
          normUnits K K1 (a ^ (n : ℕ)) := by rw [map_pow]
      _ = normUnits K K1 (normUnits K1 L1 y) := congrArg _ ha
      _ = normUnits K L1 y := LocalFieldTheory.normUnits_tower K K1 L1 y

  let L0 := L1.restrictScalars K
  letI : FiniteDimensional K L1 := FiniteDimensional.trans K K1 L1
  let eLin : L0 ≃ₗ[K] L1 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro x; ext; rfl
      map_add' := by intro x y; ext; rfl
      map_smul' := by intro a x; ext; rfl }
  letI : FiniteDimensional K L0 := Module.Finite.equiv eLin.symm
  let eL : L1 ≃ₐ[K] L0 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro x; ext; rfl
      map_add' := by intro x y; ext; rfl
      map_mul' := by intro x y; ext; rfl
      commutes' := by intro x; ext; rfl }
  have hnormL0 :
      localNormSubgroup K L0 ≤ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
    rw [LocalFieldTheory.normSubgroup_algEquiv K L1 L0 eL]
    exact hnormL1

  let F := IntermediateField.normalClosure K L0 (SeparableClosure K)
  letI : FiniteDimensional K F :=
    normalClosure.is_finiteDimensional K L0 (SeparableClosure K)
  letI : IsGalois K F :=
    IsGalois.normalClosure K L0 (SeparableClosure K)
  letI hAlgL0F : Algebra L0 F :=
    (IntermediateField.inclusion
      (IntermediateField.le_normalClosure L0)).toAlgebra
  letI : SMul L0 F := Algebra.toSMul (self := hAlgL0F)
  letI : Module L0 F := Algebra.toModule
  letI : IsScalarTower K L0 F := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  letI : FiniteDimensional L0 F := FiniteDimensional.right K L0 F

  have hnormFL0 : localNormSubgroup K F ≤ localNormSubgroup K L0 :=
    LocalFieldTheory.normSubgroup_le_of_tower K L0 F
  have hnormF : localNormSubgroup K F ≤ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
    intro x hx
    exact hnormL0 (hnormFL0 hx)

  let E : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := F
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  exact ⟨E, by simpa [E] using hnormF⟩

end LocalClassFieldTheory

end
