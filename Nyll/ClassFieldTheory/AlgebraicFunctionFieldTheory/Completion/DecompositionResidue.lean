/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition

/-!
# The decomposition group on the actual residue field

A field automorphism stabilizing a place preserves its valuation ring. Its
induced automorphism of the residue field fixes the residue field below.
The construction uses the original valuation rings and their residue maps.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

private theorem valuationCast_coe {u w : Place k L} (h : u = w)
    (x : u.toValuationSubring) :
    ((RingEquiv.cast (R := fun v : Place k L => v.toValuationSubring) h x :
      w.toValuationSubring) : L) = (x : L) := by
  subst w
  rfl

/-- A decomposition automorphism preserves the original valuation ring. -/
def decompositionValuationEquiv (w : Place k L) (σ : decompositionGroup (K := K) w) :
    w.toValuationSubring ≃+* w.toValuationSubring :=
  (SemilinearAut.smulValuationSubringEquiv
    (SemilinearAut.ofAlgAut (σ.1.restrictScalars k)) w.toValuationSubring).trans
      (RingEquiv.cast (R := fun v : Place k L => v.toValuationSubring)
        (decompositionGroup_smul_eq w σ))

@[simp]
theorem decompositionValuationEquiv_coe (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.toValuationSubring) :
    ((decompositionValuationEquiv w σ x : w.toValuationSubring) : L) = σ.1 (x : L) := by
  change ((RingEquiv.cast (R := fun v : Place k L => v.toValuationSubring)
    (decompositionGroup_smul_eq w σ)
    (SemilinearAut.smulValuationSubringEquiv
      (SemilinearAut.ofAlgAut (σ.1.restrictScalars k)) w.toValuationSubring x) :
        w.toValuationSubring) : L) = _
  rw [valuationCast_coe]
  rfl

/-- Restriction to the valuation ring respects composition of decomposition automorphisms. -/
def decompositionValuationAut (w : Place k L) :
    decompositionGroup (K := K) w →* RingAut w.toValuationSubring where
  toFun := decompositionValuationEquiv w
  map_one' := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    exact decompositionValuationEquiv_coe w 1 x
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change ((decompositionValuationEquiv w (σ * τ) x : w.toValuationSubring) : L) =
      ((decompositionValuationEquiv w σ (decompositionValuationEquiv w τ x) :
        w.toValuationSubring) : L)
    simp only [decompositionValuationEquiv_coe, Subgroup.coe_mul, AlgEquiv.mul_apply]

/-- The genuine residue-field action induced by the decomposition group. -/
def decompositionResidueRingAut (w : Place k L) :
    decompositionGroup (K := K) w →* RingAut w.ResidueField :=
  IsLocalRing.ResidueField.mapAut.comp (decompositionValuationAut (K := K) w)

@[simp]
theorem decompositionResidueRingAut_residue (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.toValuationSubring) :
    decompositionResidueRingAut (K := K) w σ (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (decompositionValuationEquiv w σ x) := by
  change IsLocalRing.ResidueField.mapEquiv (decompositionValuationEquiv w σ)
    (IsLocalRing.residue _ x) = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

variable [Algebra.IsIntegral K L]

/-- A decomposition automorphism acts over the residue field of the place below. -/
def decompositionResidueAlgEquiv (w : Place k L)
    (σ : decompositionGroup (K := K) w) :
    w.ResidueField ≃ₐ[(w.restrict K).ResidueField] w.ResidueField where
  __ := decompositionResidueRingAut (K := K) w σ
  commutes' x := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change decompositionResidueRingAut (K := K) w σ
      (w.restrictResidueMap K (IsLocalRing.residue _ a)) =
        w.restrictResidueMap K (IsLocalRing.residue _ a)
    rw [Place.restrictResidueMap_residue, decompositionResidueRingAut_residue]
    congr 1
    apply Subtype.ext
    rw [decompositionValuationEquiv_coe, Place.coe_restrictInclusion]
    exact σ.1.commutes (a : K)

/-- Reduction is a homomorphism from the actual decomposition group to residue automorphisms. -/
def decompositionResidueAut (w : Place k L) :
    decompositionGroup (K := K) w →*
      (w.ResidueField ≃ₐ[(w.restrict K).ResidueField] w.ResidueField) where
  toFun := decompositionResidueAlgEquiv w
  map_one' := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun (map_one (decompositionResidueRingAut (K := K) w)) x
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun (map_mul (decompositionResidueRingAut (K := K) w) σ τ) x

@[simp]
theorem decompositionResidueAut_residue (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.toValuationSubring) :
    decompositionResidueAut (K := K) w σ (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (decompositionValuationEquiv w σ x) :=
  decompositionResidueRingAut_residue w σ x

end FunctionField.IdeleGroup
