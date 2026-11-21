/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardGaloisDescent
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardGaloisNorm
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic

/-! # Degree-zero Tate cohomology of the standard idele class group -/

@[expose] public section

open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped NumberField

noncomputable section

namespace NumberField.IdeleClassGroup

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "CL" => IdeleClassGroup (𝓞 L) L
local notation "GalLK" => Gal(L/K)

local instance : MulDistribMulAction GalLK CL := relativeGaloisAction K L

/-- Galois descent identifies the fixed points of the original class group
with the class group of the original base. -/
def fieldInclusionEquivFixed : _root_.IdeleClassGroup K ≃* fixedSubgroup GalLK CL := by
  let f := fieldInclusion K L
  have hf (x : _root_.IdeleClassGroup K) : f x ∈ fixedSubgroup GalLK CL :=
    (mem_range_fieldInclusion_iff_fixed K L (f x)).mp ⟨x, rfl⟩
  let i := f.codRestrict (fixedSubgroup GalLK CL) hf
  refine MulEquiv.ofBijective i ⟨?_, ?_⟩
  · intro x y h
    exact fieldInclusion_injective K L (congrArg Subtype.val h)
  · intro x
    obtain ⟨a, ha⟩ := (mem_range_fieldInclusion_iff_fixed K L x.val).mpr x.property
    exact ⟨a, Subtype.ext ha⟩

private theorem fieldInclusion_norm_eq_tateNorm (c : CL) :
    fieldInclusion K L (norm K L c) = tateNorm GalLK CL c :=
  fieldInclusion_norm_eq_prod_congr K L c

/-- The actual norm image maps onto the Tate norm subgroup of the standard fixed classes. -/
theorem norm_range_map_fieldInclusionEquivFixed :
    (norm K L).range.map (fieldInclusionEquivFixed K L).toMonoidHom =
      (tateNormSubgroup GalLK CL).subgroupOf (fixedSubgroup GalLK CL) := by
  ext z
  constructor
  · rintro ⟨c, ⟨d, rfl⟩, rfl⟩
    exact ⟨d, (fieldInclusion_norm_eq_tateNorm K L d).symm⟩
  · intro hz
    change z.val ∈ tateNormSubgroup GalLK CL at hz
    obtain ⟨d, hd⟩ := hz
    exact ⟨norm K L d, ⟨d, rfl⟩, Subtype.ext ((fieldInclusion_norm_eq_tateNorm K L d).trans hd)⟩

/-- The Tate quotient on standard idele classes is the ordinary class-norm quotient. -/
def herbrandH0EquivClassNormQuotient :
    HerbrandH0 GalLK CL ≃* (_root_.IdeleClassGroup K ⧸ (norm K L).range) :=
  (HerbrandH0.equiv (G := GalLK) (A := CL)).trans
    (QuotientGroup.congr (norm K L).range
      ((tateNormSubgroup GalLK CL).subgroupOf (fixedSubgroup GalLK CL))
      (fieldInclusionEquivFixed K L) (norm_range_map_fieldInclusionEquivFixed K L)).symm

end NumberField.IdeleClassGroup
