/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Noetherian.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardZero
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.ConstantExtension

/-!
# S-units and their divisor lattice

For a finite set of actual places, the orders of actual S-units give a subgroup
of the degree-zero divisors supported there. Its cokernel embeds into the actual
degree-zero Picard group, so it is finite over a finite constant field. The
supported divisor group is a finite Z-module. The stabilizer of the set of
places acts on these groups and the divisor map is equivariant.

These are the S-unit lattice ingredients for a Herbrand-quotient calculation.
They do not assert a cyclic norm-index bound or vanishing of the idele-class
Tate group in degree minus one.
-/

noncomputable section

namespace FunctionField.SUnits

open AlgebraicCurve

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- Nonzero functions whose orders vanish outside the specified finite set. -/
def units (S : Finset (Place k K)) : Subgroup Kˣ where
  carrier := {x | ∀ v : Place k K, v ∉ S → v.ord (x : K) = 0}
  one_mem' := fun v _ => v.ord_one
  mul_mem' := by
    intro x y hx hy v hv
    change v.ord ((x : K) * (y : K)) = 0
    rw [v.ord_mul x.ne_zero y.ne_zero, hx v hv, hy v hv, add_zero]
  inv_mem' := by
    intro x hx v hv
    rw [Units.val_inv_eq_inv_val, v.ord_inv, hx v hv, neg_zero]

/-- The integral lattice of degree-zero divisors supported on `S`. -/
def divisorLattice (S : Finset (Place k K)) : AddSubgroup (Divisor k K) where
  carrier := {D | Divisor.degree D = 0 ∧ ∀ v : Place k K, v ∉ S → D v = 0}
  zero_mem' := ⟨map_zero _, fun _ _ => rfl⟩
  add_mem' := by
    intro D E hD hE
    exact ⟨by rw [map_add, hD.1, hE.1, add_zero], fun v hv => by
      rw [Finsupp.add_apply, hD.2 v hv, hE.2 v hv, add_zero]⟩
  neg_mem' := by
    intro D hD
    exact ⟨by rw [map_neg, hD.1, neg_zero], fun v hv => by
      rw [Finsupp.neg_apply, hD.2 v hv, neg_zero]⟩

variable {k K}

@[simp]
theorem mem_units (S : Finset (Place k K)) (x : Kˣ) :
    x ∈ units k K S ↔ ∀ v : Place k K, v ∉ S → v.ord (x : K) = 0 := Iff.rfl

@[simp]
theorem mem_divisorLattice (S : Finset (Place k K)) (D : Divisor k K) :
    D ∈ divisorLattice k K S ↔
      Divisor.degree D = 0 ∧ ∀ v : Place k K, v ∉ S → D v = 0 := Iff.rfl

/-- The supported lattice embeds into its finitely many integer coordinates. -/
def coordinates (S : Finset (Place k K)) : divisorLattice k K S →+ (S → ℤ) where
  toFun D v := (D : Divisor k K) v
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coordinates_injective (S : Finset (Place k K)) :
    Function.Injective (coordinates S) := by
  intro D E h
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  by_cases hv : v ∈ S
  · exact congrFun h ⟨v, hv⟩
  · exact (D.2.2 v hv).trans (E.2.2 v hv).symm

/-- A divisor supported on a finite set belongs to a finitely generated lattice. -/
theorem finite_divisorLattice (S : Finset (Place k K)) :
    Module.Finite ℤ (divisorLattice k K S) :=
  Module.Finite.of_injective (coordinates S).toIntLinearMap (coordinates_injective S)

/-- Take the actual degree-zero divisor class of a supported divisor. -/
def classMap (S : Finset (Place k K)) : divisorLattice k K S →+ Pic0 k K where
  toFun D := Pic0.mk ⟨D, D.2.1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

section Principal

variable [HasPrincipalDivisors k K]

/-- The actual principal-divisor homomorphism of the underlying curve. -/
def principalDivisor : Additive Kˣ →+ Divisor k K :=
  Divisor.principalHom

@[simp]
theorem principalDivisor_apply (x : Additive Kˣ) (v : Place k K) :
    principalDivisor x v = v.ord (x.toMul : K) :=
  Divisor.principalHom_apply x v

theorem degree_principalDivisor (x : Additive Kˣ) :
    Divisor.degree (principalDivisor (k := k) x) = 0 :=
  Divisor.degree_principalHom x

/-- The divisor map on S-units, with its actual supported degree-zero codomain. -/
def divisor (S : Finset (Place k K)) :
    Additive (units k K S) →+ divisorLattice k K S :=
  ((principalDivisor (k := k) (K := K)).comp
    (units k K S).subtype.toAdditive).codRestrict _ fun x =>
      ⟨degree_principalDivisor (Additive.ofMul (x.toMul : Kˣ)), fun v hv => by
        rw [AddMonoidHom.comp_apply, principalDivisor_apply]
        exact x.toMul.2 v hv⟩

@[simp]
theorem divisor_apply (S : Finset (Place k K)) (x : Additive (units k K S))
    (v : Place k K) :
    (divisor S x : Divisor k K) v = v.ord ((x.toMul : Kˣ) : K) :=
  principalDivisor_apply _ v

/-- The kernel of the map to Picard classes is exactly the S-unit divisor image. -/
theorem range_divisor_eq_ker_classMap (S : Finset (Place k K)) :
    (divisor S).range = (classMap S).ker := by
  ext D
  change (∃ x, divisor S x = D) ↔
    Pic0.mk (⟨D, D.2.1⟩ : Divisor.degZero (K := k) (F := K)) = 0
  rw [Pic0.mk_eq_zero_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨((x.toMul : Kˣ) : K), (x.toMul : Kˣ).ne_zero, divisor_apply S x⟩
  · rintro ⟨f, hf, hD⟩
    let u : units k K S := ⟨Units.mk0 f hf, fun v hv =>
      (hD v).symm.trans (D.2.2 v hv)⟩
    refine ⟨Additive.ofMul u, ?_⟩
    apply Subtype.ext
    apply Finsupp.ext
    intro v
    exact (divisor_apply S (Additive.ofMul u) v).trans (hD v).symm

/-- Every zero Picard class in the supported lattice is realized by an actual S-unit. -/
theorem classMap_eq_zero_iff (S : Finset (Place k K)) (D : divisorLattice k K S) :
    classMap S D = 0 ↔ ∃ x : Additive (units k K S), divisor S x = D := by
  change D ∈ (classMap S).ker ↔ D ∈ (divisor S).range
  rw [range_divisor_eq_ker_classMap]

/-- The S-unit divisor cokernel identifies with a subgroup of the actual Picard group. -/
def cokernelEquivRange (S : Finset (Place k K)) :
    divisorLattice k K S ⧸ (divisor S).range ≃+ (classMap S).range := by
  rw [range_divisor_eq_ker_classMap]
  exact QuotientAddGroup.quotientKerEquivRange (classMap S)

section FiniteConstants

variable (k K) [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The genuine finite-field Picard theorem makes the S-unit divisor cokernel finite. -/
theorem finite_cokernel (S : Finset (Place k K)) :
    Finite (divisorLattice k K S ⧸ (divisor S).range) := by
  have : Finite (Pic0 k K) := FunctionField.finite_pic0 k K
  exact Finite.of_equiv (classMap S).range (cokernelEquivRange S).symm.toEquiv

/-- S-unit divisors have finite index in the full supported degree-zero lattice. -/
theorem finiteIndex_range_divisor (S : Finset (Place k K)) :
    (divisor S).range.FiniteIndex := by
  have : Finite (divisorLattice k K S ⧸ (divisor S).range) := finite_cokernel k K S
  exact AddSubgroup.finiteIndex_of_finite_quotient

end FiniteConstants

end Principal

section Action

variable (k K)

/-- Semilinear automorphisms preserving the specified set of places. -/
def stabilizer (S : Finset (Place k K)) : Subgroup (SemilinearAut k K) where
  carrier := {g | ∀ v : Place k K, g • v ∈ S ↔ v ∈ S}
  one_mem' := fun v => by rw [one_smul]
  mul_mem' := by
    intro g h hg hh v
    rw [mul_smul, hg, hh]
  inv_mem' := by
    intro g hg v
    have h := hg (g⁻¹ • v)
    rw [smul_inv_smul] at h
    exact h.symm

variable {k K}

/-- A semilinear group action preserving `S` factors through its actual stabilizer. -/
def stabilizerHom {G : Type*} [Group G] (S : Finset (Place k K))
    (ρ : G →* SemilinearAut k K)
    (hS : ∀ g : G, ∀ v : Place k K, ρ g • v ∈ S ↔ v ∈ S) :
    G →* stabilizer k K S :=
  ρ.codRestrict (stabilizer k K S) hS

private theorem map_mem_units (S : Finset (Place k K)) (g : stabilizer k K S)
    (x : units k K S) :
    Units.map (SemilinearAut.toRingAut g.val).toMonoidHom (x : Kˣ) ∈ units k K S := by
  intro v hv
  have hv' : g.val⁻¹ • v ∉ S := by
    intro h
    have hvS := (g.2 (g.val⁻¹ • v)).mpr h
    rw [smul_inv_smul] at hvS
    exact hv hvS
  have h := SemilinearAut.ord_smul g.val (g.val⁻¹ • v) ((x : Kˣ) : K)
  rw [smul_inv_smul] at h
  exact h.trans (x.2 _ hv')

/-- The stabilizer acts on the actual S-unit subgroup through field automorphisms. -/
instance unitsMulDistribMulAction (S : Finset (Place k K)) :
    MulDistribMulAction (stabilizer k K S) (units k K S) where
  smul g x := ⟨Units.map (SemilinearAut.toRingAut g.val).toMonoidHom (x : Kˣ),
    map_mem_units S g x⟩
  one_smul _ := Subtype.ext (Units.ext rfl)
  mul_smul _ _ _ := Subtype.ext (Units.ext rfl)
  smul_one _ := Subtype.ext (Units.ext (map_one _))
  smul_mul _ _ _ := Subtype.ext (Units.ext (map_mul _ _ _))

private theorem smul_mem_lattice (S : Finset (Place k K)) (g : stabilizer k K S)
    (D : divisorLattice k K S) :
    g.val • (D : Divisor k K) ∈ divisorLattice k K S := by
  refine ⟨(SemilinearAut.degree_smul g.val D).trans D.2.1, fun v hv => ?_⟩
  rw [SemilinearAut.divisor_smul_apply]
  apply D.2.2
  intro h
  have hv' := (g.2 (g.val⁻¹ • v)).mpr h
  rw [smul_inv_smul] at hv'
  exact hv hv'

/-- The same stabilizer acts on supported degree-zero divisors. -/
instance latticeDistribMulAction (S : Finset (Place k K)) :
    DistribMulAction (stabilizer k K S) (divisorLattice k K S) where
  smul g D := ⟨g.val • (D : Divisor k K), smul_mem_lattice S g D⟩
  one_smul D := Subtype.ext (one_smul _ D.val)
  mul_smul g h D := Subtype.ext (mul_smul g.val h.val D.val)
  smul_zero g := Subtype.ext (smul_zero g.val)
  smul_add g D E := Subtype.ext (smul_add g.val D.val E.val)

/-- Actual S-unit divisors commute with the semilinear stabilizer action. -/
theorem divisor_smul [HasPrincipalDivisors k K]
    (S : Finset (Place k K)) (g : stabilizer k K S)
    (x : units k K S) :
    divisor S (Additive.ofMul (g • x)) = g • divisor S (Additive.ofMul x) := by
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  rw [divisor_apply]
  change v.ord (g.val • ((x : Kˣ) : K)) =
    (g.val • (divisor S (Additive.ofMul x) : Divisor k K)) v
  rw [SemilinearAut.divisor_smul_apply, divisor_apply]
  have h := SemilinearAut.ord_smul g.val (g.val⁻¹ • v) ((x : Kˣ) : K)
  rw [smul_inv_smul] at h
  exact h

/-- The finite-cokernel comparison is compatible with the actual Picard action. -/
theorem classMap_smul (S : Finset (Place k K)) (g : stabilizer k K S)
    (D : divisorLattice k K S) :
    classMap S (g • D) = g.val • classMap S D := rfl

end Action

end FunctionField.SUnits
