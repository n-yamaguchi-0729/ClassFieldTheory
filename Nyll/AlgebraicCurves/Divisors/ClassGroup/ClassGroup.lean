/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

The generic valuation-subring and exponential-order comparisons are also adapted from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_Repartitions.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Ring.Subring.Pointwise
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Bezout

/-!
Divisors and divisor class groups of a field extension.
The imported place orders define principal divisors and the degree-zero Picard group.
-/

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]



/-- A divisor is a finitely supported integer-valued function on places. -/
abbrev Divisor : Type _ := Place K F →₀ ℤ

namespace Divisor

variable {K F}

/-- The degree homomorphism, weighting each coefficient by its residue-field degree. -/
def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)
@[simp]
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg := by
  exact Finsupp.liftAddHom_apply_single (fun w => AddMonoidHom.mulRight (w.deg : ℤ)) v n

/-- The subgroup of divisors with degree zero. -/
def degZero : AddSubgroup (Divisor K F) := degree.ker

theorem mem_degZero {D : Divisor K F} : D ∈ degZero (K := K) (F := F) ↔ degree D = 0 :=
  Iff.rfl

/-- A divisor is principal if its coefficients are the orders of one nonzero function. -/
def IsPrincipal (D : Divisor K F) : Prop := ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

/-- The additive subgroup of principal divisors. -/
def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => v.ord_one.symm⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩

theorem mem_principal {D : Divisor K F} :
    D ∈ principal (K := K) (F := F) ↔ IsPrincipal D := Iff.rfl

end Divisor

/-- Nonzero functions have finitely supported principal divisors of degree zero. -/
class HasPrincipalDivisors : Prop where
  /-- A nonzero function admits a divisor with its valuation orders and with degree zero. -/
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0

/-- The divisor class group, obtained by quotienting divisors by principal divisors. -/
abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal (K := K) (F := F)

/-- Degree-zero divisors modulo the principal divisors lying in the degree-zero subgroup. -/
abbrev Pic0 : Type _ :=
  Divisor.degZero (K := K) (F := F) ⧸
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))

namespace Pic0

variable {K F}

/-- The quotient map from degree-zero divisors to their divisor classes. -/
def mk (D : Divisor.degZero (K := K) (F := F)) : Pic0 K F := QuotientAddGroup.mk D

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective
@[simp]
theorem mk_add (D E : Divisor.degZero (K := K) (F := F)) : mk (D + E) = mk D + mk E := rfl
@[simp]
theorem mk_zero : mk (0 : Divisor.degZero (K := K) (F := F)) = 0 := rfl

variable (K F) in
/-- The subgroup of degree-zero divisor classes annihilated by `n`. -/
def torsion (n : ℕ) : AddSubgroup (Pic0 K F) :=
  (Submodule.torsionBy ℤ (Pic0 K F) (n : ℤ)).toAddSubgroup

theorem mem_torsion {n : ℕ} {x : Pic0 K F} : x ∈ torsion K F n ↔ (n : ℤ) • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

end Pic0

/-- The prescribed cardinalities of the prime-power torsion subgroups of `Pic0`. -/
def AbelJacobiCard (p : ℕ) (g : ℕ) : Prop :=
  ∀ n : ℕ, Nat.card (Pic0.torsion K F (p ^ n)) = p ^ (2 * g * n)



namespace Divisor

open scoped Pointwise

variable {K F}

instance : DistribMulAction (F ≃ₐ[K] F) (Divisor K F) := Finsupp.comapDistribMulAction

theorem smul_def (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    σ • D = Finsupp.mapDomain (σ • ·) D := rfl
@[simp]
theorem smul_single (σ : F ≃ₐ[K] F) (v : Place K F) (n : ℤ) :
    σ • Finsupp.single v n = Finsupp.single (σ • v) n := by
  rw [smul_def, Finsupp.mapDomain_single]

theorem smul_apply_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) (v : Place K F) :
    (σ • D) (σ • v) = D v := by
  rw [smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective σ) D v

theorem smul_apply (σ : F ≃ₐ[K] F) (D : Divisor K F) (w : Place K F) :
    (σ • D) w = D (σ⁻¹ • w) := by
  have : (σ • D) (σ • (σ⁻¹ • w)) = D (σ⁻¹ • w) := smul_apply_smul σ D (σ⁻¹ • w)
  rwa [smul_inv_smul] at this
@[simp]
theorem degree_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) : degree (σ • D) = degree D := by
  induction D using Finsupp.induction with
  | zero => rw [smul_zero]
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, degree_single, degree_single,
        Place.deg_smul]

theorem smul_mem_degZero (σ : F ≃ₐ[K] F) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) : σ • D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_smul]

theorem smul_mem_principal (σ : F ≃ₐ[K] F) {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) : σ • D ∈ principal (K := K) (F := F) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨σ f, (map_ne_zero σ).mpr hf, fun w => ?_⟩
  rw [smul_apply, hD (σ⁻¹ • w)]
  have h := Place.ord_smul σ (σ⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

end Divisor

namespace Pic0

open scoped Pointwise

variable {K F}

/-- The additive action of a field automorphism restricted to degree-zero divisors. -/
def degZeroSMulHom (σ : F ≃ₐ[K] F) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((DistribSMul.toAddMonoidHom (Divisor K F) σ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.smul_mem_degZero σ D.2)
@[simp]
theorem coe_degZeroSMulHom (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroSMulHom σ D : Divisor K F) = σ • (D : Divisor K F) := rfl

instance : SMul (F ≃ₐ[K] F) (Pic0 K F) where
  smul σ := QuotientAddGroup.map _ _ (degZeroSMulHom σ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.smul_mem_principal σ hD)

theorem smul_mk (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    σ • (mk D) = mk (degZeroSMulHom σ D) := rfl

instance : DistribMulAction (F ≃ₐ[K] F) (Pic0 K F) where
  one_smul x := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    rw [smul_mk]
    exact congrArg mk (Subtype.ext (by rw [coe_degZeroSMulHom, one_smul]))
  mul_smul σ τ x := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    rw [smul_mk, smul_mk, smul_mk]
    exact congrArg mk (Subtype.ext (by simp only [coe_degZeroSMulHom]; rw [mul_smul]))
  smul_zero σ := by
    change σ • mk 0 = mk 0
    rw [smul_mk]
    exact congrArg mk (map_zero _)
  smul_add σ x y := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    obtain ⟨E, rfl⟩ := mk_surjective y
    change σ • mk (D + E) = mk (degZeroSMulHom σ D) + mk (degZeroSMulHom σ E)
    rw [smul_mk]
    exact congrArg mk (map_add _ _ _)

end Pic0



end AlgebraicCurve

end
