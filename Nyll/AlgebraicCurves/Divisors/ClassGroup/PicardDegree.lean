/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_JacobianH1Autoduality.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The degree exact sequence of the Picard group

The degree-zero Picard group identifies with the kernel of degree on divisor classes.
These definitions retain their existing cohomological names.
-/

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Divisor

variable {K F}

theorem principal_le_degZero [HasPrincipalDivisors K F] :
    Divisor.principal (K := K) (F := F) ≤ Divisor.degZero (K := K) (F := F) := by
  rintro D ⟨f, hf, hD⟩
  obtain ⟨D', hD'v, hD'deg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have hDD' : D = D' := Finsupp.ext fun v => by rw [hD v, hD'v v]
  exact hDD' ▸ hD'deg

theorem degree_eq_zero_of_isPrincipal [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D.IsPrincipal) : Divisor.degree D = 0 :=
  principal_le_degZero (Divisor.mem_principal.mpr hD)

end Divisor

/-- The Picard group, used here as the model of first cohomology with coefficients in Gm. -/
abbrev H1Gm : Type _ := Pic K F

namespace H1Gm

variable {K F}

/-- The cohomology class represented by a divisor. -/
abbrev mk (D : Divisor K F) : H1Gm K F := QuotientAddGroup.mk D

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective

variable (K F)

/-- The homomorphism from degree-zero divisor classes to the full Picard group. -/
def ofPic0 : Pic0 K F →+ H1Gm K F :=
  QuotientAddGroup.map _ _ (Divisor.degZero (K := K) (F := F)).subtype
    (fun _ hD => hD)

variable {K F} in
@[simp]
theorem ofPic0_mk (D : Divisor.degZero (K := K) (F := F)) :
    ofPic0 K F (Pic0.mk D) = mk (D : Divisor K F) := rfl

theorem ofPic0_injective : Function.Injective (ofPic0 K F) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [ofPic0_mk] at hx
  have hD : (D : Divisor K F) ∈ Divisor.principal (K := K) (F := F) :=
    (QuotientAddGroup.eq_zero_iff (D : Divisor K F)).mp hx
  exact (QuotientAddGroup.eq_zero_iff D).mpr hD

variable [HasPrincipalDivisors K F]

/-- The degree homomorphism on divisor classes. -/
def degree : H1Gm K F →+ ℤ :=
  QuotientAddGroup.lift _ Divisor.degree fun _ hD =>
    Divisor.degree_eq_zero_of_isPrincipal hD

@[simp]
theorem degree_mk (D : Divisor K F) : degree K F (mk D) = Divisor.degree D := rfl

@[simp]
theorem degree_ofPic0 (x : Pic0 K F) : degree K F (ofPic0 K F x) = 0 := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  exact D.2

theorem exact_ofPic0_degree :
    (ofPic0 K F).range = (degree K F).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact degree_ofPic0 K F y
  · intro hx
    obtain ⟨D, rfl⟩ := mk_surjective x
    exact ⟨Pic0.mk ⟨D, hx⟩, rfl⟩

/-- Identify the degree-zero Picard group with the kernel of the degree homomorphism. -/
def ofPic0Equiv : Pic0 K F ≃+ (degree K F).ker :=
  AddEquiv.ofBijective
    ((ofPic0 K F).codRestrict (degree K F).ker fun x =>
      (exact_ofPic0_degree K F).le ⟨x, rfl⟩)
    ⟨fun a b h => ofPic0_injective K F (Subtype.ext_iff.mp h),
     fun y => by
      obtain ⟨x, hx⟩ := (exact_ofPic0_degree K F).ge y.2
      exact ⟨x, Subtype.ext hx⟩⟩

end H1Gm

end AlgebraicCurve
