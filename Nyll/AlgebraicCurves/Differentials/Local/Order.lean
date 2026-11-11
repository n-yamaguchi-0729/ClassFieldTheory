/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Differentials, residues, and divisor correspondences

Uniformizer differentials, their coefficients, and differential orders at places of a function
field.
-/

@[expose] public section

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}
variable (v : Place K F)

/-- A chosen irreducible element of the valuation ring, viewed in the function field. -/
def uniformizer : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

theorem ord_uniformizer : v.ord v.uniformizer = 1 := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  simpa [uniformizer] using v.ord_coe_irreducible hirr

theorem uniformizer_ne_zero : v.uniformizer ≠ 0 := by
  intro h
  simpa [h, v.ord_zero] using v.ord_uniformizer

/-- The Kähler differential of the chosen uniformizer. -/
def dCoord : Ω[F⁄K] := KaehlerDifferential.D K F v.uniformizer

/-- The differential of the uniformizer spans the space of field differentials. -/
class DCoordGenerates : Prop where
  /-- The singleton uniformizer differential spans the whole differential module. -/
  span_eq_top : Submodule.span F {v.dCoord} = ⊤

theorem dCoord_ne_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] : v.dCoord ≠ 0 := by
  intro h0
  have htop := DCoordGenerates.span_eq_top (v := v)
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[F⁄K])
  have hx_mem : x ∈ Submodule.span F {v.dCoord} := htop ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hx_mem
  exact hx hx_mem

/-- A chosen coefficient expressing the differential as a multiple of the uniformizer
differential, or zero when no coefficient exists. -/
def differentialCoeff (ω : Ω[F⁄K]) : F :=
  letI := Classical.propDecidable
  if h : ∃ f : F, ω = f • v.dCoord then h.choose else 0

theorem exists_eq_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    ∃ f : F, ω = f • v.dCoord := by
  have hω : ω ∈ (⊤ : Submodule F Ω[F⁄K]) := Submodule.mem_top
  rw [← DCoordGenerates.span_eq_top (v := v), Submodule.mem_span_singleton] at hω
  exact hω.imp fun _ hf => hf.symm

/-- An existing local-coordinate expression is recovered by the chosen coefficient. -/
theorem differentialCoeff_smul_dCoord_of_exists {ω : Ω[F⁄K]}
    (h : ∃ f : F, ω = f • v.dCoord) : v.differentialCoeff ω • v.dCoord = ω := by
  rw [differentialCoeff, dite_eq_left h]
  exact h.choose_spec.symm

/-- A nonzero coordinate makes every existing local-coordinate expression unique. -/
theorem differentialCoeff_unique_of_ne_zero (hcoord : v.dCoord ≠ 0)
    {ω : Ω[F⁄K]} {f : F} (hf : ω = f • v.dCoord) : v.differentialCoeff ω = f := by
  have key : (v.differentialCoeff ω - f) • v.dCoord = 0 := by
    rw [sub_smul, v.differentialCoeff_smul_dCoord_of_exists ⟨f, hf⟩, hf, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact (hcoord h).elim

theorem differentialCoeff_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    v.differentialCoeff ω • v.dCoord = ω :=
  v.differentialCoeff_smul_dCoord_of_exists (v.exists_eq_smul_dCoord ω)

theorem differentialCoeff_unique [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : ω = f • v.dCoord) : v.differentialCoeff ω = f :=
  v.differentialCoeff_unique_of_ne_zero v.dCoord_ne_zero hf
@[simp]
theorem differentialCoeff_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff v.dCoord = 1 :=
  v.differentialCoeff_unique (one_smul F v.dCoord).symm
@[simp]
theorem differentialCoeff_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff (0 : Ω[F⁄K]) = 0 :=
  v.differentialCoeff_unique (zero_smul F v.dCoord).symm

theorem differentialCoeff_add [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (ω η : Ω[F⁄K]) :
    v.differentialCoeff (ω + η) = v.differentialCoeff ω + v.differentialCoeff η :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (c : F) (ω : Ω[F⁄K]) :
    v.differentialCoeff (c • ω) = c * v.differentialCoeff ω :=
  v.differentialCoeff_unique
    (by rw [mul_smul, v.differentialCoeff_smul_dCoord])

/-- The order of the differential coefficient at this place. -/
def ordDifferential (ω : Ω[F⁄K]) : ℤ := v.ord (v.differentialCoeff ω)

theorem gate_ordDifferential_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.ordDifferential v.dCoord = 0 := by
  rw [ordDifferential, v.differentialCoeff_dCoord, v.ord_one]

theorem ordDifferential_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {c : F} (hc : c ≠ 0) {ω : Ω[F⁄K]} (hω : v.differentialCoeff ω ≠ 0) :
    v.ordDifferential (c • ω) = v.ord c + v.ordDifferential ω := by
  rw [ordDifferential, ordDifferential, v.differentialCoeff_smul, v.ord_mul hc hω]

end Place

end AlgebraicCurve

end
