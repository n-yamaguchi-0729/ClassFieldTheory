/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


module

public import Nyll.AlgebraicCurves.Places.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Transport of places along field equivalences

A field equivalence preserving constants transports valuation subrings and residue fields.
The resulting equivalence of places preserves their normalized orders and degrees.
-/

@[expose] public section

noncomputable section

open WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F')

/-- The equivalence from a valuation subring to its transport under the field equivalence. -/
def comapSymmRingEquiv (V : ValuationSubring F) :
    V ≃+* (V.comap (e.symm : F' →+* F)) where
  toFun x := ⟨e x, by
    rw [ValuationSubring.mem_comap]
    change e.symm (e x) ∈ V
    rw [e.symm_apply_apply]
    exact x.2⟩
  invFun y := ⟨e.symm y, y.2⟩
  left_inv x := by
    ext
    exact e.symm_apply_apply x
  right_inv y := by
    ext
    exact e.apply_symm_apply y
  map_mul' x y := by
    ext
    exact e.map_mul x y
  map_add' x y := by
    ext
    exact e.map_add x y
@[simp]
theorem coe_comapSymmRingEquiv_apply (V : ValuationSubring F) (x : V) :
    ((comapSymmRingEquiv e V x : (V.comap (e.symm : F' →+* F))) : F') = e x := rfl

variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he

theorem symm_algebraMap_comm (a : K) : e.symm (algebraMap K F' a) = algebraMap K F a := by
  rw [← he a, e.symm_apply_apply]

/-- The place transported along a field equivalence compatible with the constant-field maps. -/
def congrRingEquiv (v : Place K F) : Place K F' where
  toValuationSubring := v.toValuationSubring.comap (e.symm : F' →+* F)
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap]
    change e.symm (algebraMap K F' a) ∈ v.toValuationSubring
    rw [symm_algebraMap_comm e he a]
    exact v.algebraMap_mem' a
  ne_top' := fun h =>
    v.ne_top' (SetLike.ext fun x =>
      ⟨fun _ => ValuationSubring.mem_top x, fun _ => by
        have hx : e x ∈ v.toValuationSubring.comap (e.symm : F' →+* F) := by
          rw [h]
          exact ValuationSubring.mem_top _
        rw [ValuationSubring.mem_comap] at hx
        have : e.symm (e x) ∈ v.toValuationSubring := hx
        rwa [e.symm_apply_apply] at this⟩)
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective
      (comapSymmRingEquiv e v.toValuationSubring : _ ≃+* _)
      (comapSymmRingEquiv e v.toValuationSubring).surjective
@[simp]
theorem congrRingEquiv_toValuationSubring (v : Place K F) :
    (congrRingEquiv e he v).toValuationSubring
      = v.toValuationSubring.comap (e.symm : F' →+* F) := rfl

/-- The induced equivalence between the original and transported valuation subrings. -/
def congrValuationSubringEquiv (v : Place K F) :
    v.toValuationSubring ≃+* (congrRingEquiv e he v).toValuationSubring :=
  comapSymmRingEquiv e v.toValuationSubring
@[simp]
theorem coe_congrValuationSubringEquiv_apply (v : Place K F) (x : v.toValuationSubring) :
    ((congrValuationSubringEquiv e he v x :
      (congrRingEquiv e he v).toValuationSubring) : F') = e x := rfl

theorem ord_congrRingEquiv (v : Place K F) (f : F) :
    (congrRingEquiv e he v).ord (e f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [map_zero, Place.ord_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  have hπ' : Irreducible (comapSymmRingEquiv e v.toValuationSubring π) :=
    (MulEquiv.irreducible_iff (comapSymmRingEquiv e v.toValuationSubring)).mpr hπ
  have hu' : IsUnit (comapSymmRingEquiv e v.toValuationSubring (u : v.toValuationSubring)) :=
    u.isUnit.map (comapSymmRingEquiv e v.toValuationSubring)
  have key : e f
      = ((hu'.unit : (v.toValuationSubring.comap (e.symm : F' →+* F))) : F')
        * (((comapSymmRingEquiv e v.toValuationSubring π :
            (v.toValuationSubring.comap (e.symm : F' →+* F))) : F') ^ (v.ord f)) := by
    rw [IsUnit.unit_spec, coe_comapSymmRingEquiv_apply, coe_comapSymmRingEquiv_apply,
      ← map_zpow₀, ← map_mul, ← hu]
  rw [key]
  exact (congrRingEquiv e he v).ord_unit_smul_zpow hu'.unit hπ' (v.ord f)

/-- The induced base-field algebra equivalence between the residue fields. -/
def congrResidueAlgEquiv (v : Place K F) :
    v.ResidueField ≃ₐ[K] (congrRingEquiv e he v).ResidueField :=
  AlgEquiv.ofRingEquiv
    (f := IsLocalRing.ResidueField.mapEquiv (congrValuationSubringEquiv e he v))
    (fun a => by
      have h3 : (congrValuationSubringEquiv e he v)
            (algebraMap K v.toValuationSubring a)
          = algebraMap K (congrRingEquiv e he v).toValuationSubring a := by
        ext
        rw [coe_congrValuationSubringEquiv_apply, coe_algebraMap, coe_algebraMap]
        exact he a
      change IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
        = IsLocalRing.residue _ _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      exact congrArg _ h3)

theorem deg_congrRingEquiv (v : Place K F) : (congrRingEquiv e he v).deg = v.deg :=
  ((congrResidueAlgEquiv e he v).toLinearEquiv.finrank_eq).symm

/-- The equivalence of place sets induced by the compatible field equivalence. -/
def congrEquiv : Place K F ≃ Place K F' where
  toFun := congrRingEquiv e he
  invFun := congrRingEquiv e.symm (symm_algebraMap_comm e he)
  left_inv v := by
    ext1
    refine SetLike.ext fun x => ?_
    change e.symm (e.symm.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [RingEquiv.symm_symm, e.symm_apply_apply]
  right_inv v := by
    ext1
    refine SetLike.ext fun x => ?_
    change e.symm.symm (e.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [RingEquiv.symm_symm, e.apply_symm_apply]
@[simp]
theorem congrEquiv_apply (v : Place K F) : congrEquiv e he v = congrRingEquiv e he v := rfl
@[simp]
theorem congrEquiv_symm_apply (v : Place K F') :
    (congrEquiv e he).symm v = congrRingEquiv e.symm (symm_algebraMap_comm e he) v := rfl

end Congr

end Place


end AlgebraicCurve
