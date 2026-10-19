/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.Pic0Congr
import Nyll.AlgebraicCurves.Divisors.Norm.PicardNorm
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver

/-!
# Picard norms under an actual field isomorphism

Transport actual divisors along the induced equivalence of places. Restriction
and residue degrees are unchanged over the fixed original field, so the actual
pushforward and its Picard norm image are unchanged.
-/

noncomputable section

namespace AlgebraicCurve

variable {k K L L' : Type*} [Field k] [Field K] [Field L] [Field L']
    [Algebra k L] [Algebra k L']

/-- An algebra isomorphism induces an isomorphism of the full Picard groups. -/
def Pic.congr (e : L ≃ₐ[k] L') : Pic k L ≃+ Pic k L' := by
  let d := Divisor.congr e.toRingEquiv e.commutes
  apply QuotientAddGroup.congr _ _ d
  ext D
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact Divisor.congr_mem_principal e.toRingEquiv e.commutes hB
  · intro hD
    exact ⟨d.symm D, Divisor.congr_symm_mem_principal e.toRingEquiv e.commutes hD,
      d.apply_symm_apply D⟩

/-- The Picard isomorphism is induced by actual transport of divisor representatives. -/
theorem Pic.congr_mk (e : L ≃ₐ[k] L') (D : Divisor k L) :
    Pic.congr e (H1Gm.mk D) = H1Gm.mk (Divisor.congr e.toRingEquiv e.commutes D) := rfl

variable [Algebra k K] [Algebra K L] [Algebra K L']
    [IsScalarTower k K L] [IsScalarTower k K L']
    [Algebra.IsIntegral K L] [Algebra.IsIntegral K L']

/-- Place transport over the original field preserves its restriction. -/
theorem Place.restrict_congrAlgEquiv (e : L ≃ₐ[K] L') (v : Place k L) :
    (Place.congrRingEquiv (e.restrictScalars k).toRingEquiv
      (e.restrictScalars k).commutes v).restrict K = v.restrict K := by
  apply Place.ext
  ext x
  change e.symm (algebraMap K L' x) ∈ v.toValuationSubring ↔
    algebraMap K L x ∈ v.toValuationSubring
  rw [e.symm.commutes]

variable [IsCurveOver k K]

/-- The residue degree over the original field is preserved by field transport. -/
theorem Place.inertiaDeg_congrAlgEquiv (e : L ≃ₐ[K] L') (v : Place k L) :
    (Place.congrRingEquiv (e.restrictScalars k).toRingEquiv
      (e.restrictScalars k).commutes v).inertiaDeg K = v.inertiaDeg K := by
  have hfin : Module.Finite k (v.restrict K).ResidueField :=
    IsCurveOver.finiteResidue (v.restrict K)
  have hn : 0 < (v.restrict K).deg := Module.finrank_pos (R := k)
  have h := (Place.congrRingEquiv (e.restrictScalars k).toRingEquiv
    (e.restrictScalars k).commutes v).deg_restrict_mul_inertiaDeg (F := K)
  rw [Place.restrict_congrAlgEquiv, Place.deg_congrRingEquiv] at h
  exact Nat.eq_of_mul_eq_mul_left hn (h.trans (v.deg_restrict_mul_inertiaDeg (F := K)).symm)

/-- Actual divisor pushforward is unchanged by an isomorphism over the target field. -/
theorem Divisor.pushforward_congrAlgEquiv (e : L ≃ₐ[K] L') (D : Divisor k L) :
    Divisor.pushforward K
        (Divisor.congr (e.restrictScalars k).toRingEquiv (e.restrictScalars k).commutes D) =
      Divisor.pushforward K D := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero, map_zero]
  | single_add v n D hv hn ih =>
    rw [map_add, map_add, map_add, ih, Divisor.congr_single,
      Divisor.pushforward_single, Divisor.pushforward_single,
      Place.restrict_congrAlgEquiv, Place.inertiaDeg_congrAlgEquiv]

variable [FiniteDimensional K L] [FiniteDimensional K L']
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K L']
    [HasPrincipalDivisors k L] [HasPrincipalDivisors k L']

omit [Algebra.IsIntegral K L] [Algebra.IsIntegral K L'] in
/-- Actual Picard norms commute with isomorphisms of the extension field. -/
theorem Pic.norm_congrAlgEquiv (e : L ≃ₐ[K] L') (x : Pic k L) :
    Pic.norm (K := K) (Pic.congr (e.restrictScalars k) x) = Pic.norm (K := K) x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  rw [Pic.congr_mk, Pic.norm_mk, Pic.norm_mk, Divisor.pushforward_congrAlgEquiv]

omit [Algebra.IsIntegral K L] [Algebra.IsIntegral K L'] in
/-- The actual Picard norm image is independent of the realization of the finite extension. -/
theorem Pic.range_norm_congrAlgEquiv (e : L ≃ₐ[K] L') :
    (Pic.norm (k := k) (K := K) (L := L')).range =
      (Pic.norm (k := k) (K := K) (L := L)).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (Pic.congr (e.restrictScalars k)).surjective y
    exact ⟨z, (Pic.norm_congrAlgEquiv e z).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨Pic.congr (e.restrictScalars k) y, Pic.norm_congrAlgEquiv e y⟩

end AlgebraicCurve
