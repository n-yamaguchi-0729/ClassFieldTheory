/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Restriction.RestrictionComposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.AlgEquiv
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.AlgEquiv
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.DenseEmbedding

/-!
# Conjugation invariance of completed and all-place norms

The completed automorphism is an isomorphism over the actual base completion:
the required square agrees on the dense original base field. Thus invariance of
the determinant norm applies to the same completion algebras used by `localNormOver`.
Reindexing the actual finite fiber proves invariance of the all-place idele norm,
and the equality descends to idele classes.

These naturality results are used by the Galois product formula in `NormProduct`.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

namespace IdeleGroup

/-- The canonical completed extension map commutes with a base-fixing field automorphism.
Only the equality of the restricted place is transported. -/
theorem completionMapOver_algAut (σ : L ≃ₐ[K] L) (v : Place k K)
    (w : Place k L) (hw : w.restrict K = v) :
    (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k)) w).toRingHom.comp
        (completionMapOver v w hw) =
      completionMapOver v (SemilinearAut.ofAlgAut (σ.restrictScalars k) • w)
        ((Place.restrict_ofAlgAut_smul σ w).trans hw) := by
  let g : SemilinearAut k L := SemilinearAut.ofAlgAut (σ.restrictScalars k)
  have hfun : (fun x => placeCompletionRingEquiv g w (completionMapOver v w hw x)) =
      completionMapOver v (g • w) ((Place.restrict_ofAlgAut_smul σ w).trans hw) := by
    apply (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
      K v.heightOneSpectrum).equalizer
    · exact (continuous_placeCompletionRingEquiv g w).comp
        (continuous_completionMapOver v w hw)
    · exact continuous_completionMapOver v (g • w)
        ((Place.restrict_ofAlgAut_smul σ w).trans hw)
    · funext x
      change placeCompletionRingEquiv g w
          (completionMapOver v w hw (algebraMap K v.adicCompletion x)) =
        completionMapOver v (g • w) ((Place.restrict_ofAlgAut_smul σ w).trans hw)
          (algebraMap K v.adicCompletion x)
      rw [completionMapOver_algebraMap, completionMapOver_algebraMap,
        placeCompletionRingEquiv_algebraMap]
      change algebraMap L (g • w).adicCompletion (σ (algebraMap K L x)) =
        algebraMap L (g • w).adicCompletion (algebraMap K L x)
      rw [σ.commutes]
  exact RingHom.ext (fun x => congrFun hfun x)

/-- The norm of a completed element is unchanged after conjugating both its place
and its value by a field automorphism over the base. -/
theorem localNormOver_algAut (σ : L ≃ₐ[K] L) (v : Place k K)
    (w : Place k L) (hw : w.restrict K = v) (x : w.adicCompletionˣ) :
    localNormOver v (SemilinearAut.ofAlgAut (σ.restrictScalars k) • w)
        ((Place.restrict_ofAlgAut_smul σ w).trans hw)
        (placeCompletionUnitsEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k)) w x) =
      localNormOver v w hw x := by
  let g : SemilinearAut k L := SemilinearAut.ofAlgAut (σ.restrictScalars k)
  let a₁ : Algebra v.adicCompletion w.adicCompletion :=
    (completionMapOver v w hw).toAlgebra
  let a₂ : Algebra v.adicCompletion (g • w).adicCompletion :=
    (completionMapOver v (g • w) ((Place.restrict_ofAlgAut_smul σ w).trans hw)).toAlgebra
  let e : w.adicCompletion ≃ₐ[v.adicCompletion] (g • w).adicCompletion :=
    { __ := placeCompletionRingEquiv g w
      commutes' := fun y => congrArg (fun f : v.adicCompletion →+* (g • w).adicCompletion =>
        f y) (completionMapOver_algAut σ v w hw) }
  rw [localNormOver_eq_norm, localNormOver_eq_norm]
  apply Units.ext
  change Algebra.norm v.adicCompletion (e (x : w.adicCompletion)) =
    Algebra.norm v.adicCompletion (x : w.adicCompletion)
  exact Algebra.norm_eq_of_algEquiv e (x : w.adicCompletion)

variable [Algebra.IsSeparable K L]

private def inverseAutomorphismFiberEquiv (σ : L ≃ₐ[K] L) (v : Place k K) :
    v.fiberOver L ≃ v.fiberOver L where
  toFun w := ⟨(SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w.1,
    (Place.mem_fiberOver v).mpr ((Place.restrict_ofAlgAut_smul σ.symm w.1).trans
      ((Place.mem_fiberOver v).mp w.2))⟩
  invFun w := ⟨SemilinearAut.ofAlgAut (σ.restrictScalars k) • w.1,
    (Place.mem_fiberOver v).mpr ((Place.restrict_ofAlgAut_smul σ w.1).trans
      ((Place.mem_fiberOver v).mp w.2))⟩
  left_inv w := Subtype.ext (smul_inv_smul (SemilinearAut.ofAlgAut (σ.restrictScalars k)) w.1)
  right_inv w := Subtype.ext (inv_smul_smul (SemilinearAut.ofAlgAut (σ.restrictScalars k)) w.1)

/-- The all-place norm is invariant under the actual completed action of every
automorphism of the finite separable extension. Galoisness is not required. -/
theorem norm_algAut_smul (σ : L ≃ₐ[K] L) (a : IdeleGroup k L) :
    norm (k := k) (K := K) (L := L)
        (SemilinearAut.ofAlgAut (σ.restrictScalars k) • a) =
      norm (k := k) (K := K) (L := L) a := by
  let g : SemilinearAut k L := SemilinearAut.ofAlgAut (σ.restrictScalars k)
  apply IdeleGroup.ext
  intro v
  change component v (norm (k := k) (K := K) (L := L) (g • a)) =
    component v (norm (k := k) (K := K) (L := L) a)
  rw [component_norm, component_norm]
  let e : v.fiberOver L ≃ v.fiberOver L := inverseAutomorphismFiberEquiv σ v
  calc
    (∏ w : v.fiberOver L, localNormOver v w.1 ((Place.mem_fiberOver v).mp w.2)
        ((g • a) w.1)) =
        ∏ w : v.fiberOver L, localNormOver v (e w).1
          ((Place.mem_fiberOver v).mp (e w).2) (a (e w).1) := by
      apply Finset.prod_congr rfl
      intro w _
      have h := localNormOver_algAut σ.symm v w.1 ((Place.mem_fiberOver v).mp w.2)
        ((placeCompletionUnitsEquiv g⁻¹ w.1).symm (a (g⁻¹ • w.1)))
      change localNormOver v (g⁻¹ • w.1) _
          (placeCompletionUnitsEquiv g⁻¹ w.1
            ((placeCompletionUnitsEquiv g⁻¹ w.1).symm (a (g⁻¹ • w.1)))) =
        localNormOver v w.1 _ ((placeCompletionUnitsEquiv g⁻¹ w.1).symm
          (a (g⁻¹ • w.1))) at h
      rw [ContinuousMulEquiv.apply_symm_apply] at h
      exact h.symm
    _ = ∏ w : v.fiberOver L,
        localNormOver v w.1 ((Place.mem_fiberOver v).mp w.2) (a w.1) :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)

end IdeleGroup

namespace IdeleClassGroup

variable [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Conjugation invariance descends through the actual principal-idele quotient. -/
theorem norm_algAut_smul (σ : L ≃ₐ[K] L) (c : IdeleClassGroup k L) :
    norm (k := k) (K := K) (L := L)
        (SemilinearAut.ofAlgAut (σ.restrictScalars k) • c) =
      norm (k := k) (K := K) (L := L) c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) c
  rw [smul_mk]
  change mk (k := k) (K := K)
      (IdeleGroup.norm (k := k) (K := K) (L := L)
        (SemilinearAut.ofAlgAut (σ.restrictScalars k) • a)) =
    mk (k := k) (K := K) (IdeleGroup.norm (k := k) (K := K) (L := L) a)
  exact congrArg (mk (k := k) (K := K)) (IdeleGroup.norm_algAut_smul σ a)

end IdeleClassGroup

end FunctionField
