/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ConstantHilbertPicard
public import Nyll.AlgebraicCurves.Divisors.ConstantReindexTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteClassGroupNorm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor
public import Nyll.AlgebraicCurves.Divisors.Norm.PicardNorm
public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindexNorm

/-!
# The original idele norm and Picard classes at constant stages

All ideles are measured over the same initial finite field. Divisor
pushforward and the proved degree formula identify their actual norm with
the Picard norm after reindexing constants. The zero-degree representatives
supplied by Hilbert reciprocity therefore need no correction term at the
chosen rational places.
-/

@[expose] public section

noncomputable section

universe u v w x y

open AlgebraicCurve

namespace FunctionField.IdeleClassGroup

variable {k : Type u} {K : Type v} {L : Type w}
    [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The original idele class norm induces the actual Picard norm. -/
theorem divisorClass_finiteNorm (c : IdeleClassGroup k L) :
    (divisorClass (finiteNorm (k := k) (K := K) (L := L) c)).toAdd =
      Pic.norm (K := K) (divisorClass c).toAdd := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) c
  change H1Gm.mk (IdeleGroup.divisor (IdeleGroup.norm (K := K) (L := L) a)).toAdd =
    Pic.norm (K := K) (H1Gm.mk (IdeleGroup.divisor a).toAdd)
  rw [IdeleGroup.divisor_norm, Pic.norm_mk]

variable {C : Type x} {E : Type y} [Field C] [Field E]
  [Algebra k C] [Algebra C K] [IsScalarTower k C K] [Module.Finite k C]
  [Algebra k E] [Algebra E L] [IsScalarTower k E L] [Algebra.IsIntegral k E]
  [HasPrincipalDivisors C K] [HasPrincipalDivisors E L]

/-- A degree-zero original idele representative has precisely the expected
Picard norm at the smaller constant stage. -/
theorem ofPic0_constantPointedDivisorClass_finiteNorm
    (ε : Place C K) (hε : ε.deg = 1) (c : IdeleClassGroup k L)
    (x : Pic0 E L)
    (hc : picConstantEquiv k E L (divisorClass c).toAdd = H1Gm.ofPic0 E L x) :
    H1Gm.ofPic0 C K
        (constantPointedDivisorClass k C K ε hε
          (finiteNorm (k := k) (K := K) (L := L) c)).toAdd =
      picConstantEquiv k C K
        (Pic.norm (K := K) ((picConstantEquiv k E L).symm (H1Gm.ofPic0 E L x))) := by
  have hsource : (divisorClass c).toAdd =
      (picConstantEquiv k E L).symm (H1Gm.ofPic0 E L x) :=
    (picConstantEquiv k E L).injective (hc.trans
      ((picConstantEquiv k E L).apply_symm_apply _).symm)
  have hdegreeSource : H1Gm.degree k L (divisorClass c).toAdd = 0 := by
    rw [degree_picConstantEquiv k E L, hc, H1Gm.degree_ofPic0, mul_zero]
  have hdegreeTarget : H1Gm.degree C K
      (picConstantEquiv k C K
        (divisorClass (finiteNorm (k := k) (K := K) (L := L) c)).toAdd) = 0 := by
    have hd : (Module.finrank k C : ℤ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := k) (M := C)).ne'
    have hprod : (Module.finrank k C : ℤ) * H1Gm.degree C K
        (picConstantEquiv k C K
          (divisorClass (finiteNorm (k := k) (K := K) (L := L) c)).toAdd) = 0 := by
      rw [← degree_picConstantEquiv k C K, divisorClass_finiteNorm,
        Pic.degree_norm, hdegreeSource]
    exact (mul_eq_zero.mp hprod).resolve_left hd
  change H1Gm.ofPic0 C K (Pic0.pointedClass ε hε
    (picConstantEquiv k C K
      (divisorClass (finiteNorm (k := k) (K := K) (L := L) c)).toAdd)) = _
  rw [Pic0.ofPic0_pointedClass, hdegreeTarget, Finsupp.single_zero]
  change picConstantEquiv k C K
    (divisorClass (finiteNorm (k := k) (K := K) (L := L) c)).toAdd - 0 = _
  rw [sub_zero, divisorClass_finiteNorm, hsource]

variable [Algebra C E] [IsScalarTower k C E] [Algebra.IsIntegral C E]
  [Algebra C L] [IsScalarTower k C L] [IsScalarTower C E L]
  [IsScalarTower C K L] [HasPrincipalDivisors C L]

omit [IsScalarTower k C E] in
/-- The same formula expressed as the actual norm between the two
constant-stage Picard groups. -/
theorem ofPic0_constantPointedDivisorClass_eq_normConstants
    (ε : Place C K) (hε : ε.deg = 1) (c : IdeleClassGroup k L)
    (x : Pic0 E L)
    (hc : picConstantEquiv k E L (divisorClass c).toAdd = H1Gm.ofPic0 E L x) :
    H1Gm.ofPic0 C K
        (constantPointedDivisorClass k C K ε hε
          (finiteNorm (k := k) (K := K) (L := L) c)).toAdd =
      Pic.normConstants C E K L (H1Gm.ofPic0 E L x) := by
  rw [ofPic0_constantPointedDivisorClass_finiteNorm ε hε c x hc,
    picConstantEquiv_normConstants]

end FunctionField.IdeleClassGroup
