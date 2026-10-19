/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalFactor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalRestriction

/-!
# Restriction of the one-place Artin factor

The factor through a completed local Artin map commutes with restriction
of the upper finite abelian extension. Both sides are evaluated on an
actual local preimage; the already proved local and global restriction
laws then identify their values.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place
open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

namespace FunctionField

variable {k K L M : Type} [Field k] [Finite k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower k L M]
    [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- Restriction of the actual decomposition automorphism commutes with the
one-place global Artin factor. -/
theorem localGlobalArtinFactor_restrictNormal (u : Place k M)
    (τ : IdeleGroup.decompositionGroup (K := K) u)
    (σ : IdeleGroup.decompositionGroup (K := K) (u.restrict L))
    (hτσ : AlgEquiv.restrictNormalHom L τ.1 = σ.1) :
    localGlobalArtinFactor (u.restrict L) σ =
      AlgEquiv.restrictNormalHom L (localGlobalArtinFactor u τ) := by
  obtain ⟨b, hb⟩ := localDecompositionArtin_surjective (K := K) u τ
  have hbτ : localArtin (K := K) u b = τ.1 := congrArg Subtype.val hb
  have hKL : (u.restrict L).restrict K = u.restrict K :=
    restrict_restrict (F := K) (E := L) u
  let bL : ((u.restrict L).restrict K).adicCompletionˣ := hKL.symm ▸ b
  have hbL : localArtin (K := K) (u.restrict L) bL = σ.1 :=
    (localArtin_restrictNormal (K := K) (L := L) u b).symm.trans
      ((congrArg (AlgEquiv.restrictNormalHom L) hbτ).trans hτσ)
  have hbLD : localDecompositionArtin (K := K) (u.restrict L) bL = σ := Subtype.ext hbL
  have hplace : IdeleGroup.placeIdele ((u.restrict L).restrict K) bL =
      IdeleGroup.placeIdele (u.restrict K) b := by
    have transport (v v' : Place k K) (h : v = v') (z : v.adicCompletionˣ) :
        IdeleGroup.placeIdele v' (h ▸ z) = IdeleGroup.placeIdele v z := by
      subst v'
      rfl
    exact transport (u.restrict K) ((u.restrict L).restrict K) hKL.symm b
  have hupper : localGlobalArtinFactor u τ = abelianFiniteArtin k K M
      (QuotientGroup.mk (IdeleGroup.placeIdele (u.restrict K) b)) := by
    rw [← hb]
    exact localGlobalArtinFactor_apply_localDecompositionArtin u b
  calc
    localGlobalArtinFactor (u.restrict L) σ = abelianFiniteArtin k K L
        (QuotientGroup.mk (IdeleGroup.placeIdele ((u.restrict L).restrict K) bL)) := by
      rw [← hbLD]
      exact localGlobalArtinFactor_apply_localDecompositionArtin (u.restrict L) bL
    _ = abelianFiniteArtin k K L
        (QuotientGroup.mk (IdeleGroup.placeIdele (u.restrict K) b)) :=
      congrArg (fun z : IdeleGroup k K => abelianFiniteArtin k K L (QuotientGroup.mk z)) hplace
    _ = AlgEquiv.restrictNormalHom L (abelianFiniteArtin k K M
        (QuotientGroup.mk (IdeleGroup.placeIdele (u.restrict K) b))) :=
      (abelianFiniteArtin_restrictNormal k K L M _).symm
    _ = AlgEquiv.restrictNormalHom L (localGlobalArtinFactor u τ) :=
      congrArg (AlgEquiv.restrictNormalHom L) hupper.symm

end FunctionField
