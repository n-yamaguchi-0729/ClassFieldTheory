/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower

/-!
# Functoriality of idele inclusion

The actual completion maps compose because they agree on the dense original
field. Their componentwise inclusions therefore compose on ideles and on idele
classes. The identity law follows from this composition law and injectivity of
idele inclusion, without identifying completions by definitional equality.
-/

open scoped AlgebraicCurve.Place

noncomputable section

namespace FunctionField

namespace IdeleGroup

section CompletionComparison

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- A completion map over a specified base place computes the corresponding
component of idele inclusion. -/
theorem completionMapOver_apply_baseChange (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L) (hw : w.restrict K = v) (a : IdeleGroup k K) :
    completionMapOver v w hw (a v : v.adicCompletion) =
      (baseChange (k := k) (K := K) (L := L) a w : w.adicCompletion) := by
  subst v
  rfl

end CompletionComparison

section Tower

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]

/-- The completion maps compose along a finite field tower. The equalities
record only the restrictions of the three places. -/
theorem completionMapOver_trans (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L) (u : AlgebraicCurve.Place k M)
    (hw : w.restrict K = v) (hu : u.restrict L = w) (huv : u.restrict K = v) :
    (completionMapOver w u hu).comp (completionMapOver v w hw) =
      completionMapOver v u huv := by
  have hdense : DenseRange (algebraMap K v.adicCompletion) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v.heightOneSpectrum
  have hfun : (fun x => completionMapOver w u hu (completionMapOver v w hw x)) =
      completionMapOver v u huv :=
    hdense.equalizer
      ((continuous_completionMapOver w u hu).comp (continuous_completionMapOver v w hw))
      (continuous_completionMapOver v u huv) (by
        funext x
        simp only [Function.comp_apply, completionMapOver_algebraMap]
        rw [← IsScalarTower.algebraMap_apply K L M])
  exact RingHom.ext (fun x => congrFun hfun x)

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

/-- Inclusion through an intermediate finite extension equals direct
inclusion into the top field. -/
@[simp]
theorem baseChange_trans (a : IdeleGroup k K) :
    baseChange (k := k) (K := L) (L := M)
        (baseChange (k := k) (K := K) (L := L) a) =
      baseChange (k := k) (K := K) (L := M) a := by
  apply RestrictedProduct.ext
  intro u
  apply Units.ext
  have hu : u.restrict K = (u.restrict L).restrict K :=
    (restrict_restrict (F := K) (E := L) u).symm
  have h := congrArg
    (fun f : ((u.restrict L).restrict K).adicCompletion →+* u.adicCompletion =>
      f (a ((u.restrict L).restrict K)))
    (completionMapOver_trans ((u.restrict L).restrict K) (u.restrict L) u rfl rfl hu)
  simpa only [RingHom.comp_apply, completionMapOver_apply_baseChange] using h

/-- The idele inclusion homomorphisms compose in finite towers. -/
theorem baseChange_comp_baseChange :
    (baseChange (k := k) (K := L) (L := M)).comp
        (baseChange (k := k) (K := K) (L := L)) =
      baseChange (k := k) (K := K) (L := M) := by
  apply MonoidHom.ext
  intro a
  exact baseChange_trans (k := k) (K := K) (L := L) (M := M) a

end Tower

section Identity

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Inclusion along the identity field extension fixes every idele. -/
@[simp]
theorem baseChange_self (a : IdeleGroup k K) :
    baseChange (k := k) (K := K) (L := K) a = a := by
  apply baseChange_injective (k := k) (K := K) (L := K)
  exact baseChange_trans (k := k) (K := K) (L := K) (M := K) a

/-- The idele inclusion of the identity extension is the identity homomorphism. -/
@[simp]
theorem baseChange_self_eq_id :
    baseChange (k := k) (K := K) (L := K) = MonoidHom.id (IdeleGroup k K) := by
  apply MonoidHom.ext
  intro a
  exact baseChange_self a

end Identity

end IdeleGroup

namespace IdeleClassGroup

section Tower

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [AlgebraicCurve.HasPrincipalDivisors k M]

/-- The tower law for inclusion descends to the actual quotient by principal
ideles. -/
@[simp]
theorem baseChange_trans (c : IdeleClassGroup k K) :
    baseChange (k := k) (K := L) (L := M)
        (baseChange (k := k) (K := K) (L := L) c) =
      baseChange (k := k) (K := K) (L := M) c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  simp only [baseChange_mk, IdeleGroup.baseChange_trans]

/-- The induced homomorphisms on idele classes compose along field towers. -/
theorem baseChange_comp_baseChange :
    (baseChange (k := k) (K := L) (L := M)).comp
        (baseChange (k := k) (K := K) (L := L)) =
      baseChange (k := k) (K := K) (L := M) := by
  apply MonoidHom.ext
  intro c
  exact baseChange_trans (k := k) (K := K) (L := L) (M := M) c

end Tower

section Identity

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Inclusion along the identity extension fixes every idele class. -/
@[simp]
theorem baseChange_self (c : IdeleClassGroup k K) :
    baseChange (k := k) (K := K) (L := K) c = c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  simp only [baseChange_mk, IdeleGroup.baseChange_self]

/-- The inclusion of idele classes along the identity extension is the identity
homomorphism. -/
@[simp]
theorem baseChange_self_eq_id :
    baseChange (k := k) (K := K) (L := K) = MonoidHom.id (IdeleClassGroup k K) := by
  apply MonoidHom.ext
  intro c
  exact baseChange_self c

end Identity

end IdeleClassGroup

end FunctionField
