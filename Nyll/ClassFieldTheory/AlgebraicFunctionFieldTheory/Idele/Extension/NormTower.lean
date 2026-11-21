/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNormCore
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Topology.DenseEmbedding
public import Nyll.AlgebraicCurves.Places.Completion
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegExchange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
public import Nyll.AlgebraicCurves.Places.Basic

/-!
# Transitivity of all-place idele norms

The completion maps form the actual scalar tower: their composites agree on the
original dense subfield. Field-norm transitivity then applies locally. The finite
fiber above a base place is the disjoint union of the fibers above its intermediate
places, so the local identities multiply to the idele norm tower law.
-/

@[expose] public section

open scoped AlgebraicCurve.Place

noncomputable section

namespace FunctionField

namespace IdeleGroup

section CompletionComparison

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

theorem localNormOver_eq_norm (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L) (hw : w.restrict K = v) (x : w.adicCompletionˣ) :
    let _ : Algebra v.adicCompletion w.adicCompletion :=
      (AlgebraicCurve.Place.completionMapOver v w hw).toAlgebra
    localNormOver v w hw x = Units.map (Algebra.norm v.adicCompletion) x := by
  subst v
  rfl

end CompletionComparison

section Tower

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M]

section Local

variable [FiniteDimensional K M]

/-- Local norms compose along the actual completed extension tower. The three
place equalities specify only the points of the fiber, not a norm comparison. -/
theorem localNormOver_trans (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L) (u : AlgebraicCurve.Place k M)
    (hw : w.restrict K = v) (hu : u.restrict L = w) (huv : u.restrict K = v)
    (x : u.adicCompletionˣ) :
    localNormOver v w hw (localNormOver w u hu x) = localNormOver v u huv x := by
  let aKL : Algebra v.adicCompletion w.adicCompletion :=
    (AlgebraicCurve.Place.completionMapOver v w hw).toAlgebra
  let aLM : Algebra w.adicCompletion u.adicCompletion :=
    (AlgebraicCurve.Place.completionMapOver w u hu).toAlgebra
  let aKM : Algebra v.adicCompletion u.adicCompletion :=
    (AlgebraicCurve.Place.completionMapOver v u huv).toAlgebra
  have htower : IsScalarTower v.adicCompletion w.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq fun y =>
      (congrArg (fun f : v.adicCompletion →+* u.adicCompletion => f y)
        (AlgebraicCurve.Place.completionMapOver_trans v w u hw hu huv)).symm
  have hKL (y : w.adicCompletionˣ) : localNormOver v w hw y =
      Units.map (Algebra.norm v.adicCompletion) y := localNormOver_eq_norm v w hw y
  have hLM : localNormOver w u hu x = Units.map (Algebra.norm w.adicCompletion) x :=
    localNormOver_eq_norm w u hu x
  have hKM : localNormOver v u huv x = Units.map (Algebra.norm v.adicCompletion) x :=
    localNormOver_eq_norm v u huv x
  rw [hKL, hLM, hKM]
  apply Units.ext
  exact Algebra.norm_norm (R := v.adicCompletion) (S := w.adicCompletion)
    (a := (x : u.adicCompletion))

end Local

section FiniteFibers

variable [FiniteDimensional K M]

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

/-- An extending place has exactly one intermediate restricted place. This gives
an equivalence of the actual finite fibers, without choosing extending places. -/
private def fiberTowerEquiv (v : AlgebraicCurve.Place k K) :
    (Σ w : v.fiberOver L, w.1.fiberOver M) ≃ v.fiberOver M where
  toFun p := ⟨p.2.1, (AlgebraicCurve.Place.mem_fiberOver v).mpr
    ((restrict_restrict (F := K) (E := L) p.2.1).symm.trans
      ((congrArg (fun w : AlgebraicCurve.Place k L => w.restrict K)
        ((AlgebraicCurve.Place.mem_fiberOver p.1.1).mp p.2.2)).trans
        ((AlgebraicCurve.Place.mem_fiberOver v).mp p.1.2)))⟩
  invFun u := ⟨⟨u.1.restrict L, (AlgebraicCurve.Place.mem_fiberOver v).mpr
    ((restrict_restrict (F := K) (E := L) u.1).trans
      ((AlgebraicCurve.Place.mem_fiberOver v).mp u.2))⟩,
    ⟨u.1, AlgebraicCurve.Place.restrict_mem_fiberOver u.1⟩⟩
  left_inv := by
    rintro ⟨⟨w, hw⟩, ⟨u, hu⟩⟩
    have h : u.restrict L = w := (AlgebraicCurve.Place.mem_fiberOver w).mp hu
    subst w
    rfl
  right_inv u := Subtype.ext rfl

end FiniteFibers

/-- Norm in a finite tower equals the composite of the two idele norms. -/
theorem norm_trans (a : IdeleGroup k M) :
    let _ : FiniteDimensional K M := Module.Finite.trans L M
    norm (k := k) (K := K) (L := L) (norm (k := k) (K := L) (L := M) a) =
      norm (k := k) (K := K) (L := M) a := by
  intro hfinite
  classical
  apply RestrictedProduct.ext
  intro v
  let e : (Σ w : v.fiberOver L, w.1.fiberOver M) ≃ v.fiberOver M :=
    fiberTowerEquiv (L := L) v
  change normComponent (k := k) (K := K) (L := L) v
      (norm (K := L) (L := M) a) = normComponent (k := k) (K := K) (L := M) v a
  rw [normComponent_apply, normComponent_apply]
  calc
    (∏ w : v.fiberOver L, localNormOver v w.1
        ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2) ((norm (K := L) (L := M) a) w.1)) =
        ∏ w : v.fiberOver L, ∏ u : w.1.fiberOver M,
          localNormOver v (e ⟨w, u⟩).1
            ((AlgebraicCurve.Place.mem_fiberOver v).mp (e ⟨w, u⟩).2) (a (e ⟨w, u⟩).1) := by
      apply Finset.prod_congr rfl
      intro w _
      change localNormOver v w.1 ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2)
        (normComponent (k := k) (K := L) (L := M) w.1 a) = _
      rw [normComponent_apply, map_prod]
      apply Finset.prod_congr rfl
      intro u _
      exact localNormOver_trans v w.1 u.1
        ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2)
        ((AlgebraicCurve.Place.mem_fiberOver w.1).mp u.2)
        ((AlgebraicCurve.Place.mem_fiberOver v).mp (e ⟨w, u⟩).2) (a u.1)
    _ = ∏ u : v.fiberOver M,
        localNormOver v u.1 ((AlgebraicCurve.Place.mem_fiberOver v).mp u.2) (a u.1) := by
      rw [Finset.prod_sigma', Finset.univ_sigma_univ]
      exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end Tower

end IdeleGroup

namespace IdeleClassGroup

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [AlgebraicCurve.HasPrincipalDivisors k M]

/-- The single quotient construction respects every finite tower, independently
of which arithmetic proofs establish preservation of principal ideles. -/
theorem normOfPrincipal_trans [FiniteDimensional K M]
    (hKL : IdeleGroup.principalSubgroup k L ≤
      (IdeleGroup.principalSubgroup k K).comap (IdeleGroup.norm (K := K) (L := L)))
    (hLM : IdeleGroup.principalSubgroup k M ≤
      (IdeleGroup.principalSubgroup k L).comap (IdeleGroup.norm (K := L) (L := M)))
    (hKM : IdeleGroup.principalSubgroup k M ≤
      (IdeleGroup.principalSubgroup k K).comap (IdeleGroup.norm (K := K) (L := M)))
    (c : IdeleClassGroup k M) :
    normOfPrincipal hKL (normOfPrincipal hLM c) = normOfPrincipal hKM c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := M) c
  change normOfPrincipal hKL (normOfPrincipal hLM (QuotientGroup.mk a)) =
    normOfPrincipal hKM (QuotientGroup.mk a)
  rw [normOfPrincipal_mk hLM a, normOfPrincipal_mk hKL, normOfPrincipal_mk hKM a]
  exact congrArg (mk (k := k) (K := K))
    (IdeleGroup.norm_trans (k := k) (K := K) (L := L) (M := M) a)

variable [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

/-- The same tower law holds after quotienting by the actual principal ideles. -/
theorem norm_trans (c : IdeleClassGroup k M) :
    let _ : FiniteDimensional K M := Module.Finite.trans L M
    let _ : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    norm (k := k) (K := K) (L := L) (norm (k := k) (K := L) (L := M) c) =
      norm (k := k) (K := K) (L := M) c := by
  intro hfinite hseparable
  exact normOfPrincipal_trans (k := k) (K := K) (L := L) (M := M)
    (fun _ ha => IdeleGroup.norm_mem_principalSubgroup ha)
    (fun _ ha => IdeleGroup.norm_mem_principalSubgroup ha)
    (fun _ ha => IdeleGroup.norm_mem_principalSubgroup ha) c

end IdeleClassGroup

end FunctionField
