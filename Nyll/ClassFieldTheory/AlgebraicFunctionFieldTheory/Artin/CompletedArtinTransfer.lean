/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.EmbeddedArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteReciprocity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTopology
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion

/-!
# Completed reciprocity and the original absolute transfer

The continuous completion of actual idele-class inclusion intertwines
profinite reciprocity with the independently constructed native Galois transfer.
The equality follows from the absolute Artin equality on the dense image of
the original idele-class group. The Galois transfer is not defined through
the reciprocity isomorphisms.
-/

@[expose] public section

universe u v w x

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k : Type u) (K : Type v) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Completed reciprocity intertwines actual fixed-field inclusion with the
original absolute transfer, using the same separable-closure equivalence as
the uncompleted Artin comparison. -/
theorem profiniteReciprocity_baseChange_nativeTransfer
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).toSubalgebra.algebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    let inclusion : IdeleClassGroup k K →ₜ* IdeleClassGroup k F :=
      { toMonoidHom := IdeleClassGroup.baseChange (k := k) (K := K) (L := F)
        continuous_toFun := IdeleClassGroup.continuous_baseChange
          (k := k) (K := K) (L := F) }
    (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k F)).comp
        (topologicalProfiniteCompletionMapHom inclusion) =
      (nativeAbsoluteTransferOfFixedField K H e).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k K)) := by
  intro F aFsep e akΩ aRΩ hkKΩ hRKΩ hkRΩ hKF inclusion
  let left : TopologicalProfiniteCompletion (IdeleClassGroup k K) →ₜ*
      localAbsoluteAbelianProfinite F :=
    (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k F)).comp
      (topologicalProfiniteCompletionMapHom inclusion)
  let right : TopologicalProfiniteCompletion (IdeleClassGroup k K) →ₜ*
      localAbsoluteAbelianProfinite F :=
    (nativeAbsoluteTransferOfFixedField K H e).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k K))
  have hleft (c : IdeleClassGroup k K) :
      left (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c) =
        absoluteArtin k F (inclusion c) :=
    (congrArg (fun a => profiniteReciprocity k F a)
      (topologicalProfiniteCompletionMapHom_map inclusion c)).trans
        (profiniteReciprocity_map k F (inclusion c))
  have hright (c : IdeleClassGroup k K) :
      right (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c) =
        nativeAbsoluteTransferOfFixedField K H e (absoluteArtin k K c) :=
    congrArg (nativeAbsoluteTransferOfFixedField K H e) (profiniteReciprocity_map k K c)
  have hbase (c : IdeleClassGroup k K) :
      absoluteArtin k F (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c) =
        nativeAbsoluteTransferOfFixedField K H e (absoluteArtin k K c) := by
    have h := absoluteArtin_baseChange_nativeTransfer k K H e c
    with_reducible exact h
  have hinc (c : IdeleClassGroup k K) :
      inclusion c = IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c :=
    rfl
  have hagree (c : IdeleClassGroup k K) :
      left (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c) =
        right (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c) :=
    (hleft c).trans ((congrArg (absoluteArtin k F) (hinc c)).trans
      ((hbase c).trans (hright c).symm))
  have heq := (topologicalProfiniteCompletionMap_denseRange (IdeleClassGroup k K)).equalizer
    left.continuous_toFun right.continuous_toFun (funext hagree)
  exact ContinuousMonoidHom.ext (fun a => congrFun heq a)

section EmbeddedTransfer

variable (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra k L] [IsScalarTower k K L]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The completed inclusion square for the original, independently presented
upper field and the native transfer constructed from its actual embedding. -/
theorem profiniteReciprocity_baseChange_transferOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    let inclusion : IdeleClassGroup k K →ₜ* IdeleClassGroup k L :=
      { toMonoidHom := IdeleClassGroup.baseChange (k := k) (K := K) (L := L)
        continuous_toFun := IdeleClassGroup.continuous_baseChange }
    (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k L)).comp
        (topologicalProfiniteCompletionMapHom inclusion) =
      (nativeAbsoluteTransferOfEmbedding K L i).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k K)) := by
  intro inclusion
  let left := (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k L)).comp
    (topologicalProfiniteCompletionMapHom inclusion)
  let right := (nativeAbsoluteTransferOfEmbedding K L i).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (profiniteReciprocity k K))
  have heq := (topologicalProfiniteCompletionMap_denseRange (IdeleClassGroup k K)).equalizer
    left.continuous_toFun right.continuous_toFun (show
      (fun c => left (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c)) =
        (fun c => right (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c)) from by
      funext c
      change profiniteReciprocity k L
          (topologicalProfiniteCompletionMapHom inclusion
            (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c)) =
        nativeAbsoluteTransferOfEmbedding K L i
          (profiniteReciprocity k K
            (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c))
      rw [topologicalProfiniteCompletionMapHom_map,
        profiniteReciprocity_map, profiniteReciprocity_map]
      exact absoluteArtin_baseChange_transferOfEmbedding K L i k c)
  exact ContinuousMonoidHom.ext (fun a => congrFun heq a)

/-- Every finite projection retains the actual upper-field Artin coordinate
on the original idele classes. -/
theorem nativeAbsoluteTransferOfEmbedding_finiteProjection
    (i : L →ₐ[K] SeparableClosure K)
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite L)) (c : IdeleClassGroup k K) :
    (QuotientGroup.mk (nativeAbsoluteTransferOfEmbedding K L i (absoluteArtin k K c)) :
        localAbsoluteAbelianProfinite L ⧸ N.toSubgroup) =
      absoluteFiniteArtinCoordinate k L N
        (IdeleClassGroup.baseChange (k := k) (K := K) (L := L) c) := by
  rw [← absoluteArtin_baseChange_transferOfEmbedding K L i k c]
  exact absoluteArtin_finiteProjection k L N _

/-- The finite projections of the completed transfer square are the continuous
extensions of those same native Artin coordinates. -/
theorem profiniteReciprocity_transferOfEmbedding_finiteProjection
    (i : L →ₐ[K] SeparableClosure K)
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite L))
    (a : TopologicalProfiniteCompletion (IdeleClassGroup k K)) :
    let inclusion : IdeleClassGroup k K →ₜ* IdeleClassGroup k L :=
      { toMonoidHom := IdeleClassGroup.baseChange (k := k) (K := K) (L := L)
        continuous_toFun := IdeleClassGroup.continuous_baseChange }
    (QuotientGroup.mk (nativeAbsoluteTransferOfEmbedding K L i (profiniteReciprocity k K a)) :
        localAbsoluteAbelianProfinite L ⧸ N.toSubgroup) =
      topologicalProfiniteCompletionLift
        ((localAbsoluteAbelianProfinite L).diagram.obj N)
        (absoluteFiniteArtinCoordinate k L N)
        (topologicalProfiniteCompletionMapHom inclusion a) := by
  intro inclusion
  have h := DFunLike.congr_fun
    (profiniteReciprocity_baseChange_transferOfEmbedding k K L i) a
  change profiniteReciprocity k L (topologicalProfiniteCompletionMapHom inclusion a) =
    nativeAbsoluteTransferOfEmbedding K L i (profiniteReciprocity k K a) at h
  rw [← h]
  exact completedArtin_finiteProjection k L N _

include k in
/-- The original native transfer is independent of the embedding used to
realize the finite extension in the lower separable closure. -/
theorem nativeAbsoluteTransferOfEmbedding_eq
    (i j : L →ₐ[K] SeparableClosure K) :
    nativeAbsoluteTransferOfEmbedding K L i = nativeAbsoluteTransferOfEmbedding K L j := by
  have heq := (absoluteArtin_denseRange k K).equalizer
    (nativeAbsoluteTransferOfEmbedding K L i).continuous_toFun
    (nativeAbsoluteTransferOfEmbedding K L j).continuous_toFun (show
      (fun c => nativeAbsoluteTransferOfEmbedding K L i (absoluteArtin k K c)) =
        (fun c => nativeAbsoluteTransferOfEmbedding K L j (absoluteArtin k K c)) from by
      funext c
      rw [← absoluteArtin_baseChange_transferOfEmbedding K L i k c,
        ← absoluteArtin_baseChange_transferOfEmbedding K L j k c])
  exact ContinuousMonoidHom.ext (fun a => congrFun heq a)

section Tower

variable (M : Type x) [Field M]
    [Algebra k M] [Algebra K M] [Algebra L M]
    [IsScalarTower k K M] [IsScalarTower k L M] [IsScalarTower K L M]
    [FiniteDimensional K M] [FiniteDimensional L M] [IsGalois K M] [IsGalois L M]
    [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M] [FunctionField k M]
    [AlgebraicCurve.HasPrincipalDivisors k M]

include k in
/-- Native transfers compose along an actual finite Galois tower. The three
closure embeddings may be chosen independently: reciprocity and its dense
image prove the law for the already constructed group transfers. -/
theorem nativeAbsoluteTransferOfEmbedding_comp
    (i : L →ₐ[K] SeparableClosure K) (j : M →ₐ[L] SeparableClosure L)
    (t : M →ₐ[K] SeparableClosure K) :
    (nativeAbsoluteTransferOfEmbedding L M j).comp
        (nativeAbsoluteTransferOfEmbedding K L i) =
      nativeAbsoluteTransferOfEmbedding K M t := by
  let left := (nativeAbsoluteTransferOfEmbedding L M j).comp
    (nativeAbsoluteTransferOfEmbedding K L i)
  let right := nativeAbsoluteTransferOfEmbedding K M t
  have heq := (absoluteArtin_denseRange k K).equalizer
    left.continuous_toFun right.continuous_toFun (show
      (fun c => left (absoluteArtin k K c)) =
        (fun c => right (absoluteArtin k K c)) from by
      funext c
      change nativeAbsoluteTransferOfEmbedding L M j
          (nativeAbsoluteTransferOfEmbedding K L i (absoluteArtin k K c)) =
        nativeAbsoluteTransferOfEmbedding K M t (absoluteArtin k K c)
      rw [← absoluteArtin_baseChange_transferOfEmbedding K L i k c,
        ← absoluteArtin_baseChange_transferOfEmbedding L M j k,
        IdeleClassGroup.baseChange_trans,
        absoluteArtin_baseChange_transferOfEmbedding K M t k c])
  exact ContinuousMonoidHom.ext (fun a => congrFun heq a)

end Tower

end EmbeddedTransfer

include k in
/-- Native transfer along the identity extension is literally the identity
of the original absolute abelian group. -/
theorem nativeAbsoluteTransferOfEmbedding_self
    (i : K →ₐ[K] SeparableClosure K) :
    nativeAbsoluteTransferOfEmbedding K K i =
      ContinuousMonoidHom.id (localAbsoluteAbelianProfinite K) := by
  have heq := (absoluteArtin_denseRange k K).equalizer
    (nativeAbsoluteTransferOfEmbedding K K i).continuous_toFun continuous_id (show
      (fun c => nativeAbsoluteTransferOfEmbedding K K i (absoluteArtin k K c)) =
        (fun c => absoluteArtin k K c) from by
      funext c
      rw [← absoluteArtin_baseChange_transferOfEmbedding K K i k c,
        IdeleClassGroup.baseChange_self])
  exact ContinuousMonoidHom.ext (fun a => congrFun heq a)

end FunctionField
