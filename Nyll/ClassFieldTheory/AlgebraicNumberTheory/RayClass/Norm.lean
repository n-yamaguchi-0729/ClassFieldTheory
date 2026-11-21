/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces

/-!
# Norms between full ray class groups

The finite local norm inclusions and the inclusion of the real places above
the selected base places imply that the actual idèle norm preserves the ray
congruence conditions. Its existing map on idèle classes therefore descends
to the full ray class groups. No Galois or surjectivity hypothesis is used.
-/

@[expose] public section

open scoped BigOperators NumberField

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver
open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations

noncomputable section

universe u v

namespace RayClass

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Local conditions on full moduli for descent of the field norm. At every
finite place this is the stated local higher-unit inclusion. At infinity it
requires precisely the real places above the selected real base places. -/
def Modulus.NormCompatible (n : Modulus L) (m : Modulus K) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 K))
      (W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v}),
    let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (_root_.finitePlaceAdicCompletionMap K L v W).toAlgebra
    ClassFieldTheory.rayLocalHigherUnitGroup W.1 (n.finitePart W.1) ≤
      (ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v)).comap
        (LocalFieldTheory.normUnits (v.adicCompletion K)
          (W.1.adicCompletion L))) ∧
  (∀ (v : RealPlace K), v ∈ m.infinitePart →
    ∀ (W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v.1}) (hW : W.1.IsReal),
      (⟨W.1, hW⟩ : RealPlace L) ∈ n.infinitePart)

omit [NumberField K] [NumberField L] [Algebra K L] in
/-- The image of an archimedean positive unit under any multiplicative map
is positive: the source unit is a square, including at complex places. -/
private theorem map_mem_infinitePositiveSubgroup
    (v : InfinitePlace K) (W : InfinitePlace L)
    (f : W.Completionˣ →* v.Completionˣ)
    (x : W.Completionˣ) (hx : x ∈ infinitePositiveSubgroup W) :
    f x ∈ infinitePositiveSubgroup v := by
  obtain ⟨y, rfl⟩ := exists_infinitePositiveSubgroup_nthRoot W 2 (by decide) x hx
  rw [map_pow, mem_infinitePositiveSubgroup_iff]
  intro hv
  let e := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
  change 0 < e ((f y : v.Completion) ^ 2)
  rw [map_pow]
  apply sq_pos_of_ne_zero
  intro hz
  exact (f y).ne_zero (e.injective (hz.trans e.map_zero.symm))

/-- The finite part of the actual norm respects all higher-unit conditions,
by the product formula over the finite places above a base place. -/
theorem Modulus.NormCompatible.finite_norm_mem
    {n : Modulus L} {m : Modulus K} (h : n.NormCompatible m)
    (a : IdeleGroup L)
    (ha : IdeleGroup.finiteCoordinates a ∈ finiteCongruenceSubgroup n.finitePart) :
    IdeleGroup.finiteCoordinates (IdeleGroup.norm K L a) ∈
      finiteCongruenceSubgroup m.finitePart := by
  classical
  intro v
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial := adicAbv_isNontrivial v
  let eAbove := finitePlaceExtensionEquivAbove (K := K) (L := L) v
  let := completionTensorDecomposition_extensionFintype
    (K := K) (L := L) vK hvK
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v},
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    fun W => (_root_.finitePlaceAdicCompletionMap K L v W).toAlgebra
  change IdeleGroup.finiteComponent v (IdeleGroup.norm K L a) ∈
    ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v)
  rw [IdeleGroup.finiteComponent_norm_eq_prod]
  apply Subgroup.prod_mem
  intro W _
  exact h.1 v W (ha W.1)

/-- The infinite part of the actual norm is positive at every selected real
base place. Real factors use the imposed sign condition; complex factors
are automatically squares. -/
theorem Modulus.NormCompatible.infinite_norm_mem
    {n : Modulus L} {m : Modulus K} (h : n.NormCompatible m)
    (a : IdeleGroup L) (ha : (IdeleGroup.infinitePart a) ∈ n.infiniteCongruenceSubgroup) :
    (IdeleGroup.infinitePart (IdeleGroup.norm K L a)) ∈ m.infiniteCongruenceSubgroup := by
  classical
  rw [Modulus.mem_infiniteCongruenceSubgroup_iff]
  intro v hv
  let vK := v.1.1
  let hvK : vK.IsNontrivial := v.1.isNontrivial
  let eAbove := _root_.infinitePlaceAboveEquivExtension (K := K) (L := L) v.1
  let := completionTensorDecomposition_extensionFintype
    (K := K) (L := L) vK hvK
  let : Fintype {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v.1} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove.symm
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v.1}, W.1.1.LiesOver v.1.1 :=
    fun W => ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  change IdeleGroup.infiniteComponent v.1 (IdeleGroup.norm K L a) ∈
    infinitePositiveSubgroup v.1
  rw [IdeleGroup.infiniteComponent_norm_eq_prod]
  apply Subgroup.prod_mem
  intro W _
  apply map_mem_infinitePositiveSubgroup v.1 W.1
    (LocalFieldTheory.normUnits v.1.Completion W.1.Completion)
  rw [mem_infinitePositiveSubgroup_iff]
  intro hW
  exact (Modulus.mem_infiniteCongruenceSubgroup_iff n (IdeleGroup.infinitePart a)).mp ha
    ⟨W.1, hW⟩ (h.2 v hv W hW) hW

/-- Local finite and real conditions imply the actual idèle norm inclusion. -/
theorem Modulus.NormCompatible.ideleCongruenceSubgroup_le
    {n : Modulus L} {m : Modulus K} (h : n.NormCompatible m) :
    n.ideleCongruenceSubgroup ≤
      m.ideleCongruenceSubgroup.comap (IdeleGroup.norm K L) := by
  intro a ha
  exact ⟨h.infinite_norm_mem a ha.1, h.finite_norm_mem a ha.2⟩

/-- The existing norm on idèle classes preserves the full ray subgroups. -/
theorem Modulus.NormCompatible.congruenceSubgroup_le
    {n : Modulus L} {m : Modulus K} (h : n.NormCompatible m) :
    n.congruenceSubgroup ≤ m.congruenceSubgroup.comap (ideleClassNorm K L) := by
  rw [Modulus.congruenceSubgroup, Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    change ideleClassNorm K L
        (IdeleGroup.toStandardClass L a) ∈ m.congruenceSubgroup
    rw [ideleClassNorm_mk]
    exact Subgroup.mem_map.mpr
      ⟨IdeleGroup.norm K L a, Subgroup.mem_sup_left (h.ideleCongruenceSubgroup_le ha), rfl⟩
  · intro a ha
    change ideleClassNorm K L
        (IdeleGroup.toStandardClass L a) ∈ m.congruenceSubgroup
    have hzero : IdeleGroup.toStandardClass L a = 1 :=
      (IdeleGroup.toStandardClass_eq_one_iff L a).mpr ha
    rw [hzero, map_one]
    exact m.congruenceSubgroup.one_mem

/-- The norm on full ray class groups, induced directly by the actual
idèle-class norm. -/
noncomputable def rayClassNorm {n : Modulus L} {m : Modulus K}
    (h : n.NormCompatible m) : RayClassGroup n →* RayClassGroup m :=
  QuotientGroup.map n.congruenceSubgroup m.congruenceSubgroup
    (ideleClassNorm K L) h.congruenceSubgroup_le

@[simp]
theorem rayClassNorm_mk {n : Modulus L} {m : Modulus K}
    (h : n.NormCompatible m) (c : NumberField.IdeleClassGroup (𝓞 L) L) :
    rayClassNorm h (QuotientGroup.mk' n.congruenceSubgroup c) =
      QuotientGroup.mk' m.congruenceSubgroup (ideleClassNorm K L c) :=
  rfl

/-- Evaluation on an actual idèle representative. -/
@[simp]
theorem rayClassNorm_mk_idele {n : Modulus L} {m : Modulus K}
    (h : n.NormCompatible m) (a : IdeleGroup L) :
    rayClassNorm h (QuotientGroup.mk' n.congruenceSubgroup
        (IdeleGroup.toStandardClass L a)) =
      QuotientGroup.mk' m.congruenceSubgroup
        (IdeleGroup.toStandardClass K (IdeleGroup.norm K L a)) := by
  rw [rayClassNorm_mk, ideleClassNorm_mk]

end RayClass
