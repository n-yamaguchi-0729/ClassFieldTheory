/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteNonabelianRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiltered
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilFiniteExtension
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-! # Norm quotients of finite Galois extensions of local fields -/

@[expose] public section

open scoped ValuativeRel

noncomputable section

namespace LocalClassFieldTheory.Universe

open FunctionField LocalFieldTheory ProCGroups.Abelian
open RamificationTheory.LocalField

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K)

omit [FiniteDimensional K L] in
private theorem ker_embeddedFiniteRestriction :
    (embeddedFiniteRestriction K L i).ker = i.fieldRange.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro h _ ⟨x, rfl⟩
    change σ (i x) = i x
    exact (embeddedFiniteRestriction_commutes K L i σ x).symm.trans
      (congrArg (fun τ : Gal(L/K) => i (τ x)) h)
  · intro h
    ext x
    apply i.injective
    change i (embeddedFiniteRestriction K L i σ x) = i x
    exact (embeddedFiniteRestriction_commutes K L i σ x).trans (h (i x) ⟨x, rfl⟩)

/-- The kernel of restriction on absolute abelianization is exactly the
image of the subgroup fixing the embedded extension. -/
theorem ker_abelianizedEmbeddedFiniteRestriction :
    (TopologicalAbelianization.map (embeddedFiniteRestrictionContinuous K L i)).ker =
      i.fieldRange.fixingSubgroup.map (TopologicalAbelianization.mk Gal(SeparableClosure K/K)) := by
  let G := Gal(SeparableClosure K/K)
  let r := embeddedFiniteRestriction K L i
  let p := TopologicalAbelianization.map (embeddedFiniteRestrictionContinuous K L i)
  ext z
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk G z
  change p (TopologicalAbelianization.mk G σ) = 1 ↔ _
  rw [TopologicalAbelianization.map_apply_mk]
  change TopologicalAbelianization.mk Gal(L/K) (r σ) = 1 ↔ _
  have hk (τ : Gal(L/K)) :
      TopologicalAbelianization.mk Gal(L/K) τ = 1 ↔ τ ∈ commutator Gal(L/K) := by
    rw [TopologicalAbelianization.mk_eq_one_iff]
    change τ ∈ (commutator Gal(L/K)).topologicalClosure ↔ _
    rw [commutator_topologicalClosure_eq]
  rw [hk]
  constructor
  · intro hσ
    have heq : (commutator G).map r = commutator Gal(L/K) :=
      map_commutator_of_surjective (embeddedFiniteRestriction_surjective K L i)
    rw [← heq] at hσ
    obtain ⟨τ, hτ, hrτ⟩ := hσ
    have hτq : TopologicalAbelianization.mk G τ = 1 :=
      TopologicalAbelianization.mk_eq_one_iff.mpr ((Subgroup.le_topologicalClosure _) hτ)
    refine ⟨τ⁻¹ * σ, ?_, ?_⟩
    · rw [← ker_embeddedFiniteRestriction K L i]
      apply MonoidHom.mem_ker.mpr
      change r (τ⁻¹ * σ) = 1
      rw [map_mul, map_inv, hrτ, inv_mul_cancel]
    · rw [map_mul, map_inv, hτq, inv_one, one_mul]
  · rintro ⟨τ, hτ, heq⟩
    have hrτ : r τ = 1 := MonoidHom.mem_ker.mp
      ((ker_embeddedFiniteRestriction K L i).symm ▸ hτ)
    have h := congrArg p heq
    rw [TopologicalAbelianization.map_apply_mk, TopologicalAbelianization.map_apply_mk] at h
    change TopologicalAbelianization.mk Gal(L/K) (r τ) =
      TopologicalAbelianization.mk Gal(L/K) (r σ) at h
    rw [hrτ, map_one] at h
    exact (hk (r σ)).mp h.symm

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Finite nonabelian reciprocity has the norm subgroup of the original
extension as its kernel. -/
theorem localArtinMapOfEmbedding_ker :
    (localArtinMapOfEmbedding K L i).ker = localNormSubgroup K L := by
  let H := localFiniteExtensionAbstractField K L i
  let N := localFixedFieldAbelianImage K H
  ext x
  change separableAbsoluteLocalArtinMap K x ∈
      (TopologicalAbelianization.map (embeddedFiniteRestrictionContinuous K L i)).ker ↔ _
  rw [ker_abelianizedEmbeddedFiniteRestriction]
  change separableAbsoluteLocalArtinMap K x ∈ N.toSubgroup ↔ x ∈ (normUnits K L).range
  rw [localFiniteExtension_norm_range_eq_maximalAbelian K L i]
  change separableAbsoluteLocalArtinMap K x ∈ N.toSubgroup ↔
    x ∈ localNormSubgroup K (absoluteFiniteQuotientField K N)
  rw [← absoluteFiniteArtinMap_ker K N, MonoidHom.mem_ker]
  change _ ↔ absoluteFiniteArtinMap K N x = 1
  exact (QuotientGroup.eq_one_iff _).symm.trans
    (Iff.of_eq (congrArg (· = 1) (separableAbsoluteLocalArtinMap_finiteProjection K N x)))

/-- Finite Galois reciprocity yields the unique continuous equivalence on
the original norm quotient with the actual Artin values. -/
theorem existsUnique_localArtinNormQuotientEquiv :
    ∃! e : (Kˣ ⧸ localNormSubgroup K L) ≃ₜ* TopologicalAbelianization Gal(L/K),
      ∀ x : Kˣ, e (QuotientGroup.mk' (localNormSubgroup K L) x) =
        localArtinMapOfEmbedding K L i x := by
  let : (localNormSubgroup K L).Normal := inferInstance
  let : DiscreteTopology (TopologicalAbelianization Gal(L/K)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  exact ProCGroups.QuotientGroup.existsUnique_quotientContinuousMulEquiv_of_surjective
    (localArtinMapOfEmbedding K L i) (localNormSubgroup K L)
    (localArtinMapOfEmbedding_surjective K L i) (localArtinMapOfEmbedding_ker K L i)

/-- The intrinsic Artin map has the norm subgroup as its kernel. -/
theorem localArtinMap_ker : (localArtinMap K L).ker = localNormSubgroup K L :=
  localArtinMapOfEmbedding_ker K L _

/-- The intrinsic Artin map identifies the norm quotient with finite
abelianization. -/
theorem existsUnique_localReciprocityEquiv :
    ∃! e : (Kˣ ⧸ localNormSubgroup K L) ≃ₜ* TopologicalAbelianization Gal(L/K),
      ∀ x : Kˣ, e (QuotientGroup.mk' (localNormSubgroup K L) x) = localArtinMap K L x :=
  existsUnique_localArtinNormQuotientEquiv K L _

private theorem separableLocalUpperRamificationGroup_map_embeddedFiniteRestriction (t : ℝ) :
    (separableLocalUpperRamificationGroup K t).map (embeddedFiniteRestriction K L i) =
      localUpperRamificationGroup K L t := by
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    i.finiteGaloisFieldRange
  let : FiniteDimensional K (↥E.toIntermediateField) := E.finiteDimensional
  let : Normal K (↥E.toIntermediateField) := E.isGalois.to_normal
  let : IsScalarTower K (↥E.toIntermediateField) (SeparableClosure K) :=
    E.toIntermediateField.isScalarTower_mid'
  let e := finiteGaloisFieldRangeEquivOfEmbedding K L i
  let r : Gal(SeparableClosure K/K) →* Gal(E/K) :=
    AlgEquiv.restrictNormalHom E.toIntermediateField
  let s : Gal(E/K) →* Gal(L/K) := (AlgEquiv.autCongr e).symm.toMonoidHom
  let G := separableLocalUpperRamificationGroup K t
  change G.map (s.comp r) = _
  have h : G.map r = localUpperRamificationGroup K E t :=
    separableLocalUpperRamificationGroup_map_restrict K t E
  let E₀ := ↥E.toIntermediateField
  let c : E₀ ≃ₐ[K] L := e.symm
  have ha := @localUpperRamificationGroup_map_autCongr K E₀ L
    ‹Field K› (inferInstanceAs (Field ↥E.toIntermediateField)) ‹Field L›
    E.toIntermediateField.toSubalgebra.algebra ‹Algebra K L›
    E.finiteDimensional ‹FiniteDimensional K L› E.isGalois ‹IsGalois K L›
    ‹ValuativeRel K› ‹TopologicalSpace K› ‹IsNonarchimedeanLocalField K› c t
  exact (Subgroup.map_map G s r).symm.trans ((congrArg (fun U => U.map s) h).trans ha)

/-- Artin sends principal units onto the upper group in the original finite Galois
abelianization, for an arbitrary finite Galois extension in independent universes. -/
theorem localArtinMap_fieldPrincipalUnits (t : ℝ) (ht : 0 ≤ t) :
    (fieldPrincipalUnits K ⌈t⌉₊).map (localArtinMap K L).toMonoidHom =
      (localUpperRamificationGroup K L t).map (TopologicalAbelianization.mk Gal(L/K)) := by
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  let p := TopologicalAbelianization.map (embeddedFiniteRestrictionContinuous K L i)
  let q := TopologicalAbelianization.mk Gal(L/K)
  let W := separableLocalUpperRamificationGroup K t
  have hp : p.toMonoidHom.comp (localAbsoluteAbelianizationQuotientMap K) =
      q.comp (embeddedFiniteRestriction K L i) :=
    TopologicalAbelianization.map_comp_mk (embeddedFiniteRestrictionContinuous K L i)
  let U := fieldPrincipalUnits K ⌈t⌉₊
  let a := (separableAbsoluteLocalArtinMap K).toMonoidHom
  let b := localAbsoluteAbelianizationQuotientMap K
  let r := embeddedFiniteRestriction K L i
  rw [localArtinMap_eq_ofEmbedding K L i]
  change U.map (p.toMonoidHom.comp a) = _
  calc
    U.map (p.toMonoidHom.comp a) = (U.map a).map p.toMonoidHom :=
      (Subgroup.map_map U p.toMonoidHom a).symm
    _ = (W.map b).map p.toMonoidHom :=
      congrArg (fun S => S.map p.toMonoidHom)
        (separableAbsoluteLocalArtinMap_fieldPrincipalUnits K t ht)
    _ = W.map (q.comp r) :=
      (Subgroup.map_map W p.toMonoidHom b).trans (congrArg (fun f => W.map f) hp)
    _ = (W.map r).map q := (Subgroup.map_map W q r).symm
    _ = _ := congrArg (fun S => S.map q)
      (separableLocalUpperRamificationGroup_map_embeddedFiniteRestriction K L i t)

end LocalClassFieldTheory.Universe
