/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.IntermediateFieldRingEquivOrderIso
public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupRingEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkLocalClassification
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Local class-field classification under base and closure equivalences

Finite fields are transported by the image of the specified closure map.
The ordinary field-norm comparison gives the classification square, and
injectivity of the existing classification proves closure-choice independence.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

variable {K : Type u} {M : Type v} [Field K] [Field M]

namespace FiniteAbelianLocalExtension

/-- The actual image of a finite abelian intermediate field under the
specified compatible equivalence of separable closures. -/
def mapBaseEquiv (e : K ≃+* M)
    (c : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a))
    (E : FiniteAbelianLocalExtension K) : FiniteAbelianLocalExtension M :=
  ⟨intermediateFieldMapRingEquiv e c hc E.1,
    Module.Finite.of_equiv_equiv e
      (intermediateFieldMapRingEquivEquiv e c hc E.1)
      (intermediateFieldMapRingEquivEquiv_commutes e c hc E.1),
    isAbelianGalois_of_equiv_equiv e
      (intermediateFieldMapRingEquivEquiv e c hc E.1)
      (intermediateFieldMapRingEquivEquiv_commutes e c hc E.1)⟩

/-- Finite abelian fields are order-isomorphic under the specified base and
ambient equivalences. The two inverses are the actual inverse image maps. -/
def baseEquivOrderIso (e : K ≃+* M)
    (c : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a)) :
    FiniteAbelianLocalExtension K ≃o FiniteAbelianLocalExtension M where
  toFun := mapBaseEquiv e c hc
  invFun := mapBaseEquiv e.symm c.symm
    (intermediateFieldMapRingEquiv_symm_commutes e c hc)
  left_inv E := Subtype.ext ((intermediateFieldRingEquivOrderIso e c hc).left_inv E.1)
  right_inv E := Subtype.ext ((intermediateFieldRingEquivOrderIso e c hc).right_inv E.1)
  map_rel_iff' := by
    intro E F
    exact (intermediateFieldRingEquivOrderIso e c hc).le_iff_le

/-- Norms of the actual transported field are the image of the original
norms under the given base-field equivalence. -/
theorem mapBaseEquiv_normSubgroup (e : K ≃+* M)
    (c : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a))
    (E : FiniteAbelianLocalExtension K) :
    E.normSubgroup.map (Units.mapEquiv e.toMulEquiv).toMonoidHom =
      (mapBaseEquiv e c hc E).normSubgroup := by
  let : FiniteDimensional M (intermediateFieldMapRingEquiv e c hc E.1) :=
    (mapBaseEquiv e c hc E).2.1
  change (fieldNormSubgroup K E.1).map
      (Units.mapEquiv e.toMulEquiv).toMonoidHom =
    fieldNormSubgroup M (intermediateFieldMapRingEquiv e c hc E.1)
  exact fieldNormSubgroup_map_ringEquiv e
    (intermediateFieldMapRingEquivEquiv e c hc E.1)
    (intermediateFieldMapRingEquivEquiv_commutes e c hc E.1)

end FiniteAbelianLocalExtension

namespace OpenFiniteIndexSubgroup

variable [TopologicalSpace K] [TopologicalSpace M]

/-- The image of an open finite-index subgroup under an actual topological
isomorphism of unit groups. -/
def mapContinuousMulEquiv (e : Kˣ ≃ₜ* Mˣ)
    (H : OpenFiniteIndexSubgroup K) : OpenFiniteIndexSubgroup M :=
  ⟨H.1.map e.toMonoidHom, by
    change IsOpen (e '' (H.1 : Set Kˣ))
    exact e.toHomeomorph.isOpenMap _ H.2.1, by
    let : H.1.FiniteIndex := H.2.2
    exact Subgroup.FiniteIndex.map_of_surjective H.1 e.surjective⟩

end OpenFiniteIndexSubgroup

end ClassFieldTheory

namespace LocalFieldTheory

universe u v

variable {K : Type u} {M : Type v} [Field K] [Field M]

open ClassFieldTheory

section TopologicalBaseChange

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]

/-- Classification is natural for the actual transported field and actual
image subgroup under a topological base-field equivalence. -/
theorem shrinkFiniteAbelianFieldNormSubgroupOrderIso_mapBaseEquiv
    (e : K ≃+* M) (he : Continuous e) (he' : Continuous e.symm)
    (c : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a))
    (E : FiniteAbelianLocalExtension K) :
    let eu : Kˣ ≃ₜ* Mˣ := Units.mapContinuousMulEquiv
      { toMulEquiv := e.toMulEquiv, continuous_toFun := he, continuous_invFun := he' }
    shrinkFiniteAbelianFieldNormSubgroupOrderIso M
        (FiniteAbelianLocalExtension.mapBaseEquiv e c hc E) =
      OrderDual.toDual (OpenFiniteIndexSubgroup.mapContinuousMulEquiv eu
        (OrderDual.ofDual (shrinkFiniteAbelianFieldNormSubgroupOrderIso K E))) := by
  intro eu
  apply Subtype.ext
  change (OrderDual.ofDual (shrinkFiniteAbelianFieldNormSubgroupOrderIso M
      (FiniteAbelianLocalExtension.mapBaseEquiv e c hc E))).1 =
    (OrderDual.ofDual (shrinkFiniteAbelianFieldNormSubgroupOrderIso K E)).1.map
      (Units.mapEquiv e.toMulEquiv).toMonoidHom
  rw [shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply,
    shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply]
  exact (FiniteAbelianLocalExtension.mapBaseEquiv_normSubgroup e c hc E).symm

/-- The inverse class-field construction commutes with the same actual
base/closure transport; the subgroup is mapped by its given unit isomorphism. -/
theorem shrinkFiniteAbelianFieldNormSubgroupOrderIso_symm_mapBaseEquiv
    (e : K ≃+* M) (he : Continuous e) (he' : Continuous e.symm)
    (c : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a))
    (H : OpenFiniteIndexSubgroup K) :
    let eu : Kˣ ≃ₜ* Mˣ := Units.mapContinuousMulEquiv
      { toMulEquiv := e.toMulEquiv, continuous_toFun := he, continuous_invFun := he' }
    (shrinkFiniteAbelianFieldNormSubgroupOrderIso M).symm
        (OrderDual.toDual (OpenFiniteIndexSubgroup.mapContinuousMulEquiv eu H)) =
      FiniteAbelianLocalExtension.mapBaseEquiv e c hc
        ((shrinkFiniteAbelianFieldNormSubgroupOrderIso K).symm (OrderDual.toDual H)) := by
  intro eu
  apply (shrinkFiniteAbelianFieldNormSubgroupOrderIso M).injective
  rw [(shrinkFiniteAbelianFieldNormSubgroupOrderIso M).apply_symm_apply]
  rw [shrinkFiniteAbelianFieldNormSubgroupOrderIso_mapBaseEquiv e he he' c hc]
  rw [(shrinkFiniteAbelianFieldNormSubgroupOrderIso K).apply_symm_apply]
  rfl

end TopologicalBaseChange

variable [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]

/-- Different compatible equivalences between the chosen closures give
exactly the same finite abelian intermediate field. This follows from the
existing norm-classification injection, not from an arbitrary field isomorphism. -/
theorem finiteAbelianLocalExtension_mapBaseEquiv_independent
    (e : K ≃+* M)
    (c d : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a))
    (hd : ∀ a : K, d (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a))
    (E : FiniteAbelianLocalExtension K) :
    FiniteAbelianLocalExtension.mapBaseEquiv e c hc E =
      FiniteAbelianLocalExtension.mapBaseEquiv e d hd E := by
  apply (shrinkFiniteAbelianFieldNormSubgroupOrderIso M).injective
  apply Subtype.ext
  change (OrderDual.ofDual (shrinkFiniteAbelianFieldNormSubgroupOrderIso M
      (FiniteAbelianLocalExtension.mapBaseEquiv e c hc E))).1 =
    (OrderDual.ofDual (shrinkFiniteAbelianFieldNormSubgroupOrderIso M
      (FiniteAbelianLocalExtension.mapBaseEquiv e d hd E))).1
  rw [shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply,
    shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply]
  exact (FiniteAbelianLocalExtension.mapBaseEquiv_normSubgroup e c hc E).symm.trans
    (FiniteAbelianLocalExtension.mapBaseEquiv_normSubgroup e d hd E)

end LocalFieldTheory
