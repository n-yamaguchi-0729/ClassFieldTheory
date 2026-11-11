/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Profinite.CompatibleSubgroupImages
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildGroup
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaContinuity
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildImage

/-!
# Exact finite images of the original normalization wild subgroup

The original wild subgroup is defined independently by the principal-unit
conditions at all finite normalizations. Its finite restrictions are onto the
original finite wild subgroups: compactness of the original inertia group and
the proved finite wild transition images supply compatible lifts. In
particular, the assertion is not inferred from pointwise choices of finite
lifts, and no replacement topology on the intrinsic finite groups is used.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The literal finite restriction of independently defined original wild
inertia has exactly the independently defined finite wild subgroup as image. -/
theorem actualNormalizationWildSubgroup_map
    (E : FiniteGaloisIntermediateField K L) :
    (actualNormalizationWildSubgroup A K L Q).map
        (actualFiniteInertiaRestriction A K L Q E).hom' =
      actualFiniteWildSubgroup A K L Q E := by
  have : (show Ideal (integralClosure A L) from Q).IsPrime :=
    inferInstanceAs Q.IsPrime
  have : CompactSpace (actualNormalizationInertiaGroup A K L Q).carrier :=
    actualNormalizationInertia_compactSpace A K L Q
  exact Subgroup.map_iInf_comap_of_locallyConstant
    (H := fun F : FiniteGaloisIntermediateField K L =>
      (actualFiniteStageInertiaGroup A K L Q F).carrier)
    (fun F => (actualFiniteInertiaRestriction A K L Q F).hom')
    (actualFiniteInertiaRestriction_isLocallyConstant A K L Q)
    (actualFiniteInertiaRestriction_surjective A K L Q)
    (fun F H hFH => (actualFiniteInertiaTowerRestriction A K L Q F H hFH).hom')
    (actualFiniteInertiaTowerRestriction_apply_restriction A K L Q)
    (actualFiniteWildSubgroup A K L Q)
    (actualFiniteWildSubgroup_map A K L Q) E

/-- Every original finite wild element lifts to the same absolute wild group,
with equality for the original restriction map. -/
theorem actualNormalizationWildRestriction_surjective
    (E : FiniteGaloisIntermediateField K L) :
    Function.Surjective (actualNormalizationWildRestriction A K L Q E).hom'.toFun := by
  intro τ
  have hτ : τ.val ∈ (actualNormalizationWildSubgroup A K L Q).map
      (actualFiniteInertiaRestriction A K L Q E).hom' := by
    rw [actualNormalizationWildSubgroup_map]
    exact τ.property
  obtain ⟨σ, hσ, hστ⟩ := hτ
  exact ⟨⟨σ, hσ⟩, Subtype.ext hστ⟩

end EtaleFundamentalGroups.Inertia
