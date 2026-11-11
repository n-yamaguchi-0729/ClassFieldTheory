/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.ProC.LocallyConstantResidualCore
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildProP
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaContinuity
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildProperties
public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualPrimeExclusion
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Original wild inertia is intrinsic in every continuous inertia image

The independently defined wild subgroup is the existing prime-to-p
residual core of the original normalization inertia group. One inclusion
uses its proved pro-p structure. For the other, the original finite
inertia restrictions followed by their actual tame quotients detect all
finite wild conditions. These locally constant maps need no replacement
topology on the finite normalization groups.

The continuous image theorem for the residual core then reconstructs the
original wild image from the original inertia image. Consequently, a
continuous ambient map carrying one actual inertia image onto another
also carries their actual wild images onto each other.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory ProCGroups

universe u v w u' v'

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

/-- The native wild subgroup, defined independently through all actual
finite principal-unit conditions, is the prime-to-p residual core of the
original inertia group with its original topology. -/
theorem actualNormalizationWildSubgroup_eq_primeToResidualCore :
    actualNormalizationWildSubgroup A K L Q =
      ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ))
        (actualNormalizationInertiaGroup A K L Q).carrier := by
  apply le_antisymm
  · exact ProC.subgroup_le_sigmaResidualCore_of_proP p
      (not_not.mpr (Set.mem_singleton p))
      (actualNormalizationWildSubgroup A K L Q)
      (actualNormalizationWildGroup_hasPGroupOpenNormalBasis A K L Q p)
  · intro σ hσ
    apply (mem_actualNormalizationWildSubgroup A K L Q σ).mpr
    intro E
    have : (actualFiniteWildSubgroup A K L Q E).Normal :=
      actualFiniteWildSubgroup_normal A K L Q E
    have : Finite (actualFiniteStageInertiaGroup A K L Q E).carrier :=
      actualFiniteStageInertiaGroup_finite A K L Q E
    let f : (actualNormalizationInertiaGroup A K L Q).carrier →*
        (actualFiniteStageInertiaGroup A K L Q E).carrier ⧸
          actualFiniteWildSubgroup A K L Q E :=
      (QuotientGroup.mk' (actualFiniteWildSubgroup A K L Q E)).comp
        (actualFiniteInertiaRestriction A K L Q E).hom'
    have hf : IsLocallyConstant f :=
      (actualFiniteInertiaRestriction_isLocallyConstant A K L Q E).comp
        (QuotientGroup.mk' (actualFiniteWildSubgroup A K L Q E))
    have htame : FiniteGroupClass.sigmaGroup ({p}ᶜ)
        ((actualFiniteStageInertiaGroup A K L Q E).carrier ⧸
          actualFiniteWildSubgroup A K L Q E) := by
      refine ⟨inferInstance, ?_⟩
      intro q _ hq hdiv
      have hqp : q = p := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hq
      subst q
      exact actualFiniteWildSubgroup_index_not_dvd_of_baseResidue_charP
        A K L Q E p hdiv
    have hkernel := ProC.proCResidualCore_le_ker_of_locallyConstant_finite
      (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ)) f hf htame
    exact (QuotientGroup.eq_one_iff
      (N := actualFiniteWildSubgroup A K L Q E)
      ((actualFiniteInertiaRestriction A K L Q E).hom' σ)).mp (hkernel hσ)

section Images

variable {H : Type w} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H]

/-- Every continuous image of original wild inertia is the prime-to-p
residual core of the literal original inertia image, included through its
actual subgroup inclusion. This also applies before abelianization. -/
theorem actualNormalizationWildSubgroup_map_eq_rangeResidualCore
    (f : (actualNormalizationInertiaGroup A K L Q).carrier →ₜ* H) :
    (actualNormalizationWildSubgroup A K L Q).map f.toMonoidHom =
      (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ))
        f.toMonoidHom.range).map f.toMonoidHom.range.subtype := by
  have : CompactSpace (actualNormalizationInertiaGroup A K L Q).carrier :=
    actualNormalizationInertia_compactSpace A K L Q
  rw [actualNormalizationWildSubgroup_eq_primeToResidualCore A K L Q p]
  exact ProC.map_proCResidualCore_eq_rangeCore
    (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ)) f

variable (A' : Type u') (K' : Type v') (L' : Type w)
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Field K'] [Field L'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L'] [IsGalois K' L']
    (Q' : Ideal (normalizationCommAlgCat A' L').carrier) [Q'.IsMaximal]
    [CharP (IsLocalRing.ResidueField A') p]

include p

/-- Equal original inertia images have equal original wild images in the
same residue characteristic, including for different original DVRs and
different original Galois extensions. -/
theorem actualNormalizationWildSubgroup_map_eq_of_inertiaRange_eq
    (f : (actualNormalizationInertiaGroup A K L Q).carrier →ₜ* H)
    (g : (actualNormalizationInertiaGroup A' K' L' Q').carrier →ₜ* H)
    (hI : f.toMonoidHom.range = g.toMonoidHom.range) :
    (actualNormalizationWildSubgroup A K L Q).map f.toMonoidHom =
      (actualNormalizationWildSubgroup A' K' L' Q').map g.toMonoidHom := by
  have h := congrArg
    (fun I : Subgroup H =>
      (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ)) I).map I.subtype) hI
  exact (actualNormalizationWildSubgroup_map_eq_rangeResidualCore A K L Q p f).trans
    (h.trans
      (actualNormalizationWildSubgroup_map_eq_rangeResidualCore A' K' L' Q' p g).symm)

variable {H' : Type w} [Group H'] [TopologicalSpace H']
    [IsTopologicalGroup H'] [T2Space H']

omit [IsTopologicalGroup H] [T2Space H] in
/-- An original continuous ambient map preserving the actual inertia
images necessarily preserves the actual wild images. Wild preservation
is a consequence of the proved intrinsic characterization. -/
theorem actualNormalizationWildSubgroup_map_map_eq_of_inertiaRange_map
    (f : (actualNormalizationInertiaGroup A K L Q).carrier →ₜ* H)
    (g : (actualNormalizationInertiaGroup A' K' L' Q').carrier →ₜ* H')
    (e : H →ₜ* H')
    (hI : f.toMonoidHom.range.map e.toMonoidHom = g.toMonoidHom.range) :
    ((actualNormalizationWildSubgroup A K L Q).map f.toMonoidHom).map
        e.toMonoidHom =
      (actualNormalizationWildSubgroup A' K' L' Q').map g.toMonoidHom := by
  rw [Subgroup.map_map]
  apply actualNormalizationWildSubgroup_map_eq_of_inertiaRange_eq
    A K L Q p A' K' L' Q' (e.comp f) g
  exact (MonoidHom.range_comp e.toMonoidHom f.toMonoidHom).trans hI

end Images

end EtaleFundamentalGroups.Inertia
