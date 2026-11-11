/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.ActualWildFiniteImages
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaContinuity
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildProperties
public import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationGaloisFaithful
public import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup

/-!
# Characteristic-primary elements in actual finite field restrictions

The original finite wild group is a normal p-group of prime-to-p index.
Its elements are therefore exactly the elements killed by a p-power.
Faithfulness of the actual finite normalization action carries this
criterion to the original finite Galois group. Exact finite wild lifting
then characterizes the image of the independently defined absolute wild
group, through its original field restriction.
-/

@[expose] public section

noncomputable section

namespace Subgroup

/-- A normal p-subgroup of prime-to-p index consists exactly of the
elements killed by a p-power. The index power and coprimality give the
reverse inclusion directly inside the original group. -/
theorem mem_iff_prime_pow_eq_one_of_normal
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (hindex : ¬ p ∣ P.index) (g : G) :
    g ∈ P ↔ ∃ r : ℕ, g ^ (p ^ r) = 1 := by
  constructor
  · intro hg
    obtain ⟨r, hr⟩ := hP ⟨g, hg⟩
    exact ⟨r, congrArg Subtype.val hr⟩
  · rintro ⟨r, hr⟩
    have hprime : p.Coprime P.index := by
      by_contra hcoprime
      exact hindex ((Fact.out : p.Prime).dvd_iff_not_coprime.mpr hcoprime)
    have hcoprime : P.index.Coprime (orderOf g) :=
      (hprime.symm.pow_right r).coprime_dvd_right (orderOf_dvd_of_pow_eq_one hr)
    obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcoprime
    exact hs ▸ P.pow_mem (P.pow_index_mem g) s

end Subgroup

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The prescribed finite wild subgroup is exactly the characteristic-primary
part of its original intrinsic finite inertia group. -/
theorem mem_actualFiniteWildSubgroup_iff_prime_pow_eq_one
    (E : FiniteGaloisIntermediateField K L)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (g : (actualFiniteStageInertiaGroup A K L Q E).carrier) :
    g ∈ actualFiniteWildSubgroup A K L Q E ↔
      ∃ r : ℕ, g ^ (p ^ r) = 1 := by
  have : (actualFiniteWildSubgroup A K L Q E).Normal :=
    actualFiniteWildSubgroup_normal A K L Q E
  exact Subgroup.mem_iff_prime_pow_eq_one_of_normal p
    (actualFiniteWildSubgroup A K L Q E)
    (actualFiniteWildSubgroup_isPGroup_of_baseResidue_charP A K L Q E p)
    (actualFiniteWildSubgroup_index_not_dvd_of_baseResidue_charP A K L Q E p) g

/-- The actual finite field restriction of original wild inertia consists
exactly of the characteristic-primary elements in the actual inertia image.
The equality is proved through the original coefficient restriction and its
proved faithfulness; no finite wild-image condition is an input. -/
theorem mem_actualNormalizationWildSubgroup_field_image_iff
    (E : FiniteGaloisIntermediateField K L)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (g : (finiteGaloisGroupObject K L E).carrier) :
    g ∈ (actualNormalizationWildSubgroup A K L Q).map
        ((finiteGaloisRestrictionGroupMap K L E).hom'.comp
          (actualNormalizationInertiaInclusion A K L Q).hom') ↔
      g ∈ (Q.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom E) ∧
        ∃ r : ℕ, g ^ (p ^ r) = 1 := by
  let r : (actualNormalizationInertiaGroup A K L Q).carrier →*
      (finiteGaloisGroupObject K L E).carrier :=
    (finiteGaloisRestrictionGroupMap K L E).hom'.comp
      (actualNormalizationInertiaInclusion A K L Q).hom'
  let c := (finiteNormalizationGaloisGroupMap A K L E).hom'
  let f := (actualFiniteInertiaRestriction A K L Q E).hom'
  have hcoeff (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
      (f σ).val = c (r σ) :=
    actualFiniteInertiaRestriction_coefficient A K L Q E σ
  have hc : Function.Injective c := finiteNormalizationGaloisGroupMap_injective A K L E
  change g ∈ (actualNormalizationWildSubgroup A K L Q).map r ↔ _
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have hw : f σ ∈ actualFiniteWildSubgroup A K L Q E := by
      rw [← actualNormalizationWildSubgroup_map A K L Q E]
      exact ⟨σ, hσ, rfl⟩
    obtain ⟨n, hn⟩ :=
      (mem_actualFiniteWildSubgroup_iff_prime_pow_eq_one A K L Q E p (f σ)).mp hw
    refine ⟨⟨σ.val, σ.property, rfl⟩, n, ?_⟩
    apply hc
    rw [map_pow, map_one]
    have h := congrArg Subtype.val hn
    change (f σ).val ^ (p ^ n) = 1 at h
    rwa [hcoeff σ] at h
  · rintro ⟨⟨σ, hσ, rfl⟩, n, hn⟩
    let ι : (actualNormalizationInertiaGroup A K L Q).carrier := ⟨σ, hσ⟩
    have hpower : f ι ^ (p ^ n) = 1 := by
      apply Subtype.ext
      change (f ι).val ^ (p ^ n) = 1
      have hn' : r ι ^ (p ^ n) = 1 := hn
      exact (congrArg (fun y => y ^ (p ^ n)) (hcoeff ι)).trans
        ((map_pow c (r ι) (p ^ n)).symm.trans
          ((congrArg c hn').trans (map_one c)))
    have hw : f ι ∈ actualFiniteWildSubgroup A K L Q E :=
      (mem_actualFiniteWildSubgroup_iff_prime_pow_eq_one A K L Q E p (f ι)).mpr
        ⟨n, hpower⟩
    have hlift : f ι ∈ (actualNormalizationWildSubgroup A K L Q).map f := by
      rw [actualNormalizationWildSubgroup_map A K L Q E]
      exact hw
    obtain ⟨τ, hτ, hτι⟩ := hlift
    refine ⟨τ, hτ, ?_⟩
    apply hc
    exact (hcoeff τ).symm.trans ((congrArg Subtype.val hτι).trans (hcoeff ι))

end EtaleFundamentalGroups.Inertia
