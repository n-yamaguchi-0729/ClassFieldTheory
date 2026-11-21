/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Norm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNorm
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

/-!
# Full ray norms on ideal representatives

The comparison uses the common subgroup of ideals avoiding both the upstairs
modulus support and the primes above the downstairs support. Local norm
compatibility alone does not imply an inclusion of these supports.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain
open GlobalClassFieldTheory.GlobalClassFields

noncomputable section

universe u v

namespace RayClass

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The common ideal domain required for comparison with a full ray norm. -/
def rayClassNormIdealDomain (n : Modulus L) (m : Modulus K) :
    Subgroup (ClassFieldTheory.NumberFieldFractionalIdealGroup L) :=
  primeToModulusIdeals n ⊓ primeToModulusIdealNormDomain (L := L) m

/-- Enlarging the modulus strengthens the conditions on prime-to ideles. -/
theorem idelePrimeToModulusSubgroup_antitone
    {m n : Modulus K} (hmn : m ≤ n) :
    idelePrimeToModulusSubgroup n ≤ idelePrimeToModulusSubgroup m := by
  intro a ha
  refine ⟨Modulus.infiniteCongruenceSubgroup_antitone hmn ha.1, ?_⟩
  intro v hv
  exact ClassFieldTheory.rayLocalHigherUnitGroup_antitone v (hmn.1 v)
    (ha.2 v (Finsupp.support_mono hmn.1 hv))

variable [FiniteDimensional K L]

/-- The actual ray norm on an ideal representative equals the ordinary
ideal norm, on the common support domain. The lifted modulus is used only
to choose a representative in the proof; it does not define the domain. -/
theorem rayClassNorm_idealRepresentative
    {n : Modulus L} {m : Modulus K} (h : n.NormCompatible m)
    (I : rayClassNormIdealDomain n m) :
    rayClassGroupEquivIdealRayClassGroup m
        (rayClassNorm h ((rayClassGroupEquivIdealRayClassGroup n).symm
          (QuotientGroup.mk' (principalRayIdealSubgroup n)
            ⟨I.1, I.2.1⟩))) =
      QuotientGroup.mk' (principalRayIdealSubgroup m)
        (primeToModulusIdealNorm m ⟨I.1, I.2.2⟩) := by
  classical
  let r := n ⊔ idealNormLiftedModulus (K := K) (L := L) m
  have hIr : I.1 ∈ primeToModulusIdeals r := by
    intro W hW
    change W ∈ (n.finitePart ⊔
      (idealNormLiftedModulus (K := K) (L := L) m).finitePart).support at hW
    rw [Finsupp.support_sup, Finset.mem_union] at hW
    rcases hW with hW | hW
    · exact I.2.1 W hW
    · exact I.2.2 W ((mem_idealNormLiftedModulus_support_iff m W).mp hW)
  obtain ⟨a, haI⟩ := primeToIdealMap_surjective r ⟨I.1, hIr⟩
  have hI : IdeleGroup.fractionalIdeal (a : IdeleGroup L) = I.1 :=
    congrArg Subtype.val haI
  let an : idelePrimeToModulusSubgroup n :=
    ⟨a, idelePrimeToModulusSubgroup_antitone
      (show n ≤ r from le_sup_left) a.2⟩
  let alift : idelePrimeToModulusSubgroup
      (idealNormLiftedModulus (K := K) (L := L) m) :=
    ⟨a, idelePrimeToModulusSubgroup_antitone
      (show idealNormLiftedModulus (K := K) (L := L) m ≤ r from le_sup_right) a.2⟩
  let b : idelePrimeToModulusSubgroup m :=
    ⟨IdeleGroup.norm K L a,
      h.infinite_norm_mem a an.2.1,
      finite_norm_mem_finitePrimeToModulusSubgroup m alift⟩
  have hn : primeToIdealMap n an = ⟨I.1, I.2.1⟩ :=
    Subtype.ext hI
  have hm : primeToIdealMap m b = primeToModulusIdealNorm m ⟨I.1, I.2.2⟩ := by
    apply Subtype.ext
    change IdeleGroup.fractionalIdeal (IdeleGroup.norm K L (a : IdeleGroup L)) =
      ClassFieldTheory.fractionalIdealNorm K L I.1
    rw [IdeleGroup.fractionalIdeal_ideleNorm, hI]
  have hnclass :
      rayClassGroupEquivIdealRayClassGroup n
          (QuotientGroup.mk' n.congruenceSubgroup
            (IdeleGroup.toStandardClass L (a : IdeleGroup L))) =
        QuotientGroup.mk' (principalRayIdealSubgroup n) ⟨I.1, I.2.1⟩ := by
    rw [RayClass.rayClassGroupEquivIdealRayClassGroup_mk_primeTo n an]
    exact congrArg (QuotientGroup.mk' (principalRayIdealSubgroup n)) hn
  rw [← hnclass, MulEquiv.symm_apply_apply, rayClassNorm_mk_idele]
  rw [RayClass.rayClassGroupEquivIdealRayClassGroup_mk_primeTo m b]
  exact congrArg (QuotientGroup.mk' (principalRayIdealSubgroup m)) hm

omit [FiniteDimensional K L] in
/-- An explicit support inclusion extends the comparison domain to all
ideals prime to the upstairs modulus. This conclusion is independent of
the local higher-unit norm conditions. -/
theorem rayClassNormIdealDomain_eq_of_support
    (n : Modulus L) (m : Modulus K)
    (hsupport : ∀ W : HeightOneSpectrum (𝓞 L),
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support →
        W ∈ n.finitePart.support) :
    rayClassNormIdealDomain n m = primeToModulusIdeals n := by
  apply inf_eq_left.mpr
  intro I hI W hW
  exact hI W (hsupport W hW)

end RayClass

namespace ClassFieldTheory.GlobalClassFieldComparison

/-- The public-to-original ideal ray comparison preserves every ideal
representative, not just the classes of individual primes. -/
@[simp]
theorem rayClassGroupEquivOriginal_mk
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (I : rayClassPrimeToIdeals m) :
    rayClassGroupEquivOriginal K m
        (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) I) =
      QuotientGroup.mk'
        (RayClass.principalRayIdealSubgroup (rayClassModulusToOriginal K m)) I :=
  rfl

end ClassFieldTheory.GlobalClassFieldComparison

namespace ClassFieldTheory

open GlobalClassFieldComparison

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- On the common ideal domain, the full idelic ray norm is the existing
public ideal norm, under the canonical ray-class comparisons. -/
theorem rayClassNorm_eq_rayClassIdealNorm
    (n : RayClassModulus L) (m : RayClassModulus K)
    (h : (rayClassModulusToOriginal L n).NormCompatible
      (rayClassModulusToOriginal K m))
    (I : RayClass.rayClassNormIdealDomain
      (rayClassModulusToOriginal L n) (rayClassModulusToOriginal K m)) :
    RayClass.rayClassNorm h
        (rayClassGroupEquivOriginalIdele L n
          (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo n) ⟨I.1, I.2.1⟩)) =
      rayClassGroupEquivOriginalIdele K m
        (rayClassIdealNorm K L m ⟨I.1, I.2.2⟩) := by
  let m₀ := rayClassModulusToOriginal K m
  let n₀ := rayClassModulusToOriginal L n
  let eK := RayClass.rayClassGroupEquivIdealRayClassGroup m₀
  let eL := RayClass.rayClassGroupEquivIdealRayClassGroup n₀
  let A : rayClassPrimeToIdeals n := ⟨I.1, I.2.1⟩
  let B : rayClassPrimeToIdealNormDomain K L m := ⟨I.1, I.2.2⟩
  let x := QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo n) A
  let y := rayClassIdealNorm K L m B
  let a := rayClassGroupEquivOriginal L n x
  let b := rayClassGroupEquivOriginal K m y
  apply eK.injective
  change eK (RayClass.rayClassNorm h (eL.symm a)) = eK (eK.symm b)
  calc
    _ = eK (RayClass.rayClassNorm h (eL.symm
          (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup n₀) A))) :=
      congrArg
        (fun c : RayClass.IdealRayClassGroup n₀ => eK (RayClass.rayClassNorm h (eL.symm c)))
        (rayClassGroupEquivOriginal_mk L n A)
    _ = QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m₀)
          (RayClass.primeToModulusIdealNorm m₀ B) :=
      RayClass.rayClassNorm_idealRepresentative h I
    _ = b := (rayClassGroupEquivOriginal_mk K m (rayClassPrimeToIdealNorm K L m B)).symm
    _ = _ := (eK.apply_symm_apply b).symm


end ClassFieldTheory
