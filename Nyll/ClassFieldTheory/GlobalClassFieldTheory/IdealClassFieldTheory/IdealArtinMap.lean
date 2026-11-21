/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNormCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Nyll.ValuedFieldTheory.LocalField.NormUnits

/-!
# The ideal-theoretic Artin map

Let `N ≤ C_K` be a class-field norm subgroup and let `m` be a defining
modulus, so `C_K^m ≤ N`.  The idelic quotient map then factors through the
ideal ray class group.  Composing with the projection from ideals prime to
`m` gives the ideal-theoretic Artin map.  This file proves its surjectivity,
identifies its kernel, and records the exact sequence.

The target is kept as the concrete reciprocity quotient `C_K / N`; global
reciprocity identifies this quotient with the corresponding abelian Galois
group.
-/



@[expose] public section

universe u v w

open scoped NumberField BigOperators

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

variable {K : Type u} [Field K] [NumberField K]


local instance ideleClassSubgroupNormal
    (N : Subgroup (IdeleClassGroup K)) : N.Normal :=
  N.normal_of_isMulCommutative

/-- The quotient map from the ray class group modulo a defining modulus
to the class-field reciprocity quotient. -/
def rayClassToNormQuotient
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.RayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup m) N
    (MonoidHom.id (IdeleClassGroup K)) hm

/-- The ray-class quotient map sends the class of an idele class to its
class modulo the norm subgroup. -/
@[simp]
theorem rayClassToNormQuotient_mk
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (c : IdeleClassGroup K) :
    rayClassToNormQuotient m N hm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c) =
      QuotientGroup.mk' N c :=
  rfl

/-- The quotient map attached to a defining modulus is surjective. -/
theorem rayClassToNormQuotient_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Function.Surjective
      (rayClassToNormQuotient m N hm) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro c
  exact
    ⟨QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c, rfl⟩

/-- The Artin map on the ideal ray class group, obtained from the
idele-theoretic reciprocity quotient. -/
def idealRayClassArtinMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.IdealRayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  (rayClassToNormQuotient m N hm).comp
    (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.toMonoidHom

/-- The ideal-ray-class Artin map is surjective. -/
theorem idealRayClassArtinMap_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Function.Surjective
      (idealRayClassArtinMap m N hm) := by
  exact
    (rayClassToNormQuotient_surjective m N hm).comp
      (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.surjective

/-- The Artin map on fractional ideals prime to `m`. -/
def idealArtinMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.primeToModulusIdeals m →*
      IdeleClassGroup K ⧸ N :=
  (idealRayClassArtinMap m N hm).comp
    (QuotientGroup.mk'
      (RayClass.principalRayIdealSubgroup m))

/-- The ideal Artin map of the fractional ideal attached to a
prime-to-modulus idèle is its class in the idèle-class quotient. -/
@[simp]
theorem idealArtinMap_primeToIdealMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    idealArtinMap m N hm
        (RayClass.primeToIdealMap m a) =
      QuotientGroup.mk' N
        (IdeleGroup.toStandardClass K
          (a : IdeleGroup K)) := by
  let e :=
    RayClass.rayClassGroupEquivIdealRayClassGroup m
  let c : RayClass.RayClassGroup m :=
    QuotientGroup.mk'
      (RayClass.Modulus.congruenceSubgroup m)
      (IdeleGroup.toStandardClass K
        (a : IdeleGroup K))
  have he :
      e c = RayClass.idealRayProjection m a := by
    exact
      RayClass.rayClassGroupEquivIdealRayClassGroup_mk_primeTo m a
  have he' :
      e.symm (RayClass.idealRayProjection m a) = c := by
    rw [← he, e.symm_apply_apply]
  change
    rayClassToNormQuotient m N hm
        (e.symm (RayClass.idealRayProjection m a)) =
      QuotientGroup.mk' N
        (IdeleGroup.toStandardClass K
          (a : IdeleGroup K))
  rw [he', rayClassToNormQuotient_mk]

/-- The ideal group `H_m` attached to `N`: precisely the ideals whose
Artin class is trivial. -/
def idealArtinKernel
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Subgroup (RayClass.primeToModulusIdeals m) :=
  (idealArtinMap m N hm).ker

/-- Principal ray ideals lie in the Artin kernel. -/
theorem principalRayIdealSubgroup_le_idealArtinKernel
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.principalRayIdealSubgroup m ≤
      idealArtinKernel m N hm := by
  intro a ha
  change
    idealRayClassArtinMap m N hm
        (QuotientGroup.mk'
          (RayClass.principalRayIdealSubgroup m) a) =
      1
  have hqa :
      QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m) a = 1 :=
    (QuotientGroup.eq_one_iff a).2 ha
  rw [hqa, map_one]

section NormDefinedFiniteKernel

variable
    {L : Type v} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- For choosing idèle representatives of ideal norms, retain the finite
part of the ideal-norm lifted modulus and impose positivity at every real
place upstairs.  Its prime-to ideal group is definitionally the same as the
one for `idealNormLiftedModulus`, while positivity makes its idèle norm
prime to the selected infinite part downstairs. -/
noncomputable def normIdeleLiftedModulus
    (m : RayClass.Modulus K) : RayClass.Modulus L :=
  RayClass.Modulus.narrowOfFinite
    (RayClass.idealNormLiftedModulus
      (K := K) (L := L) m).finitePart

private theorem ideleNorm_mem_finitePrimeToModulusSubgroup_aux
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup
      (normIdeleLiftedModulus (K := K) (L := L) m)) :
    IdeleGroup.finiteCoordinates (IdeleGroup.norm K L (a : IdeleGroup L)) ∈
      RayClass.finitePrimeToModulusSubgroup m := by
  let aFinite :
      RayClass.idelePrimeToModulusSubgroup
        (RayClass.idealNormLiftedModulus (K := K) (L := L) m) :=
    ⟨(a : IdeleGroup L), by
      constructor
      · apply
          (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff
            (RayClass.idealNormLiftedModulus
              (K := K) (L := L) m) _).2
        intro v hv
        have hNoInfinite :
            (RayClass.idealNormLiftedModulus
              (K := K) (L := L) m).infinitePart = ∅ :=
          rfl
        rw [hNoInfinite] at hv
        exact (Finset.notMem_empty _ hv).elim
      · exact a.property.2⟩
  exact
    RayClass.finite_norm_mem_finitePrimeToModulusSubgroup
      (K := K) (L := L) m aFinite

/-- The idèle norm carries idèles prime to the lifted modulus to
idèles prime to the base modulus.  At real places this uses positivity
of both real-real and complex-real local norms. -/
theorem ideleNorm_mem_idelePrimeToModulusSubgroup
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup
      (normIdeleLiftedModulus
        (K := K) (L := L) m)) :
    IdeleGroup.norm K L (a : IdeleGroup L) ∈
      RayClass.idelePrimeToModulusSubgroup m := by
  classical
  constructor
  · apply
      (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff m
        (IdeleGroup.infinitePart (IdeleGroup.norm K L (a : IdeleGroup L)))).2
    intro v _hv
    let : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v.1},
        W.1.1.LiesOver v.1.1 :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    have hNormComponent :
        IdeleGroup.infiniteComponent v.1
            (IdeleGroup.norm K L (a : IdeleGroup L)) ∈
          RayClass.infinitePositiveSubgroup v.1 := by
      rw [IdeleGroup.infiniteComponent_norm_eq_prod]
      apply Subgroup.prod_mem
      intro W _hW
      apply
        (RayClass.mem_infinitePositiveSubgroup_iff v.1
          (LocalFieldTheory.normUnits
            v.1.Completion W.1.Completion
            (IdeleGroup.infiniteComponent W.1
              (a : IdeleGroup L)))).2
      intro hvReal
      have hbelow :
          W.1.comap (algebraMap K L) = v.1 := by
        simpa only [_root_.infinitePlaceBelow] using W.2
      rcases W.1.isReal_or_isComplex with hWReal | hWComplex
      · have hUpstairs :
            0 <
              InfinitePlace.Completion.ringEquivRealOfIsReal
                hWReal
              (IdeleGroup.infiniteComponent W.1
                  (a : IdeleGroup L) :
                  W.1.Completion) := by
          have hPositive :=
            (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff
              (normIdeleLiftedModulus
                (K := K) (L := L) m)
              (IdeleGroup.infinitePart (a : IdeleGroup L))).1 a.property.1
                ⟨W.1, hWReal⟩ (by exact Finset.mem_univ _)
          exact
            (RayClass.mem_infinitePositiveSubgroup_iff W.1
              (IdeleGroup.infiniteComponent W.1
                (a : IdeleGroup L))).1 hPositive hWReal
        have hNorm :=
          Reciprocity.infinitePlace_normUnits_real_real
            (K := K) (K' := L) v.1 W.1 hbelow
              hvReal hWReal
              (IdeleGroup.infiniteComponent W.1
                (a : IdeleGroup L))
        have hNormVal := congrArg Units.val hNorm
        change
          0 <
            ((Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hvReal).toMulEquiv)
              (LocalFieldTheory.normUnits
                v.1.Completion W.1.Completion
                (IdeleGroup.infiniteComponent W.1
                  (a : IdeleGroup L))) : ℝ)
        rw [hNormVal]
        change
          0 <
            InfinitePlace.Completion.ringEquivRealOfIsReal
              hWReal
              (IdeleGroup.infiniteComponent W.1
                (a : IdeleGroup L) : W.1.Completion)
        exact hUpstairs
      · simpa only [
            InfinitePlace.Completion.ringEquivRealOfIsReal_apply] using
          Reciprocity.infinitePlace_normUnits_real_complex_pos
            (K := K) (K' := L) v.1 W.1 hbelow
              hvReal hWComplex
              (IdeleGroup.infiniteComponent W.1
                (a : IdeleGroup L))
    simpa only [IdeleGroup.infiniteComponent_apply] using hNormComponent
  · exact ideleNorm_mem_finitePrimeToModulusSubgroup_aux m a

/-- The ordinary idèle norm restricted to the prime-to-modulus
subgroups selected by the lifted modulus. -/
noncomputable def primeToModulusIdeleNorm
    (m : RayClass.Modulus K) :
    RayClass.idelePrimeToModulusSubgroup
        (normIdeleLiftedModulus
          (K := K) (L := L) m) →*
      RayClass.idelePrimeToModulusSubgroup m where
  toFun a :=
    ⟨IdeleGroup.norm K L (a : IdeleGroup L),
      ideleNorm_mem_idelePrimeToModulusSubgroup
        (K := K) (L := L) m a⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (IdeleGroup.norm K L)
  map_mul' a b := by
    apply Subtype.ext
    exact
      (IdeleGroup.norm K L).map_mul
        (a : IdeleGroup L) (b : IdeleGroup L)

/-- The restricted idèle norm and the genuine ideal norm commute with
the prime-to-modulus fractional-ideal maps. -/
@[simp]
theorem primeToIdealMap_primeToModulusIdeleNorm
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup
      (normIdeleLiftedModulus
        (K := K) (L := L) m)) :
    RayClass.primeToIdealMap m
        (primeToModulusIdeleNorm
          (K := K) (L := L) m a) =
      RayClass.primeToModulusIdealNorm
        (K := K) (L := L) m
        (RayClass.idealNormLiftedDomainEquiv (L := L) m
          (RayClass.primeToIdealMap
            (normIdeleLiftedModulus
              (K := K) (L := L) m) a)) := by
  apply Subtype.ext
  exact
    IdeleGroup.fractionalIdeal_ideleNorm
      (K := K) (L := L) (a : IdeleGroup L)

omit [FiniteDimensional K L] in
private theorem
    exists_primeToModulusIdele_norm_class_eq_of_mem_idealArtinKernel
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    {I : RayClass.primeToModulusIdeals m}
    (hI : I ∈ idealArtinKernel m
      (_root_.ideleClassNorm K L).range hm) :
    ∃ a : RayClass.idelePrimeToModulusSubgroup m,
      RayClass.primeToIdealMap m a = I ∧
        ∃ b : RayClass.idelePrimeToModulusSubgroup
            (normIdeleLiftedModulus
              (K := K) (L := L) m),
          IdeleGroup.toStandardClass K
              (IdeleGroup.norm K L (b : IdeleGroup L)) =
            IdeleGroup.toStandardClass K
              (a : IdeleGroup K) := by
  change
    idealArtinMap m
        (_root_.ideleClassNorm K L).range hm I = 1 at hI
  obtain ⟨a, ha⟩ :=
    RayClass.primeToIdealMap_surjective m I
  have haKernel :
      QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          (IdeleGroup.toStandardClass K
            (a : IdeleGroup K)) = 1 := by
    rw [← idealArtinMap_primeToIdealMap m
      (_root_.ideleClassNorm K L).range hm a, ha]
    exact hI
  have haNormRange :
      IdeleGroup.toStandardClass K
          (a : IdeleGroup K) ∈
        (_root_.ideleClassNorm K L).range :=
    (QuotientGroup.eq_one_iff _).1 haKernel
  obtain ⟨c, hc⟩ := haNormRange
  obtain ⟨b, rfl⟩ :=
    IdeleGroup.toStandardClass_surjective L c
  obtain ⟨x, hbx⟩ :=
    RayClass.exists_principal_quotient_mem_primeTo
      (normIdeleLiftedModulus
        (K := K) (L := L) m) b
  let b' :
      RayClass.idelePrimeToModulusSubgroup
        (normIdeleLiftedModulus
          (K := K) (L := L) m) :=
    ⟨b * (IdeleGroup.principalIdele L x)⁻¹, hbx⟩
  have hb'class :
      IdeleGroup.toStandardClass L
          (b' : IdeleGroup L) =
        IdeleGroup.toStandardClass L b := by
    apply (IdeleGroup.toStandardClass_eq_iff (K := L) _ _).2
    change (b * (IdeleGroup.principalIdele L x)⁻¹)⁻¹ * b ∈ IdeleGroup.principalSubgroup L
    refine ⟨x, ?_⟩
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨a, ha, b', ?_⟩
  rw [← _root_.ideleClassNorm_mk, hb'class]
  exact hc

private theorem
    primeToIdealMap_mem_idealNormSubgroup_of_norm_class_eq
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup m)
    (b : RayClass.idelePrimeToModulusSubgroup
      (normIdeleLiftedModulus
        (K := K) (L := L) m))
    (hNormClass :
      IdeleGroup.toStandardClass K
          (IdeleGroup.norm K L (b : IdeleGroup L)) =
        IdeleGroup.toStandardClass K
          (a : IdeleGroup K)) :
    RayClass.primeToIdealMap m a ∈
      RayClass.idealNormSubgroup
        (K := K) (L := L) m := by
  let nb : RayClass.idelePrimeToModulusSubgroup m :=
    primeToModulusIdeleNorm
      (K := K) (L := L) m b
  let d : RayClass.idelePrimeToModulusSubgroup m :=
    a * nb⁻¹
  have hdPrincipal :
      (d : IdeleGroup K) ∈
        IdeleGroup.principalSubgroup K := by
    apply (IdeleGroup.toStandardClass_eq_one_iff K d).1
    change
      IdeleGroup.toStandardClass K
            ((a : IdeleGroup K) *
              (IdeleGroup.norm K L
                (b : IdeleGroup L))⁻¹) = 1
    rw [map_mul, map_inv, hNormClass]
    exact mul_inv_cancel _
  have hdRay :
      RayClass.primeToIdealMap m d ∈
        RayClass.principalRayIdealSubgroup m :=
    ⟨d, hdPrincipal, rfl⟩
  let J :=
    RayClass.idealNormLiftedDomainEquiv (L := L) m
      (RayClass.primeToIdealMap
        (normIdeleLiftedModulus
          (K := K) (L := L) m) b)
  let n :=
    RayClass.primeToModulusIdealNorm
      (K := K) (L := L) m J
  have hnRange :
      n ∈
        (RayClass.primeToModulusIdealNorm
          (K := K) (L := L) m).range :=
    ⟨J, rfl⟩
  have hnbIdeal :
      RayClass.primeToIdealMap m nb = n :=
    primeToIdealMap_primeToModulusIdeleNorm
      (K := K) (L := L) m b
  have hdIdeal :
      RayClass.primeToIdealMap m d =
        RayClass.primeToIdealMap m a * n⁻¹ := by
    change
      RayClass.primeToIdealMap m (a * nb⁻¹) =
        RayClass.primeToIdealMap m a * n⁻¹
    rw [map_mul, map_inv, hnbIdeal]
  rw [RayClass.idealNormSubgroup, Subgroup.mem_sup]
  refine
    ⟨n, hnRange, RayClass.primeToIdealMap m d,
      hdRay, ?_⟩
  calc
    n * RayClass.primeToIdealMap m d =
        n * (RayClass.primeToIdealMap m a * n⁻¹) := by
      rw [hdIdeal]
    _ = RayClass.primeToIdealMap m a * (n * n⁻¹) := by
      ac_rfl
    _ = RayClass.primeToIdealMap m a := by
      rw [mul_inv_cancel, mul_one]

private theorem idealArtinKernel_le_idealNormSubgroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    idealArtinKernel m
        (_root_.ideleClassNorm K L).range hm ≤
      RayClass.idealNormSubgroup
        (K := K) (L := L) m := by
  intro I hI
  obtain ⟨a, ha, b, hab⟩ :=
    exists_primeToModulusIdele_norm_class_eq_of_mem_idealArtinKernel
      (K := K) (L := L) m hm hI
  rw [← ha]
  exact
    primeToIdealMap_mem_idealNormSubgroup_of_norm_class_eq
      (K := K) (L := L) m a b hab

private theorem idealNormSubgroup_le_idealArtinKernel
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.idealNormSubgroup
        (K := K) (L := L) m ≤
      idealArtinKernel m
        (_root_.ideleClassNorm K L).range hm := by
  rw [RayClass.idealNormSubgroup]
  apply sup_le
  · rintro n ⟨J, rfl⟩
    obtain ⟨b, hb⟩ :=
      RayClass.primeToIdealMap_surjective
        (normIdeleLiftedModulus
          (K := K) (L := L) m)
        ((RayClass.idealNormLiftedDomainEquiv (L := L) m).symm J)
    have hJ : RayClass.idealNormLiftedDomainEquiv (L := L) m
        (RayClass.primeToIdealMap
          (normIdeleLiftedModulus (K := K) (L := L) m) b) = J := by
      rw [hb]
      exact (RayClass.idealNormLiftedDomainEquiv (L := L) m).apply_symm_apply J
    change
      idealArtinMap m
          (_root_.ideleClassNorm K L).range hm
          (RayClass.primeToModulusIdealNorm
            (K := K) (L := L) m J) = 1
    rw [← hJ,
      ← primeToIdealMap_primeToModulusIdeleNorm
        (K := K) (L := L) m b,
      idealArtinMap_primeToIdealMap]
    apply (QuotientGroup.eq_one_iff _).2
    exact
      ⟨IdeleGroup.toStandardClass L
          (b : IdeleGroup L),
        _root_.ideleClassNorm_mk
          K L (b : IdeleGroup L)⟩
  · exact
      principalRayIdealSubgroup_le_idealArtinKernel
        m (_root_.ideleClassNorm K L).range hm

/-- For a finite extension and a defining modulus, the kernel of the ideal
Artin map is exactly the genuine norm-defined ideal group
`N_{L/K} J_L^m P_K^m`. -/
theorem idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    idealArtinKernel m
        (_root_.ideleClassNorm K L).range hm =
      RayClass.idealNormSubgroup
        (K := K) (L := L) m :=
  le_antisymm
    (idealArtinKernel_le_idealNormSubgroup
      (K := K) (L := L) m hm)
    (idealNormSubgroup_le_idealArtinKernel
      (K := K) (L := L) m hm)

end NormDefinedFiniteKernel

section NormDefinedKernel

variable
    {L : Type v} [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]

omit [IsGalois K L] in
/-- For a defining modulus, the kernel of the ideal Artin map is exactly the
genuine norm-defined ideal group `N_{L/K} J_L^m P_K^m` for a finite Galois
extension.  This preserves the original Galois-facing API while delegating to
the finite-extension theorem. -/
theorem idealArtinKernel_eq_idealNormSubgroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    idealArtinKernel m
        (_root_.ideleClassNorm K L).range hm =
      RayClass.idealNormSubgroup
        (K := K) (L := L) m :=
  idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension
    (K := K) (L := L) m hm

end NormDefinedKernel

/-- The Artin map on ideals is surjective. -/
theorem idealArtinMap_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Function.Surjective (idealArtinMap m N hm) := by
  exact
    (idealRayClassArtinMap_surjective m N hm).comp
      (QuotientGroup.mk'_surjective
        (RayClass.principalRayIdealSubgroup m))

/-- Exactness of
`1 → H_m → J_K^m → C_K/N → 1`. -/
theorem idealArtin_exact
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    (∀ a : RayClass.primeToModulusIdeals m,
      idealArtinMap m N hm a = 1 ↔
        a ∈ idealArtinKernel m N hm) ∧
      Function.Surjective (idealArtinMap m N hm) := by
  exact ⟨fun _ => Iff.rfl, idealArtinMap_surjective m N hm⟩

section ActualGaloisArtin

variable
    {L : Type v} [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The ideal-theoretic Artin map with its actual Galois-group target.

For a defining modulus of the genuine norm subgroup
`N_{L/K} C_L`, this is the quotient-valued ideal Artin map followed by
the global norm-residue equivalence
`C_K / N_{L/K} C_L ≃ Gal(L/K)`. -/
noncomputable def idealArtinGaloisMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m →*
      (L ≃ₐ[K] L) :=
  (AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L)).toMonoidHom.comp
    (idealArtinMap m
      ((_root_.ideleClassNorm K L).range) hm)

/-- Evaluation of the actual ideal Artin map is the global
norm-residue equivalence applied to the quotient-valued ideal Artin
class. -/
@[simp]
theorem idealArtinGaloisMap_apply
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    idealArtinGaloisMap (K := K) (L := L) m hm a =
      Additive.toMul
        (Reciprocity.globalNormResidueEquiv K L
          (Additive.ofMul
            (idealArtinMap m
              ((_root_.ideleClassNorm K L).range) hm a))) :=
  rfl

/-- The actual Galois-valued ideal Artin map is surjective. -/
theorem idealArtinGaloisMap_surjective
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    Function.Surjective
      (idealArtinGaloisMap (K := K) (L := L) m hm) := by
  exact
    (AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L)).surjective.comp
      (idealArtinMap_surjective m
        ((_root_.ideleClassNorm K L).range) hm)

/-- Passing from the genuine norm quotient to the actual Galois group
does not change the ideal Artin kernel. -/
@[simp]
theorem idealArtinGaloisMap_ker
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (idealArtinGaloisMap
        (K := K) (L := L) m hm).ker =
      idealArtinKernel m
        ((_root_.ideleClassNorm K L).range) hm := by
  ext a
  let e :=
    AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L)
  change
    e
          (idealArtinMap m
            ((_root_.ideleClassNorm K L).range) hm a) =
        1 ↔
      idealArtinMap m
          ((_root_.ideleClassNorm K L).range) hm a =
        1
  exact e.map_eq_one_iff

/-- Exactness of the actual ideal Artin sequence
`1 → H_m → J_K^m → Gal(L/K) → 1`. -/
theorem idealArtinGalois_exact
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (∀ a : RayClass.primeToModulusIdeals m,
      idealArtinGaloisMap (K := K) (L := L) m hm a = 1 ↔
        a ∈ idealArtinKernel m
          ((_root_.ideleClassNorm K L).range) hm) ∧
      Function.Surjective
        (idealArtinGaloisMap (K := K) (L := L) m hm) := by
  constructor
  · intro a
    change
      a ∈
          (idealArtinGaloisMap
            (K := K) (L := L) m hm).ker ↔
        a ∈ idealArtinKernel m
          ((_root_.ideleClassNorm K L).range) hm
    rw [idealArtinGaloisMap_ker]
  · exact idealArtinGaloisMap_surjective m hm

end ActualGaloisArtin

end IdealClassFieldTheory
end GlobalClassFieldTheory
