/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderCoprimeRepresentative
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderConductorModulus
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderFractionalIdealClass
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderIdealClass
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldConstruction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticClassFieldCorrespondence
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderRayClass
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassModulusProjection
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassNormIdealComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Ring class fields of full integer orders -/

@[expose] public section

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain

namespace GlobalClassFieldTheory.GlobalClassFields

variable {K : Type*} [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] [IsFractionRing O K]

/-- The idèle class map of the order, through the actual conductor ray quotient. -/
noncomputable def orderIdeleClassMap : IdeleClassGroup K →* ClassGroup O :=
  (orderRayClassToClassGroup O).comp
    ((RayClass.rayClassGroupEquivIdealRayClassGroup (orderConductorModulus O)).toMonoidHom.comp
      (QuotientGroup.mk' (orderConductorModulus O).congruenceSubgroup))

theorem orderIdeleClassMap_surjective : Function.Surjective (orderIdeleClassMap O) :=
  (orderRayClassToClassGroup_surjective O).comp
    ((RayClass.rayClassGroupEquivIdealRayClassGroup (orderConductorModulus O)).surjective.comp
      (QuotientGroup.mk'_surjective (orderConductorModulus O).congruenceSubgroup))

theorem orderIdeleClassMap_continuous [TopologicalSpace (ClassGroup O)] :
    Continuous (orderIdeleClassMap O) := by
  let m := orderConductorModulus O
  let g : RayClass.RayClassGroup m →* ClassGroup O :=
    (orderRayClassToClassGroup O).comp (RayClass.rayClassGroupEquivIdealRayClassGroup m).toMonoidHom
  have : DiscreteTopology (RayClass.RayClassGroup m) :=
    QuotientGroup.discreteTopology (RayClass.isOpen_congruenceSubgroup m)
  change Continuous (g ∘ QuotientGroup.mk' m.congruenceSubgroup)
  exact (continuous_of_discreteTopology : Continuous g).comp QuotientGroup.continuous_mk

theorem orderClassGroup_finite : Finite (ClassGroup O) := by
  let m := orderConductorModulus O
  have : Finite (RayClass.RayClassGroup m) := inferInstance
  let e := RayClass.rayClassGroupEquivIdealRayClassGroup m
  exact Finite.of_surjective ((orderRayClassToClassGroup O).comp e.toMonoidHom)
    ((orderRayClassToClassGroup_surjective O).comp e.surjective)

theorem orderConductorCongruence_le_ideleClassMap_ker :
    (orderConductorModulus O).congruenceSubgroup ≤ (orderIdeleClassMap O).ker := by
  intro c hc
  let m := orderConductorModulus O
  change orderRayClassToClassGroup O (RayClass.rayClassGroupEquivIdealRayClassGroup m
    (QuotientGroup.mk' m.congruenceSubgroup c)) = 1
  have h : QuotientGroup.mk' m.congruenceSubgroup c = 1 :=
    (QuotientGroup.eq_one_iff (N := m.congruenceSubgroup) c).mpr hc
  rw [h, map_one, map_one]

theorem orderIdeleClassMap_ker_isOpen :
    IsOpen ((orderIdeleClassMap O).ker : Set (IdeleClassGroup K)) :=
  Subgroup.isOpen_mono (orderConductorCongruence_le_ideleClassMap_ker O)
    (RayClass.isOpen_congruenceSubgroup (orderConductorModulus O))

theorem orderIdeleClassMap_ker_isClosed :
    IsClosed ((orderIdeleClassMap O).ker : Set (IdeleClassGroup K)) :=
  (orderIdeleClassMap O).ker.isClosed_of_isOpen (orderIdeleClassMap_ker_isOpen O)

instance orderIdeleClassMap_ker_finiteIndex : (orderIdeleClassMap O).ker.FiniteIndex := by
  have : Finite (ClassGroup O) := orderClassGroup_finite O
  exact Subgroup.finiteIndex_ker (orderIdeleClassMap O)

/-- The finite abelian class field selected by the kernel of the order's idèle class quotient. -/
noncomputable abbrev ringClassField : IntermediateField K (SeparableClosure K) :=
  closedFiniteIndexClassField (orderIdeleClassMap O).ker (orderIdeleClassMap_ker_isClosed O)

theorem ringClassField_ideleClassNorm_range :
    (_root_.ideleClassNorm K (ringClassField O)).range = (orderIdeleClassMap O).ker :=
  closedFiniteIndexClassField_ideleClassNorm_range (orderIdeleClassMap O).ker
    (orderIdeleClassMap_ker_isClosed O)

/-- Arithmetic reciprocity identifies the order class group with the ring class Galois group. -/
noncomputable def ringClassArtinEquiv : ClassGroup O ≃* Gal(ringClassField O / K) :=
  (QuotientGroup.quotientKerEquivOfSurjective (orderIdeleClassMap O)
    (orderIdeleClassMap_surjective O)).symm.trans
      (arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
        (orderIdeleClassMap O).ker (orderIdeleClassMap_ker_isClosed O)).toMulEquiv.symm

theorem ringClassArtinEquiv_orderIdeleClassMap (c : IdeleClassGroup K) :
    ringClassArtinEquiv O (orderIdeleClassMap O c) =
      Reciprocity.arithmeticGlobalNormResidueMonoidHom K (ringClassField O) c := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (orderIdeleClassMap O)
    (orderIdeleClassMap_surjective O)
  let g := arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
    (orderIdeleClassMap O).ker (orderIdeleClassMap_ker_isClosed O)
  change g.symm (e.symm (orderIdeleClassMap O c)) = _
  have he : e (QuotientGroup.mk' (orderIdeleClassMap O).ker c) = orderIdeleClassMap O c := rfl
  rw [← he, e.symm_apply_apply]
  exact arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient_symm_mk
    (orderIdeleClassMap O).ker (orderIdeleClassMap_ker_isClosed O) c

theorem ringClassField_finrank : Module.finrank K (ringClassField O) = Nat.card (ClassGroup O) := by
  rw [closedFiniteIndexClassField_finrank_eq_index, Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (orderIdeleClassMap O)
    (orderIdeleClassMap_surjective O)).toEquiv

theorem ringClassField_conductor_le :
    (ideleClassNormConductorialSubgroup (K := K) (L := ringClassField O)).fullConductor ≤
      orderConductorModulus O := by
  let H := ideleClassNormConductorialSubgroup (K := K) (L := ringClassField O)
  apply (H.isDefiningModulus_iff_fullConductor_le (orderConductorModulus O)).mp
  change (orderConductorModulus O).congruenceSubgroup ≤
    (_root_.ideleClassNorm K (ringClassField O)).range
  rw [ringClassField_ideleClassNorm_range]
  exact orderConductorCongruence_le_ideleClassMap_ker O

private theorem orderIdeleClassMap_apply_integral
    (b : RayClass.idelePrimeToModulusSubgroup (orderConductorModulus O))
    (J : orderPrimeToConductorIdeals O)
    (hb : RayClass.primeToIdealMap (orderConductorModulus O) b =
      orderIntegralIdealToFractional O J) :
    orderIdeleClassMap O (IdeleGroup.toStandardClass K (b : IdeleGroup K)) =
      orderIdealClassMap O J := by
  let m := orderConductorModulus O
  change orderRayClassToClassGroup O (RayClass.rayClassGroupEquivIdealRayClassGroup m
    (QuotientGroup.mk' m.congruenceSubgroup
      (IdeleGroup.toStandardClass K (b : IdeleGroup K)))) = _
  rw [RayClass.rayClassGroupEquivIdealRayClassGroup_mk_primeTo]
  change orderRayClassToClassGroup O
    (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m) (RayClass.primeToIdealMap m b)) = _
  exact (congrArg (fun I : RayClass.primeToModulusIdeals m =>
    orderRayClassToClassGroup O (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m) I))
    hb).trans (orderRayClassToClassGroup_integral O J)

/-- The order map sends the normalized prime idèle to the class of the contracted prime. -/
theorem orderIdeleClassMap_finitePrimeIdele (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (orderConductorModulus O).finitePart.support) :
    orderIdeleClassMap O (IdeleGroup.toStandardClass K
      (IdeleGroup.finitePrimeIdele v)) =
        orderIdealClassMap O ⟨v.asIdeal, v.ne_bot, orderPrime_coprime_conductor O v hv⟩ := by
  let m := orderConductorModulus O
  let a : RayClass.idelePrimeToModulusSubgroup m :=
    ⟨IdeleGroup.finitePrimeIdele v, finitePrimeIdele_mem_idelePrimeToModulusSubgroup m v hv⟩
  let I : orderPrimeToConductorIdeals O :=
    ⟨v.asIdeal, v.ne_bot, orderPrime_coprime_conductor O v hv⟩
  have hI : RayClass.primeToModulusIdeal m v hv = orderIntegralIdealToFractional O I := by
    apply Subtype.ext
    apply Units.ext
    rfl
  apply orderIdeleClassMap_apply_integral O a I
  exact (primeToIdealMap_finitePrimeIdele m v hv).trans hI

/-- Away from the conductor, the contracted prime class acts by arithmetic Frobenius. -/
theorem ringClassArtinEquiv_prime (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (orderConductorModulus O).finitePart.support)
    (w : HeightOneSpectrum (𝓞 (ringClassField O))) (hw : w.asIdeal.LiesOver v.asIdeal) :
    ringClassArtinEquiv O
      (orderIdealClassMap O ⟨v.asIdeal, v.ne_bot, orderPrime_coprime_conductor O v hv⟩) =
        ClassFieldTheory.arithmeticFrobeniusAt (K := K) w := by
  let m := orderConductorModulus O
  let m' : ClassFieldTheory.RayClassModulus K := ⟨m.finitePart, m.infinitePart⟩
  have hle : m.congruenceSubgroup ≤ (_root_.ideleClassNorm K (ringClassField O)).range := by
    rw [ringClassField_ideleClassNorm_range]
    exact orderConductorCongruence_le_ideleClassMap_ker O
  have hunram :=
    ClassFieldTheory.GlobalClassFieldComparison.unramifiedOutsideModulus_of_definingModulus
      K (ringClassField O) m' hle
  rw [← orderIdeleClassMap_finitePrimeIdele O v hv, ringClassArtinEquiv_orderIdeleClassMap,
    ← arithmeticFinitePlacePrimeArtin_eq_arithmeticGlobalNormResidue]
  exact ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
    (K := K) (L := ringClassField O) v w hw (hunram.1 v hv w.asIdeal inferInstance hw)

private theorem rayClassRep_eq_of_idealRep (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) (b : RayClass.idelePrimeToModulusSubgroup m)
    (I : RayClass.primeToModulusIdeals m) (hb : RayClass.primeToIdealMap m b = I)
    (hI : QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m) I =
      RayClass.rayClassGroupEquivIdealRayClassGroup m (QuotientGroup.mk' m.congruenceSubgroup c)) :
    QuotientGroup.mk' m.congruenceSubgroup c =
      QuotientGroup.mk' m.congruenceSubgroup (IdeleGroup.toStandardClass K (b : IdeleGroup K)) := by
  apply (RayClass.rayClassGroupEquivIdealRayClassGroup m).injective
  have hr := RayClass.rayClassGroupEquivIdealRayClassGroup_mk_primeTo m b
  change _ = QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m)
    (RayClass.primeToIdealMap m b) at hr
  exact hI.symm.trans ((congrArg (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m))
    hb).symm.trans hr.symm)

private def orderPrimeToConductorIdeal_of_le
    {P : Subalgebra ℤ K} [Module.Finite ℤ P] [IsFractionRing P K] (h : O ≤ P)
    (J : orderPrimeToConductorIdeals O) : orderPrimeToConductorIdeals P :=
  ⟨J.1, J.2.1, top_unique (J.2.2 ▸ sup_le_sup le_rfl (orderConductor_mono h))⟩

private theorem primeToIdealMap_fractionalIdeal (m : RayClass.Modulus K)
    (b : RayClass.idelePrimeToModulusSubgroup m) :
    (RayClass.primeToIdealMap m b).val = IdeleGroup.fractionalIdeal b.val := rfl

private theorem orderIntegralIdealToFractional_mk0 (J : orderPrimeToConductorIdeals O) :
    (orderIntegralIdealToFractional O J).val =
      FractionalIdeal.mk0 K ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr J.2.1⟩ := rfl

private theorem primeToIdealMap_eq_orderIntegralIdealToFractional_of_le
    {P : Subalgebra ℤ K} [Module.Finite ℤ P] [IsFractionRing P K] (h : O ≤ P)
    (J : orderPrimeToConductorIdeals O)
    (b : RayClass.idelePrimeToModulusSubgroup (orderConductorModulus O))
    (hb : RayClass.primeToIdealMap (orderConductorModulus O) b =
      orderIntegralIdealToFractional O J) :
    RayClass.primeToIdealMap (orderConductorModulus P)
      ⟨b, RayClass.idelePrimeToModulusSubgroup_antitone (orderConductorModulus_antitone O h) b.2⟩ =
        orderIntegralIdealToFractional P (orderPrimeToConductorIdeal_of_le O h J) := by
  let m := orderConductorModulus O
  let m' := orderConductorModulus P
  let b' : RayClass.idelePrimeToModulusSubgroup m' :=
    ⟨b, RayClass.idelePrimeToModulusSubgroup_antitone (orderConductorModulus_antitone O h) b.2⟩
  let J' := orderPrimeToConductorIdeal_of_le O h J
  have hb' : (RayClass.primeToIdealMap m' b').val = (RayClass.primeToIdealMap m b).val :=
    (primeToIdealMap_fractionalIdeal m' b').trans (primeToIdealMap_fractionalIdeal m b).symm
  have hJ : (orderIntegralIdealToFractional O J).val = (orderIntegralIdealToFractional P J').val :=
    (orderIntegralIdealToFractional_mk0 O J).trans (orderIntegralIdealToFractional_mk0 P J').symm
  exact Subtype.ext (hb'.trans
    ((congrArg (fun I : RayClass.primeToModulusIdeals m => I.val) hb).trans hJ))

omit [IsFractionRing (↥O) K] in
private theorem orderIdealClassMap_eq_one_of_principal_from_suborder
    {P : Subalgebra ℤ K} [Module.Finite ℤ P] [IsFractionRing P K] (h : O ≤ P)
    (J : orderPrimeToConductorIdeals P) (a : O)
    (hJ : J.1 = Ideal.span ({orderToRingOfIntegers O a} : Set (𝓞 K))) :
    orderIdealClassMap P J = 1 := by
  let a' : P := Subalgebra.inclusion h a
  have haa' : orderToRingOfIntegers O a = orderToRingOfIntegers P a' := Subtype.ext
    ((orderToRingOfIntegers_coe O a).trans
      ((orderToRingOfIntegers_coe P a').trans (Subalgebra.coe_inclusion h a)).symm)
  exact (orderIdealClassMap_eq_one_iff P J).mpr
    ⟨a', hJ.trans (congrArg (fun x : 𝓞 K => Ideal.span ({x} : Set (𝓞 K))) haa')⟩

private theorem orderIdeleClassMap_eq_one_of_principalIdealRepresentative
    {P : Subalgebra ℤ K} [Module.Finite ℤ P] [IsFractionRing P K] (h : O ≤ P)
    (J : orderPrimeToConductorIdeals O) (a : O)
    (hJ : J.1 = Ideal.span ({orderToRingOfIntegers O a} : Set (𝓞 K)))
    (b : RayClass.idelePrimeToModulusSubgroup (orderConductorModulus O))
    (hb : RayClass.primeToIdealMap (orderConductorModulus O) b =
      orderIntegralIdealToFractional O J) :
    orderIdeleClassMap P (IdeleGroup.toStandardClass K (b : IdeleGroup K)) = 1 := by
  let b' : RayClass.idelePrimeToModulusSubgroup (orderConductorModulus P) :=
    ⟨b, RayClass.idelePrimeToModulusSubgroup_antitone (orderConductorModulus_antitone O h) b.2⟩
  let J' := orderPrimeToConductorIdeal_of_le O h J
  exact (orderIdeleClassMap_apply_integral P b' J'
    (primeToIdealMap_eq_orderIntegralIdealToFractional_of_le O h J b hb)).trans
    (orderIdealClassMap_eq_one_of_principal_from_suborder O h J' a hJ)

/-- Enlarging the order enlarges the defining idèle class subgroup. -/
theorem orderIdeleClassMap_ker_mono
    {P : Subalgebra ℤ K} [Module.Finite ℤ P] [IsFractionRing P K] (h : O ≤ P) :
    (orderIdeleClassMap O).ker ≤ (orderIdeleClassMap P).ker := by
  let m := orderConductorModulus O
  let n := orderConductorModulus P
  let q := QuotientGroup.mk' m.congruenceSubgroup
  let q' := QuotientGroup.mk' n.congruenceSubgroup
  let e := RayClass.rayClassGroupEquivIdealRayClassGroup m
  let e' := RayClass.rayClassGroupEquivIdealRayClassGroup n
  have hnm : n ≤ m := orderConductorModulus_antitone O h
  intro c hc
  change orderRayClassToClassGroup O (e (q c)) = 1 at hc
  obtain ⟨J, a, hJray, hJ⟩ := (orderRayClassToClassGroup_eq_one_iff O (e (q c))).mp hc
  obtain ⟨b, hb⟩ := RayClass.primeToIdealMap_surjective m (orderIntegralIdealToFractional O J)
  let c' := IdeleGroup.toStandardClass K (b : IdeleGroup K)
  have hrepr := rayClassRep_eq_of_idealRep m c b (orderIntegralIdealToFractional O J) hb hJray
  have hrepr' : q' c = q' c' :=
    congrArg (ClassFieldTheory.originalRayClassModulusProjection K hnm) hrepr
  have hMap : orderIdeleClassMap P c = orderIdeleClassMap P c' :=
    congrArg (fun z => orderRayClassToClassGroup P (e' z)) hrepr'
  exact hMap.trans (orderIdeleClassMap_eq_one_of_principalIdealRepresentative O h J a hJ b hb)

/-- The class field of a larger order embeds over the base field into the class field of the
smaller order. -/
theorem ringClassField_nonempty_algHom_of_le
    {P : Subalgebra ℤ K} [Module.Finite ℤ P] [IsFractionRing P K] (h : O ≤ P) :
    Nonempty (ringClassField P →ₐ[K] ringClassField O) := by
  apply finiteAbelianExtension_nonempty_algHom_of_normRange_le
  rw [ringClassField_ideleClassNorm_range, ringClassField_ideleClassNorm_range]
  exact orderIdeleClassMap_ker_mono O h

private theorem zero_rayCongruence_eq_smallHilbertClassFieldNormSubgroup :
    (0 : RayClass.Modulus K).congruenceSubgroup = smallHilbertClassFieldNormSubgroup (K := K) := by
  have hzero : (0 : RayClass.Modulus K).ideleCongruenceSubgroup =
      IdeleGroup.integralAtFinitePlaces (K := K) := by
    ext a
    change (IdeleGroup.infinitePart a ∈ (0 : RayClass.Modulus K).infiniteCongruenceSubgroup ∧
      IdeleGroup.finiteCoordinates a ∈
        RayClass.finiteCongruenceSubgroup (0 : RayClass.FiniteModulus K)) ↔
      IdeleGroup.finiteCoordinates a ∈ FiniteIdeleGroup.integralSubgroup
    rw [RayClass.finiteCongruenceSubgroup_zero]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    intro v hv
    rw [RayClass.Modulus.infinitePart_zero] at hv
    exact (Finset.notMem_empty v hv).elim
  rw [RayClass.Modulus.congruenceSubgroup, smallHilbertClassFieldNormSubgroup, hzero]

/-- The unit-conductor order has the same norm subgroup as the ordinary Hilbert class field. -/
theorem orderIdeleClassMap_ker_eq_smallHilbertClassFieldNormSubgroup
    (h : orderConductor O = ⊤) :
    (orderIdeleClassMap O).ker = smallHilbertClassFieldNormSubgroup (K := K) := by
  let m := orderConductorModulus O
  have hm : m = 0 := orderConductorModulus_eq_zero_of_conductor_eq_top O h
  have hk : (orderIdeleClassMap O).ker = m.congruenceSubgroup := by
    apply le_antisymm _ (orderConductorCongruence_le_ideleClassMap_ker O)
    intro c hc
    let e := RayClass.rayClassGroupEquivIdealRayClassGroup m
    change orderRayClassToClassGroup O (e (QuotientGroup.mk' m.congruenceSubgroup c)) = 1 at hc
    apply (QuotientGroup.eq_one_iff (N := m.congruenceSubgroup) c).mp
    have hq := orderRayClassToClassGroup_injective_of_conductor_eq_top O h
    apply e.injective
    apply hq
    exact hc.trans ((congrArg (orderRayClassToClassGroup O) (map_one e)).trans
      (map_one (orderRayClassToClassGroup O))).symm
  rw [hk, hm, zero_rayCongruence_eq_smallHilbertClassFieldNormSubgroup]

/-- For the maximal order, the selected field is the ordinary Hilbert class field over `K`. -/
theorem ringClassField_nonempty_algEquiv_smallHilbertClassField
    (h : O = integralClosure ℤ K) :
    Nonempty (ringClassField O ≃ₐ[K] rayClassField K (0 : RayClass.Modulus K)) := by
  apply (nonempty_algEquiv_iff_ideleClassNorm_range_eq (K := K) (ringClassField O)
    (rayClassField K (0 : RayClass.Modulus K))).mpr
  rw [ringClassField_ideleClassNorm_range, rayClassField_ideleClassNorm_range_over_original,
    zero_rayCongruence_eq_smallHilbertClassFieldNormSubgroup]
  exact orderIdeleClassMap_ker_eq_smallHilbertClassFieldNormSubgroup O
    ((orderConductor_eq_top_iff_eq_ringOfIntegers O).mpr h)

end GlobalClassFieldTheory.GlobalClassFields
