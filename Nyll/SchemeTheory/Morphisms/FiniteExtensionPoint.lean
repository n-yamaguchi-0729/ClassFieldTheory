/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.NoetherNormalization.Nonvanishing
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Topology.JacobsonSpace

/-!
# Points over finite intermediate extensions

Closed points provide finite residue fields over the ground field. Embedding
one in a specified algebraic closure yields an actual finite intermediate
field and an actual closed point over that field. For a formally unramified
scheme, the same point is defined over a finite separable extension.
-/

noncomputable section
open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A nonempty scheme locally of finite type has a point over a finite subextension
of any specified algebraically closed extension of its base field. The
constructed point is a closed immersion, so its residue field is not enlarged. -/
theorem exists_point_finite_intermediateField
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [Nonempty X] :
    ∃ E : IntermediateField k Ω, Module.Finite k E ∧
      ∃ p : Spec (CommRingCat.of E) ⟶ X, IsClosedImmersion p ∧
        p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (X := X) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let a := Spec.preimage (X.fromSpecResidueField x ≫ f)
  let κ : Type u := X.residueField x
  let : Algebra k κ := a.hom.toAlgebra
  have : Module.Finite k κ := (IsFinite.SpecMap_iff a).mp (by
    simpa only [a, Spec.map_preimage] using hfin)
  let j : κ →ₐ[k] Ω := IsAlgClosed.lift
  let E := j.fieldRange
  let e : κ ≃ₐ[k] E := j.equivFieldRange
  have hE : Module.Finite k E := Module.Finite.of_surjective e.toLinearMap e.surjective
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ e.surjective
  refine ⟨E, hE, Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x,
    inferInstance, ?_⟩
  rw [Category.assoc, ← Spec.map_preimage (X.fromSpecResidueField x ≫ f), ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact congrArg (fun z : E => (z : Ω)) (e.commutes r)

/-- A nonempty scheme locally of finite type and formally unramified over a
field has a closed point over a finite separable intermediate extension.
No perfectness assumption on the ground field is required. -/
theorem exists_point_finite_separable_intermediateField
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [FormallyUnramified f] [Nonempty X] :
    ∃ E : IntermediateField k Ω, Module.Finite k E ∧ Algebra.IsSeparable k E ∧
      ∃ p : Spec (CommRingCat.of E) ⟶ X, IsClosedImmersion p ∧
        p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  obtain ⟨E, hE, p, hpClosed, hp⟩ := exists_point_finite_intermediateField k Ω f
  have : Module.Finite k E := hE
  have : IsClosedImmersion p := hpClosed
  have hf : FormallyUnramified
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) := by
    rw [← hp]
    exact MorphismProperty.comp_mem (@FormallyUnramified) p f
      inferInstance inferInstance
  have hRing : (algebraMap k E).FormallyUnramified :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp hf
  have : Algebra.FormallyUnramified k E :=
    (RingHom.formallyUnramified_algebraMap).mp hRing
  exact ⟨E, hE, Algebra.FormallyUnramified.isSeparable k E, p, hpClosed, hp⟩


/-- A nonempty étale chart over affine space meets a rational fibre over an
infinite ground field. That fibre supplies an actual point defined over a
finite separable intermediate extension of the specified algebraic closure. -/
theorem exists_point_finite_separable_intermediateField_of_etale_chart
    (k Ω : Type u) [Field k] [Infinite k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {n : ℕ} {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k)))
    [Etale f] [Nonempty X] :
    ∃ E : IntermediateField k Ω, Module.Finite k E ∧ Algebra.IsSeparable k E ∧
      ∃ (a : Fin n → k) (p : Spec (CommRingCat.of E) ⟶ X),
        p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k E)) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  have hopen : IsOpen (Set.range f) := by
    simpa only [Set.image_univ] using f.isOpenMap Set.univ isOpen_univ
  obtain ⟨_, ⟨g, rfl⟩, hg, hsubset⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show f x ∈ Set.range f from ⟨x, rfl⟩) hopen
  have hg0 : g ≠ 0 := by
    intro hzero
    change g ∉ (f x).asIdeal at hg
    apply hg
    rw [hzero]
    exact Ideal.zero_mem _
  obtain ⟨a, ha⟩ := FieldArithmetic.Chapter06.exists_eval_ne_zero_fin hg0
  let y := Spec.map (CommRingCat.ofHom (MvPolynomial.eval a))
  let t : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  have hyt : y t ∈ PrimeSpectrum.basicOpen g := by
    change MvPolynomial.eval a g ∉ IsLocalRing.maximalIdeal k
    simpa only [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] using ha
  obtain ⟨x', hx'⟩ := hsubset hyt
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x' t hx'
  have : Nonempty ↥(CategoryTheory.Limits.pullback f y) := ⟨z⟩
  obtain ⟨E, hE, hsep, p, _, hp⟩ :=
    exists_point_finite_separable_intermediateField k Ω
      (CategoryTheory.Limits.pullback.snd f y)
  refine ⟨E, hE, hsep, a, p ≫ CategoryTheory.Limits.pullback.fst f y, ?_⟩
  rw [Category.assoc, CategoryTheory.Limits.pullback.condition, ← Category.assoc, hp]


/-- A nonzero smooth affine algebra over an infinite field has a point over
a finite separable intermediate extension. The étale chart is constructed
from smoothness, rather than supplied as an extra hypothesis. -/
theorem exists_point_finite_separable_intermediateField_of_smooth_algebra
    (k Ω S : Type u) [Field k] [Infinite k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    [CommRing S] [Nontrivial S] [Algebra k S] [Algebra.Smooth k S] :
    ∃ E : IntermediateField k Ω, Module.Finite k E ∧ Algebra.IsSeparable k E ∧
      ∃ p : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of S),
        p ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)) =
          Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  classical
  obtain ⟨q⟩ := PrimeSpectrum.nonempty_iff_nontrivial.mpr (inferInstance : Nontrivial S)
  obtain ⟨r, hr, n, polynomialAlgebra, polynomialTower, standardEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := q.asIdeal)
  let A := Localization.Away r
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := polynomialAlgebra
  have : IsScalarTower k P A := polynomialTower
  have : Algebra.IsStandardEtale P A := standardEtale
  have hprime : (q.asIdeal.map (algebraMap S A)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r) A q.asIdeal q.isPrime
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hr)
  have : Nonempty (Spec (CommRingCat.of A)) := ⟨⟨_, hprime⟩⟩
  let f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of P) :=
    Spec.map (CommRingCat.ofHom (algebraMap P A))
  have : Etale f := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap P A)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact (RingHom.etale_algebraMap).mpr inferInstance
  obtain ⟨E, hE, hsep, a, p, hp⟩ :=
    exists_point_finite_separable_intermediateField_of_etale_chart k Ω f
  have hSA :
      Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k S)) =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq k S A).symm
  have hPA :
      Spec.map (CommRingCat.ofHom (algebraMap k A)) =
        f ≫ Spec.map (CommRingCat.ofHom (algebraMap k P)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap P A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k P))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact IsScalarTower.algebraMap_eq k P A
  have heval :
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k P)) =
        𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    ext t
    exact MvPolynomial.eval_C (f := a) t
  refine ⟨E, hE, hsep, p ≫ Spec.map (CommRingCat.ofHom (algebraMap S A)), ?_⟩
  rw [Category.assoc, hSA, hPA, ← Category.assoc, hp, Category.assoc, heval,
    Category.comp_id]


/-- A nonempty smooth scheme over any field has a point over a finite separable
intermediate extension of a specified algebraically closed extension.
Finite fields are perfect; over an infinite field a smooth affine chart
supplies the point by specialization of its constructed étale coordinates. -/
theorem exists_point_finite_separable_intermediateField_of_smooth
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] [Nonempty X] :
    ∃ E : IntermediateField k Ω, Module.Finite k E ∧ Algebra.IsSeparable k E ∧
      ∃ p : Spec (CommRingCat.of E) ⟶ X,
        p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  classical
  rcases finite_or_infinite k with hk | hk
  · have : Finite k := hk
    obtain ⟨E, hE, p, _, hp⟩ := exists_point_finite_intermediateField k Ω f
    have : Module.Finite k E := hE
    exact ⟨E, hE, inferInstance, p, hp⟩
  · have : Infinite k := hk
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨i, y, _⟩ := X.affineCover.exists_eq x
    let U := X.affineCover.X i
    let e := U.isoSpec
    let A : Type u := Γ(U, ⊤)
    let a := Spec.preimage (e.inv ≫ X.affineCover.f i ≫ f)
    let : Algebra k A := a.hom.toAlgebra
    have hSpec : Smooth (Spec.map a) := by
      rw [Spec.map_preimage]
      infer_instance
    have hRing : a.hom.Smooth :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hSpec
    have : Algebra.Smooth k A := (RingHom.smooth_algebraMap).mp hRing
    have hnonempty : Nonempty (Spec (CommRingCat.of A)) := ⟨e.hom y⟩
    have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp hnonempty
    obtain ⟨E, hE, hsep, p, hp⟩ :=
      exists_point_finite_separable_intermediateField_of_smooth_algebra k Ω A
    change p ≫ Spec.map a = Spec.map (CommRingCat.ofHom (algebraMap k E)) at hp
    refine ⟨E, hE, hsep, p ≫ e.inv ≫ X.affineCover.f i, ?_⟩
    simpa only [a, Spec.map_preimage, Category.assoc] using hp

end AlgebraicGeometry
