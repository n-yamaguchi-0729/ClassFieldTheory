/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.EmbeddedAbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Nyll.ValuedFieldTheory.LocalField.NormUnits
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct
public import Nyll.GaloisCohomology.Cyclic.IntegralTateZeroTransfers
public import Nyll.GaloisCohomology.Cyclic.TateH0.Invariants
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology

/-! # Degree-zero Tate corestriction on field units -/

@[expose] public section

noncomputable section

open CategoryTheory FunctionField LocalFieldTheory
open scoped BigOperators

namespace ClassFieldTheory.Brauer

universe u v

open IntegralGroupCohomology.Universe

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] (F : IntermediateField K L)
  (i : L →ₐ[K] SeparableClosure K)

local notation "G" => Gal(L/K)
local notation "H" => F.fixingSubgroup
local notation "U" => Rep.ofAlgebraAutOnUnits K L

/-- Restricting an actual coset representative to the intermediate field
gives the corresponding embedding into the chosen separable closure. -/
def localNormCosetEmbedding (q : G ⧸ H) : F →ₐ[K] SeparableClosure K :=
  Quotient.liftOn' q (fun g => i.comp (g.toAlgHom.comp F.val)) (by
    intro g h hgh
    have hfix : g⁻¹ * h ∈ H := QuotientGroup.leftRel_apply.mp hgh
    apply AlgHom.ext
    intro a
    have ha := (IntermediateField.mem_fixingSubgroup_iff F _).mp hfix a.val a.property
    have hh : g⁻¹ (h a.val) = a.val := ha
    exact congrArg i ((g.symm_apply_eq).mp hh).symm)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Reading the coset through `out` gives the same embedding. -/
theorem localNormCosetEmbedding_out (q : G ⧸ H) (a : F) :
    localNormCosetEmbedding K L F i q a = i (q.out a.val) := by
  exact congrArg (fun z : G ⧸ H => localNormCosetEmbedding K L F i z a) q.out_eq.symm

/-- Each base-field embedding is represented by a unique coset of the
subgroup fixing the intermediate field. -/
def localNormCosetEmbeddingEquiv : (G ⧸ H) ≃ (F →ₐ[K] SeparableClosure K) := by
  apply Equiv.ofBijective (localNormCosetEmbedding K L F i)
  constructor
  · intro q r h
    have hfix : q.out⁻¹ * r.out ∈ H := by
      apply (IntermediateField.mem_fixingSubgroup_iff F _).2
      intro a ha
      have he (z : G ⧸ H) := localNormCosetEmbedding_out K L F i z (⟨a, ha⟩ : F)
      have heq := congrArg (fun f : F →ₐ[K] SeparableClosure K => f ⟨a, ha⟩) h
      have hqr : q.out a = r.out a := i.injective ((he q).symm.trans (heq.trans (he r)))
      change q.out⁻¹ (r.out a) = a
      rw [← hqr]
      exact q.out.symm_apply_apply a
    exact q.out_eq.symm.trans ((QuotientGroup.eq.mpr hfix).trans r.out_eq)
  · intro g
    let : Algebra.IsSeparable F L := Algebra.isSeparable_tower_top_of_isSeparable K F L
    obtain ⟨j, hj⟩ := (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := K) (L := F) (M := SeparableClosure K) (E := L)) g
    obtain ⟨σ, hσ⟩ :=
      AlgebraicNumberTheory.exists_separableClosureEmbeddingComparisonAutomorphism i j
    refine ⟨QuotientGroup.mk (embeddedFiniteRestriction K L i σ), ?_⟩
    apply AlgHom.ext
    intro a
    change i (embeddedFiniteRestriction K L i σ a.val) = g a
    rw [embeddedFiniteRestriction_commutes, hσ]
    exact congrArg (fun f : F →ₐ[K] SeparableClosure K => f a) hj

/-- An intermediate-field unit is an original fixed vector for its fixing subgroup. -/
def localIntermediateUnitFixedVector (a : Fˣ) : (Rep.res (H).subtype U).ρ.invariants :=
  ⟨Additive.ofMul (Units.map F.val.toMonoidHom a), fun g => by
    apply Additive.toMul.injective
    apply Units.ext
    exact (IntermediateField.mem_fixingSubgroup_iff F g.val).mp g.property _ (a : F).property⟩

/-- The actual finite coset norm of an intermediate-field unit is the field norm. -/
theorem localCorestrictInvariants_baseUnit [Fintype ((L ≃ₐ[K] L) ⧸ F.fixingSubgroup)] (a : Fˣ) :
    corestrictInvariants H U (localIntermediateUnitFixedVector K L F a) =
      CyclicCohomology.baseUnitToInvariantUnit K L (normUnits K F a) := by
  let Ω := SeparableClosure K
  let i : L →ₐ[K] Ω := IsSepClosed.lift
  let e := localNormCosetEmbeddingEquiv K L F i
  let : Fintype (F →ₐ[K] Ω) :=
    PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable K F)
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  apply i.injective
  change i (((Additive.toMul (show Additive Lˣ from
      relativeNorm H U (localIntermediateUnitFixedVector K L F a))) : Lˣ) : L) =
    i (algebraMap K L (Algebra.norm K (a : F)))
  simp only [relativeNorm, LinearMap.sum_apply]
  rw [i.commutes]
  change (i.toMonoidHom.comp (Units.coeHom L))
      (∏ q : G ⧸ H, Additive.toMul ((U).ρ q.out (localIntermediateUnitFixedVector K L F a))) = _
  rw [map_prod]
  calc
    _ = ∏ g : F →ₐ[K] Ω, g (a : F) :=
      Fintype.prod_equiv e _ _ (fun q => (localNormCosetEmbedding_out K L F i q (a : F)).symm)
    _ = algebraMap K Ω (Algebra.norm K (a : F)) :=
      (LocalClassFieldTheory.algebraMap_norm_eq_prod_embeddings_of_isSepClosed K Ω F (a : F)).symm

/-- The fixing subgroup expressed in the single group lift used in Tate cup. -/
abbrev localLiftedFixingSubgroup : Subgroup (ULift.{v} G) :=
  (H).comap (MulEquiv.ulift : ULift.{v} G ≃* G).toMonoidHom

local notation "T" => localLiftedFixingSubgroup K L F
/-- The actual field unit representation in the auxiliary Tate carrier. -/
abbrev localLiftedUnitsRep : Rep.{v} ℤ (ULift.{v} G) :=
  (Rep.universeLiftFunctor ℤ G).obj U

local notation "V" => localLiftedUnitsRep K L

/-- The same intermediate unit in the Tate cup's auxiliary carrier. -/
def localLiftedIntermediateUnitFixedVector (a : Fˣ) : (Rep.res (T).subtype V).ρ.invariants :=
  ⟨ULift.up (localIntermediateUnitFixedVector K L F a).val, fun g =>
    ULift.ext ((localIntermediateUnitFixedVector K L F a).property ⟨g.val.down, g.property⟩)⟩

/-- The finite coset norm still gives the same field norm in the auxiliary lift. -/
theorem localLiftedCorestrictInvariants_baseUnit [Fintype (ULift.{v} G ⧸ T)]
    (a : Fˣ) :
    corestrictInvariants T V (localLiftedIntermediateUnitFixedVector K L F a) =
      ⟨ULift.up (CyclicCohomology.baseUnitToInvariantUnit K L (normUnits K F a)).val, fun g =>
        ULift.ext
          ((CyclicCohomology.baseUnitToInvariantUnit K L (normUnits K F a)).property g.down)⟩ := by
  let : Fintype ((L ≃ₐ[K] L) ⧸ F.fixingSubgroup) := Fintype.ofFinite _
  let b := localIntermediateUnitFixedVector K L F a
  let c := localLiftedIntermediateUnitFixedVector K L F a
  let n := CyclicCohomology.baseUnitToInvariantUnit K L (normUnits K F a)
  let e : ULift.{v} G ≃* G := MulEquiv.ulift
  let q : (ULift.{v} G ⧸ T) ≃ (G ⧸ H) := Quotient.congr e.toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    change e (x⁻¹ * y) ∈ H ↔ e x ⁻¹ * e y ∈ H
    rw [map_mul, map_inv])
  let d : V ≃ₗ[ℤ] U := (ULift.moduleEquiv : ULift.{v} U ≃ₗ[ℤ] U)
  have hn : relativeNorm H U b = n.val :=
    congrArg (fun z : (U).ρ.invariants => z.val) (localCorestrictInvariants_baseUnit K L F a)
  apply Subtype.ext
  apply d.injective
  change d (relativeNorm T V c) = n.val
  rw [← hn]
  simp only [relativeNorm, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv q _ _ (fun s => ?_)
  change (U).ρ (e s.out) b.val = (U).ρ (q s).out b.val
  have hs : QuotientGroup.mk (e s.out) = q s :=
    congrArg q (QuotientGroup.out_eq' s)
  have ht : (q s).out⁻¹ * e s.out ∈ H :=
    QuotientGroup.eq.mp ((QuotientGroup.out_eq' (q s)).trans hs.symm)
  let h : H := ⟨(q s).out⁻¹ * e s.out, ht⟩
  have he : e s.out = (q s).out * h.val := (mul_inv_cancel_left _ _).symm
  have hb : (U).ρ h.val b.val = b.val := b.property h
  rw [he, map_mul, mul_apply_eq_comp, hb]

end ClassFieldTheory.Brauer
