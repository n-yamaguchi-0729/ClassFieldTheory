/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteRestrictionKernel
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalInvariant

/-! # The local fundamental class in finite field-unit cohomology -/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology
open ClassFieldTower.Cohomology LocalFieldTheory Module
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K]

attribute [local instance] stageSeparableClosureAlgebra

variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))

/-- The finite relative Brauer group injects onto the absolute restriction
kernel for the original finite normal extension. -/
theorem mem_range_finiteInflation_iff_restriction_eq_zero
    (j : (SeparableClosure K) ≃ₐ[E] SeparableClosure E) (x : Br K) :
    x ∈ (finiteInflation E).range ↔
      embeddedAbsoluteBrRestriction K E.toIntermediateField j x = 0 := by
  have h : embeddedAbsoluteBrRestriction K E.toIntermediateField j =
      restrict (algebraMap K (↥E.toIntermediateField)) :=
    restrictOfEmbedding_eq_of_extends (algebraMap K (↥E.toIntermediateField))
      (embeddedAbsoluteRestrictionHom K E.toIntermediateField j) j.toRingEquiv.toRingHom
      (fun a => j.commutes (algebraMap K E a))
      (embeddedAbsoluteRestrictionHom_commutes K E.toIntermediateField j)
  rw [finiteInflation_range_eq_ker, AddMonoidHom.mem_ker]
  exact Iff.of_eq (congrArg (fun f : Br K →+ Br E => f x = 0) h.symm)

section LocalInvariant

variable (K) [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The invariant of a relative class is its canonical absolute invariant
after actual inflation. -/
def relativeLocalBrauerInvariant : relativeBr E →+ AddCircle (1 : ℚ) :=
  (localBrauerInvariant K).comp (finiteInflation E)

/-- The invariant image of the actual finite relative classes is the
torsion subgroup cut out by the degree of the extension. -/
theorem mem_range_relativeLocalBrauerInvariant_iff (z : AddCircle (1 : ℚ)) :
    z ∈ (relativeLocalBrauerInvariant K E).range ↔ finrank K E • z = 0 := by
  let : Algebra.IsSeparable E (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K E (SeparableClosure K)
  let : IsSepClosure E (SeparableClosure K) := ⟨inferInstance, inferInstance⟩
  let j := IsSepClosure.equiv E (SeparableClosure K) (SeparableClosure E)
  obtain ⟨x, rfl⟩ := (localBrauerInvariantEquiv K).surjective z
  change localBrauerInvariant K x ∈ (relativeLocalBrauerInvariant K E).range ↔
    finrank K E • localBrauerInvariant K x = 0
  rw [← embeddedAbsoluteBrRestriction_eq_zero_iff K E.toIntermediateField j x,
    ← mem_range_finiteInflation_iff_restriction_eq_zero E j x]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (localBrauerInvariantEquiv K).injective hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

/-- Canonical coordinates and their equality with the additive circle invariant. -/
def relativeLocalBrauerInvariantCoordinates :
    { e : relativeBr E ≃+ ZMod (finrank K E) //
      ∀ x : relativeBr E, zmodToRationalCircle (finrank K E) Module.finrank_pos (e x) =
        relativeLocalBrauerInvariant K E x } := by
  let d := finrank K E
  let hd : 0 < d := Module.finrank_pos
  let q := zmodToRationalCircle d hd
  let f := relativeLocalBrauerInvariant K E
  let S := f.range
  let g := f.codRestrict S (fun a => ⟨a, rfl⟩)
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      exact finiteInflation_injective E
        ((localBrauerInvariantEquiv K).injective (congrArg Subtype.val hab))
    · rintro ⟨z, ⟨x, rfl⟩⟩
      exact ⟨x, rfl⟩
  let q' := q.codRestrict S (fun a => (mem_range_relativeLocalBrauerInvariant_iff K E _).2
    ((mem_range_zmodToRationalCircle_iff d hd _).1 ⟨a, rfl⟩))
  have hq : Function.Bijective q' := by
    constructor
    · intro a b hab
      exact zmodToRationalCircle_injective d hd (congrArg Subtype.val hab)
    · intro z
      obtain ⟨a, ha⟩ := (mem_range_zmodToRationalCircle_iff d hd _).2
        ((mem_range_relativeLocalBrauerInvariant_iff K E z.val).1 z.property)
      exact ⟨a, Subtype.ext ha⟩
  let e := AddEquiv.ofBijective g hg
  let r := AddEquiv.ofBijective q' hq
  refine ⟨e.trans r.symm, fun x => ?_⟩
  change (r (r.symm (e x))).val = (e x).val
  exact congrArg (fun z : S => z.val) (r.apply_symm_apply (e x))

/-- The finite relative Brauer group in canonical invariant coordinates. -/
def relativeLocalBrauerInvariantEquiv : relativeBr E ≃+ ZMod (finrank K E) :=
  (relativeLocalBrauerInvariantCoordinates K E).val

/-- The invariant coordinates use the original inclusion of fractions
with denominator the degree. -/
theorem relativeLocalBrauerInvariantEquiv_apply (x : relativeBr E) :
    zmodToRationalCircle (finrank K E) Module.finrank_pos
      (relativeLocalBrauerInvariantEquiv K E x) = relativeLocalBrauerInvariant K E x :=
  (relativeLocalBrauerInvariantCoordinates K E).property x

/-- The arithmetic fundamental class of the finite embedded extension,
defined in its original field-unit cohomology. -/
def localFundamentalClass : relativeBr E := (relativeLocalBrauerInvariantEquiv K E).symm 1

theorem relativeLocalBrauerInvariant_fundamentalClass :
    relativeLocalBrauerInvariant K E (localFundamentalClass K E) =
      (((1 : ℚ) / (finrank K E : ℕ) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← relativeLocalBrauerInvariantEquiv_apply K E, localFundamentalClass,
    AddEquiv.apply_symm_apply]
  simpa only [Int.cast_one] using
    zmodToRationalCircle_intCast (finrank K E) Module.finrank_pos 1

/-- The local fundamental class generates the actual finite relative
cohomology group. -/
theorem localFundamentalClass_addOrder :
    addOrderOf (localFundamentalClass K E) = finrank K E := by
  exact ((relativeLocalBrauerInvariantEquiv K E).symm.addOrderOf_eq (1 : ZMod (finrank K E))).trans
    (ZMod.addOrderOf_one (finrank K E))

/-- The finite relative cohomology has the arithmetic degree as its order. -/
theorem relativeBr_natCard : Nat.card (relativeBr E) = finrank K E :=
  (Nat.card_congr (relativeLocalBrauerInvariantEquiv K E).toEquiv).trans (Nat.card_zmod _)

end LocalInvariant

section OriginalExtension

universe v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] (i : L →ₐ[K] SeparableClosure K)

/-- The original extension embedded as the finite stage used by the local invariant. -/
def fundamentalClassStage : FiniteGaloisIntermediateField K (SeparableClosure K) :=
  i.finiteGaloisFieldRange

/-- The actual relative cohomology comparison for the chosen embedded finite stage. -/
def fundamentalClassStageEquiv :
    continuousCohomology 2 (galoisUnitsRep K L) ≃+ relativeBr (fundamentalClassStage K L i) :=
  continuousRelativeUnitsH2Congr K L (fundamentalClassStage K L i) i.equivFieldRange

/-- The invariant of a relative class on the original extension, through
the specified embedding into the chosen separable closure. -/
def relativeLocalBrauerInvariantOfEmbedding :
    continuousCohomology 2 (galoisUnitsRep K L) →+ AddCircle (1 : ℚ) :=
  (relativeLocalBrauerInvariant K (fundamentalClassStage K L i)).comp
    (fundamentalClassStageEquiv K L i).toAddMonoidHom

/-- The arithmetic fundamental class on the original field-unit
representation. The upper and lower fields can lie in independent universes. -/
def localFundamentalClassOfEmbedding : continuousCohomology 2 (galoisUnitsRep K L) :=
  (fundamentalClassStageEquiv K L i).symm (localFundamentalClass K (fundamentalClassStage K L i))

theorem relativeLocalBrauerInvariantOfEmbedding_fundamentalClass :
    relativeLocalBrauerInvariantOfEmbedding K L i (localFundamentalClassOfEmbedding K L i) =
      (((1 : ℚ) / (finrank K L : ℕ) : ℚ) : AddCircle (1 : ℚ)) := by
  let E := fundamentalClassStage K L i
  let e := fundamentalClassStageEquiv K L i
  change relativeLocalBrauerInvariant K E (e (e.symm (localFundamentalClass K E))) = _
  have hdegree : finrank K L = finrank K (↥E.toIntermediateField) :=
    i.equivFieldRange.toLinearEquiv.finrank_eq
  rw [e.apply_symm_apply, relativeLocalBrauerInvariant_fundamentalClass K E, ← hdegree]

end OriginalExtension

end ClassFieldTheory.Brauer
