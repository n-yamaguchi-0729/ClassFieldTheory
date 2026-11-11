/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Separable

/-!
# A native closure extension of the original field isomorphism

The given field isomorphism supplies the source coefficients on the
target closure. Transporting separability gives an actual separable
closure of the source field and hence an extension of that same
isomorphism to the two native separable closures.
-/

@[expose] public section

noncomputable section

namespace GaloisCohomology

universe u v w z

variable {K : Type u} {F : Type v} {Ω : Type w}
  [Field K] [Field F] [Field Ω] [Algebra F Ω]
  (Φ : K ≃+* F)

/-- Source coefficients on the given target closure, through the
original field isomorphism. -/
@[reducible]
def fieldIsoClosureAlgebra : Algebra K Ω :=
  ((algebraMap F Ω).comp Φ.toRingHom).toAlgebra

/-- The same target closure is a separable closure of the source field
for these literal transported coefficients. -/
theorem fieldIsoClosure_isSepClosure [IsSepClosure F Ω] :
    let : Algebra K Ω := fieldIsoClosureAlgebra (Ω := Ω) Φ
    IsSepClosure K Ω := by
  intro aKΩ
  refine ⟨IsSepClosure.sep_closed F, ?_⟩
  apply Algebra.IsSeparable.of_equiv_equiv Φ.symm (RingEquiv.refl Ω)
  apply RingHom.ext
  intro x
  change algebraMap F Ω (Φ (Φ.symm x)) = algebraMap F Ω x
  rw [Φ.apply_symm_apply]

/-- The original field isomorphism extends to any two specified
separable closures, retaining their given coefficient maps. -/
def suppliedFieldIsoClosureEquiv
    (Ω₁ : Type w) (Ω₂ : Type z) [Field Ω₁] [Field Ω₂]
    [Algebra K Ω₁] [Algebra F Ω₂] [IsSepClosure K Ω₁] [IsSepClosure F Ω₂] :
    Ω₁ ≃+* Ω₂ := by
  let : Algebra K Ω₂ := fieldIsoClosureAlgebra (Ω := Ω₂) Φ
  have : IsSepClosure K Ω₂ := fieldIsoClosure_isSepClosure (Ω := Ω₂) Φ
  exact (IsSepClosure.equiv K Ω₁ Ω₂).toRingEquiv

/-- The selected supplied-closure extension agrees with the same
original field isomorphism on every actual coefficient. -/
theorem suppliedFieldIsoClosureEquiv_algebraMap
    (Ω₁ : Type w) (Ω₂ : Type z) [Field Ω₁] [Field Ω₂]
    [Algebra K Ω₁] [Algebra F Ω₂] [IsSepClosure K Ω₁] [IsSepClosure F Ω₂]
    (x : K) :
    suppliedFieldIsoClosureEquiv Φ Ω₁ Ω₂ (algebraMap K Ω₁ x) =
      algebraMap F Ω₂ (Φ x) := by
  let : Algebra K Ω₂ := fieldIsoClosureAlgebra (Ω := Ω₂) Φ
  have : IsSepClosure K Ω₂ := fieldIsoClosure_isSepClosure (Ω := Ω₂) Φ
  exact (IsSepClosure.equiv K Ω₁ Ω₂).commutes x

/-- The native closure extension is the specialization of the same
supplied-closure construction to the two native separable closures. -/
def nativeFieldIsoClosureEquiv : SeparableClosure K ≃+* SeparableClosure F :=
  suppliedFieldIsoClosureEquiv Φ (SeparableClosure K) (SeparableClosure F)

/-- The selected native closure map extends precisely the original
field isomorphism, on every original coefficient. -/
theorem nativeFieldIsoClosureEquiv_algebraMap (x : K) :
    nativeFieldIsoClosureEquiv Φ (algebraMap K (SeparableClosure K) x) =
      algebraMap F (SeparableClosure F) (Φ x) :=
  suppliedFieldIsoClosureEquiv_algebraMap Φ (SeparableClosure K) (SeparableClosure F) x

section NativeCoordinates

variable {Ω₁ : Type w} {Ω₂ : Type z} [Field Ω₁] [Field Ω₂]
  [Algebra K Ω₁] [Algebra F Ω₂]
  (a : Ω₁ ≃+* Ω₂)
  (e₁ : SeparableClosure K ≃ₐ[K] Ω₁) (e₂ : SeparableClosure F ≃ₐ[F] Ω₂)

/-- One specified ambient closure map in the actual native coordinates
of any two source fields. No new extension of a field map is selected. -/
def nativeClosureEquivOfSupplied : SeparableClosure K ≃+* SeparableClosure F :=
  e₁.toRingEquiv.trans (a.trans e₂.symm.toRingEquiv)

/-- Native coordinate transport retains the literal ambient closure
map on every original native element. -/
theorem nativeClosureEquivOfSupplied_apply (x : SeparableClosure K) :
    e₂ (nativeClosureEquivOfSupplied a e₁ e₂ x) = a (e₁ x) :=
  e₂.apply_symm_apply _

/-- If the single ambient map extends a specified field map, its native
coordinate expression extends exactly that same field map. -/
theorem nativeClosureEquivOfSupplied_algebraMap
    (ha : ∀ x, a (algebraMap K Ω₁ x) = algebraMap F Ω₂ (Φ x)) (x : K) :
    nativeClosureEquivOfSupplied a e₁ e₂ (algebraMap K (SeparableClosure K) x) =
      algebraMap F (SeparableClosure F) (Φ x) := by
  apply e₂.injective
  rw [nativeClosureEquivOfSupplied_apply, e₁.commutes, ha, e₂.commutes]

end NativeCoordinates

end GaloisCohomology
