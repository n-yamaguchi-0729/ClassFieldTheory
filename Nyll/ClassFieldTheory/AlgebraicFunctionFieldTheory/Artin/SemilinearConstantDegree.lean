/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.FieldIsomorphismRayNaturality
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree

/-!
# The actual constant degree under a semilinear field isomorphism

The original closure isomorphism carries the actual separable constants
to the actual separable constants. Their finite-base semilinear Frobenius
comparison preserves degree. Consequently the native Galois conjugation
of a semilinear function-field isomorphism preserves the original
arithmetic degree, even when the finite base-field automorphism is nontrivial.
-/

@[expose] public section

noncomputable section

open LocalClassFieldTheory

namespace FunctionField

section Constants

variable {k₁ k₂ Ω₁ Ω₂ : Type*}
  [Field k₁] [Finite k₁] [Field k₂] [Finite k₂]
  [Field Ω₁] [Field Ω₂] [Algebra k₁ Ω₁] [Algebra k₂ Ω₂]
  (τ : k₁ ≃+* k₂) (a : Ω₁ ≃+* Ω₂)
  (ha : ∀ c, a (algebraMap k₁ Ω₁ c) = algebraMap k₂ Ω₂ (τ c))

include ha in
/-- A semilinear field equivalence preserves the actual separable constant subfields. -/
theorem semilinear_mem_separableClosure (x : Ω₁) :
    x ∈ separableClosure k₁ Ω₁ ↔ a x ∈ separableClosure k₂ Ω₂ := by
  let : Algebra k₁ k₂ := τ.toRingHom.toAlgebra
  let : Algebra k₁ Ω₂ :=
    ((algebraMap k₂ Ω₂).comp τ.toRingHom).toAlgebra
  have : IsScalarTower k₁ k₂ Ω₂ := IsScalarTower.of_algebraMap_eq' rfl
  let ea : Ω₁ ≃ₐ[k₁] Ω₂ := { a with commutes' := ha }
  let et : k₁ ≃ₐ[k₁] k₂ := { τ with commutes' := fun _ => rfl }
  have : FiniteDimensional k₁ k₂ := et.toLinearEquiv.finiteDimensional
  have hconstants := separableClosure.eq_restrictScalars_of_isSeparable k₁ k₂ Ω₂
  have hmap : x ∈ separableClosure k₁ Ω₁ ↔ a x ∈ separableClosure k₁ Ω₂ :=
    (map_mem_separableClosure_iff ea.toAlgHom).symm
  rw [hconstants] at hmap
  exact hmap

/-- Restriction of the original semilinear closure map to its actual
constant subfields. On ambient elements this is literally the given map. -/
def semilinearConstantClosureEquiv :
    separableClosure k₁ Ω₁ ≃+* separableClosure k₂ Ω₂ where
  toFun x := ⟨a x.val, (semilinear_mem_separableClosure τ a ha x.val).mp x.property⟩
  invFun y := ⟨a.symm y.val, (semilinear_mem_separableClosure τ a ha (a.symm y.val)).mpr
    (by rw [a.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext (a.symm_apply_apply x.val)
  right_inv y := Subtype.ext (a.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul a x.val y.val)
  map_add' x y := Subtype.ext (map_add a x.val y.val)

/-- The original finite scalar square is retained inside the actual
constant closures. -/
theorem semilinearConstantClosureEquiv_algebraMap (c : k₁) :
    semilinearConstantClosureEquiv τ a ha
        (algebraMap k₁ (separableClosure k₁ Ω₁) c) =
      algebraMap k₂ (separableClosure k₂ Ω₂) (τ c) :=
  Subtype.ext (ha c)

end Constants

section Native

variable {k₁ k₂ K₁ K₂ : Type*}
  [Field k₁] [Finite k₁] [Field k₂] [Finite k₂]
  [Field K₁] [Field K₂] [Algebra k₁ K₁] [Algebra k₂ K₂]

variable (τ : k₁ ≃+* k₂) (Φ : K₁ ≃+* K₂)
  (hΦ : ∀ c, Φ (algebraMap k₁ K₁ c) = algebraMap k₂ K₂ (τ c))
  (a : SeparableClosure K₁ ≃+* SeparableClosure K₂)
  (ha : ∀ x, a (algebraMap K₁ (SeparableClosure K₁) x) =
    algebraMap K₂ (SeparableClosure K₂) (Φ x))

include hΦ in
/-- Native Galois conjugation by the actual field and closure
isomorphisms preserves the original finite-constant arithmetic degree. -/
theorem nativeFieldIsoGaloisEquiv_constantDegree
    (σ : Gal(SeparableClosure K₁/K₁)) :
    let _ : Algebra k₁ (SeparableClosure K₁) :=
      ((algebraMap K₁ (SeparableClosure K₁)).comp (algebraMap k₁ K₁)).toAlgebra
    let _ : Algebra k₂ (SeparableClosure K₂) :=
      ((algebraMap K₂ (SeparableClosure K₂)).comp (algebraMap k₂ K₂)).toAlgebra
    have _ : IsScalarTower k₁ K₁ (SeparableClosure K₁) :=
      IsScalarTower.of_algebraMap_eq' rfl
    have _ : IsScalarTower k₂ K₂ (SeparableClosure K₂) :=
      IsScalarTower.of_algebraMap_eq' rfl
    absoluteConstantDegree k₂ K₂ (SeparableClosure K₂)
        (nativeFieldIsoGaloisEquiv Φ a ha σ) =
      absoluteConstantDegree k₁ K₁ (SeparableClosure K₁) σ := by
  intro firstAlgebra secondAlgebra firstTower secondTower
  let _ : Fintype k₁ := Fintype.ofFinite k₁
  let _ : Fintype k₂ := Fintype.ofFinite k₂
  have hc (c : k₁) : a (algebraMap k₁ (SeparableClosure K₁) c) =
      algebraMap k₂ (SeparableClosure K₂) (τ c) := by
    change a (algebraMap K₁ (SeparableClosure K₁) (algebraMap k₁ K₁ c)) =
      algebraMap K₂ (SeparableClosure K₂) (algebraMap k₂ K₂ (τ c))
    rw [ha, hΦ]
  let C₁ := separableClosure k₁ (SeparableClosure K₁)
  let C₂ := separableClosure k₂ (SeparableClosure K₂)
  have : IsAlgClosed C₁ := IsAlgClosure.isAlgClosed (R := k₁) (K := C₁)
  have : IsAlgClosed C₂ := IsAlgClosure.isAlgClosed (R := k₂) (K := C₂)
  let e := semilinearConstantClosureEquiv τ a hc
  let δ := absoluteConstantRestriction k₁ K₁ (SeparableClosure K₁) σ
  let σ' := nativeFieldIsoGaloisEquiv Φ a ha σ
  let δ' := absoluteConstantRestriction k₂ K₂ (SeparableClosure K₂) σ'
  have hd := residueAbsoluteDegreeIn_semilinear_conjugation
    k₁ C₁ τ e (semilinearConstantClosureEquiv_algebraMap τ a hc) δ
  let δc : C₂ ≃ₐ[k₂] C₂ :=
    { e.symm.trans (δ.toRingEquiv.trans e) with
      commutes' := fun c => by
        change e (δ (e.symm (algebraMap k₂ C₂ c))) = algebraMap k₂ C₂ c
        have hpre : e.symm (algebraMap k₂ C₂ c) =
            algebraMap k₁ C₁ (τ.symm c) := by
          apply e.injective
          rw [e.apply_symm_apply, semilinearConstantClosureEquiv_algebraMap,
            τ.apply_symm_apply]
        rw [hpre, δ.commutes, semilinearConstantClosureEquiv_algebraMap,
          τ.apply_symm_apply] }
  have hδ : δc = δ' := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change a ((δ (e.symm x) : C₁) : SeparableClosure K₁) =
      (δ' x : SeparableClosure K₂)
    have hleft : ((δ (e.symm x) : C₁) : SeparableClosure K₁) =
        σ ((e.symm x : C₁) : SeparableClosure K₁) :=
      (σ.restrictScalars k₁).restrictNormal_commutes C₁ (e.symm x)
    have hright : ((δ' x : C₂) : SeparableClosure K₂) = σ' x.val :=
      (σ'.restrictScalars k₂).restrictNormal_commutes C₂ x
    calc
      a ((δ (e.symm x) : C₁) : SeparableClosure K₁) =
          a (σ (a.symm x.val)) := congrArg a hleft
      _ = σ' x.val := (nativeFieldIsoGaloisEquiv_apply Φ a ha σ x.val).symm
      _ = (δ' x : SeparableClosure K₂) := hright.symm
  change residueAbsoluteDegreeIn k₂ C₂ δc = residueAbsoluteDegreeIn k₁ C₁ δ at hd
  change residueAbsoluteDegreeIn k₂ C₂ δ' = residueAbsoluteDegreeIn k₁ C₁ δ
  rw [← hδ]
  exact hd

end Native

end FunctionField
