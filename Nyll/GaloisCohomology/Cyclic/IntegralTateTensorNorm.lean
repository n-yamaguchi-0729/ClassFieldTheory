/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTraceVanishing
public import Nyll.GaloisCohomology.GroupTheory.TensorInvariant
public import Nyll.GaloisCohomology.GroupTheory.RepresentationTensor

/-!
# Norm coefficients act trivially on the original Tate groups

Tensoring with a norm induces zero in every integer Tate degree. This gives
the bilinear tensor pairing with a degree-zero Tate class.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped RepTensor TensorProduct

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- Tensoring with a norm induces zero on the actual integral Tate groups
in every integer degree. -/
theorem tate_map_tensorInvariant_eq_zero (A B : Rep.{u} ℤ G)
    (y : B.ρ.invariants) (hy : (y : B) ∈ LinearMap.range B.ρ.norm) (n : ℤ) :
    (tateFunctor G n).map (Rep.tensorInvariant A B y) = 0 := by
  obtain ⟨z, hz⟩ := hy
  rw [Rep.tensorInvariant_eq_trace_of_norm.{0, u, 0} A B y z hz.symm]
  exact tate_map_trivialSubgroupTrace_eq_zero (Rep.tensorTrivialSubgroupMap A B z) n

/-- Tensoring with an invariant coefficient acts linearly on the Tate groups. -/
def tensorInvariantOnTate (A B : Rep.{u} ℤ G) (n : ℤ) :
    B.ρ.invariants →ₗ[ℤ] tate A n →ₗ[ℤ] tate (A ⊗ᵣ B) n := by
  let C := A ⊗ᵣ B
  let f : B.ρ.invariants →+ (tate A n →ₗ[ℤ] tate C n) :=
    ModuleCat.homAddEquiv.toAddMonoidHom.comp
      ((tateFunctor G n).mapAddHom.comp (Rep.tensorInvariantLinear A B).toAddMonoidHom)
  exact f.toIntLinearMap

/-- The original norm image lies in the kernel of the tensor action. -/
theorem fixedNormSubmodule_le_ker_tensorInvariantOnTate (A B : Rep.{u} ℤ G) (n : ℤ) :
    fixedNormSubmodule B ≤ LinearMap.ker (tensorInvariantOnTate A B n) := by
  intro y hy
  change (y : B) ∈ LinearMap.range B.ρ.norm at hy
  change ((tateFunctor G n).map (Rep.tensorInvariant A B y)).hom = 0
  rw [tate_map_tensorInvariant_eq_zero A B y hy n, ModuleCat.hom_zero]

/-- The tensor cup pairing with a degree-zero class is induced by tensoring
with an actual fixed representative. Norm representatives act by zero. -/
def tensorCupZeroRight (A B : Rep.{u} ℤ G) (n : ℤ) :
    tate A n →ₗ[ℤ] tate B 0 →ₗ[ℤ] tate (A ⊗ᵣ B) n := by
  let f : tate B 0 →ₗ[ℤ] tate A n →ₗ[ℤ] tate (A ⊗ᵣ B) n :=
    ((fixedNormSubmodule B).liftQ (tensorInvariantOnTate A B n)
      (fixedNormSubmodule_le_ker_tensorInvariantOnTate A B n)).comp
        (tateZeroEquivFixedQuotient B).toIntLinearEquiv.toLinearMap
  let linear {M N : Type u} [AddCommGroup M] [AddCommGroup N]
      [m : Module ℤ M] [n : Module ℤ N] (p : M →+ N) : M →ₗ[ℤ] N :=
    { toFun := p, map_add' := p.map_add
      map_smul' := fun z x => (congrArg p (int_smul_eq_zsmul m z x)).trans
        ((map_zsmul p z x).trans (int_smul_eq_zsmul n z (p x)).symm) }
  let eval (x : tate A n) : (tate A n →ₗ[ℤ] tate (A ⊗ᵣ B) n) →+ tate (A ⊗ᵣ B) n :=
    { toFun := fun j => j x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let flip : tate A n →+ (tate B 0 →ₗ[ℤ] tate (A ⊗ᵣ B) n) :=
    { toFun := fun x => linear ((eval x).comp f.toAddMonoidHom)
      map_zero' := LinearMap.ext fun y => map_zero (f y)
      map_add' := fun x z => LinearMap.ext fun y => map_add (f y) x z }
  exact linear flip

/-- The pairing acts by the original equivariant tensor map of the fixed vector. -/
theorem tensorCupZeroRight_fixedClass (A B : Rep.{u} ℤ G) (n : ℤ)
    (x : tate A n) (y : B.ρ.invariants) :
    tensorCupZeroRight A B n x (fixedClass B y) =
      (tateFunctor G n).map (Rep.tensorInvariant A B y) x := by
  change ((fixedNormSubmodule B).liftQ (tensorInvariantOnTate A B n)
    (fixedNormSubmodule_le_ker_tensorInvariantOnTate A B n)
    (tateZeroEquivFixedQuotient B (fixedClass B y))) x = _
  rw [tateZeroEquivFixedQuotient_fixedClass]
  have h := DFunLike.congr_fun ((fixedNormSubmodule B).liftQ_mkQ
    (tensorInvariantOnTate A B n) (fixedNormSubmodule_le_ker_tensorInvariantOnTate A B n)) y
  exact DFunLike.congr_fun h x

/-- In degree zero on both inputs the pairing sends the two fixed classes to
the class of their elementary tensor for the original diagonal action. -/
theorem tensorCupZeroRight_fixedClasses (A B : Rep.{u} ℤ G)
    (x : A.ρ.invariants) (y : B.ρ.invariants) :
    tensorCupZeroRight A B 0 (fixedClass A x) (fixedClass B y) =
      fixedClass (A ⊗ᵣ B)
        ⟨(x : A) ⊗ₜ[ℤ] (y : B), fun g => by
          change (A.ρ.tprod B.ρ) g ((x : A) ⊗ₜ[ℤ] (y : B)) = _
          rw [Representation.tprod_apply, TensorProduct.map_tmul,
            x.property g, y.property g]⟩ := by
  rw [tensorCupZeroRight_fixedClass]
  exact fixedClass_map (Rep.tensorInvariant A B y) x

/-- The degree-zero cup pairing commutes with the actual tensor of two
equivariant coefficient maps. -/
theorem tensorCupZeroRight_natural {A B C D : Rep.{u} ℤ G}
    (f : A ⟶ C) (g : B ⟶ D) (n : ℤ) (x : tate A n) (y : tate B 0) :
    (tateFunctor G n).map (f ⊗ᵣₘ g) (tensorCupZeroRight A B n x y) =
      tensorCupZeroRight C D n ((tateFunctor G n).map f x) ((tateFunctor G 0).map g y) := by
  obtain ⟨b, rfl⟩ := fixedClass_surjective B y
  let d : D.ρ.invariants := ⟨g b, fun h => by rw [← Rep.hom_comm_apply, b.property h]⟩
  have hd : (tateFunctor G 0).map g (fixedClass B b) = fixedClass D d := fixedClass_map g b
  rw [tensorCupZeroRight_fixedClass, hd, tensorCupZeroRight_fixedClass]
  have hdiag : Rep.tensorInvariant A B b ≫ (f ⊗ᵣₘ g) = f ≫ Rep.tensorInvariant C D d := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro a
    change TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap (a ⊗ₜ[ℤ] (b : B)) =
      f a ⊗ₜ[ℤ] g b
    exact TensorProduct.map_tmul f.hom.toLinearMap g.hom.toLinearMap a (b : B)
  change ((tateFunctor G n).map (Rep.tensorInvariant A B b) ≫
    (tateFunctor G n).map (f ⊗ᵣₘ g)) x =
    ((tateFunctor G n).map f ≫ (tateFunctor G n).map (Rep.tensorInvariant C D d)) x
  let F := tateFunctor G n
  have h := ((F.map_comp (Rep.tensorInvariant A B b) (f ⊗ᵣₘ g)).symm.trans
    (congrArg (fun j : A ⟶ C ⊗ᵣ D => F.map j) hdiag)).trans
      (F.map_comp f (Rep.tensorInvariant C D d))
  exact ConcreteCategory.congr_hom h x

end IntegralGroupCohomology.Universe
