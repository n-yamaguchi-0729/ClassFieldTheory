/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertAutomorphisms
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertSemilinear
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiniteGaloisMonodromyOperations
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Mathlib.FieldTheory.KrullTopology
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality

/-!
# Native abelian fixedness gives actual Hilbert--Picard fixedness

The original ambient automorphism supplies an automorphism of the actual
pointed Hilbert field. Literal monodromy computes its conjugation. A fixed
class in the original topological abelianization then gives a fixed class
under the original semilinear Picard action by Artin reciprocity.
-/

@[expose] public section

noncomputable section

universe u v w x y

open AlgebraicCurve ProCGroups.Abelian
open scoped IsMulCommutative

namespace FunctionField

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

variable {k : Type u} {E : Type v} {K : Type w} {F : Type x} {Ω : Type y}
    [Field k] [Finite k] [Field E] [Field K]
    [Field F] [Field Ω]
    [Algebra k K] [Algebra k E] [Algebra E K] [IsScalarTower k E K]
    [Module.Finite k E]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors E K]
    [Algebra F Ω] [Algebra K Ω]
    {P Γ : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [Group Γ]

/-- Fixedness in the original geometric abelianization implies fixedness
of its actual finite Hilbert--Picard class. The Hilbert automorphism and
the reciprocity conjugation square are constructed in the proof. -/
theorem constantHilbertPicard_fixed_of_native_conjugation
    (v : Place E K) (hv : v.deg = 1) :
    let H := hilbertClassField k K {v.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun a =>
        congrArg (algebraMap K (SeparableClosure K))
          (IsScalarTower.algebraMap_apply k (RatFunc k) K a))
    ∀ (q : Gal(Ω/F) →* P) (π : P →* Γ)
      (i : H.val →ₐ[K] Ω) (χ : π.ker →ₜ* Gal(H.val/K)),
      (∀ (σ : Gal(Ω/F)) (hσ : π (q σ) = 1) (a : H.val),
        i (χ ⟨q σ, hσ⟩ a) = σ (i a)) →
      ∀ (ρ : Gal(Ω/F)) (eK : K ≃ₐ[k] K) (g : SemilinearAut E K)
        (_ : eK.toRingEquiv = SemilinearAut.toRingAut g),
        (∀ a : K, ρ (algebraMap K Ω a) = algebraMap K Ω (eK a)) →
        SemilinearAut.ofAlgAut eK • v.forgetConstants (K := k) =
          v.forgetConstants (K := k) →
        ∀ (σ : Gal(Ω/F)) (hσ : π (q σ) = 1),
          TopologicalAbelianization.mk π.ker
              (MulAut.conjNormal (q ρ) ⟨q σ, hσ⟩) =
            TopologicalAbelianization.mk π.ker ⟨q σ, hσ⟩ →
          g • ((constantHilbertClassFieldGaloisEquivPic0 k E K v hv)
            (χ ⟨q σ, hσ⟩)).toAdd =
            ((constantHilbertClassFieldGaloisEquivPic0 k E K v hv)
              (χ ⟨q σ, hσ⟩)).toAdd := by
  intro H akS aRS hkKS hRKS hkRS q π i χ hχ ρ eK g hfield hρ hvfixed σ hσ hfixed
  obtain ⟨eH, heH, hbase⟩ := exists_hilbertClassFieldAutomorphism_of_fixed_place
    (v.forgetConstants (K := k)) Ω i eK ρ.toRingEquiv hρ hvfixed
  have hvalue : χ (MulAut.conjNormal (q ρ) ⟨q σ, hσ⟩) = χ ⟨q σ, hσ⟩ :=
    congrArg (TopologicalAbelianization.lift χ) hfixed
  have hconjugation := EtaleFundamentalGroups.finiteGaloisMonodromy_conjugation_source
    q π i χ.toMonoidHom hχ ρ eK.toRingEquiv eH.toRingEquiv hbase heH σ hσ
  have htarget : LocalClassFieldTheory.semilinearGaloisGroupCongr K K H.val H.val
      eK.toRingEquiv eH.toRingEquiv hbase (χ ⟨q σ, hσ⟩) = χ ⟨q σ, hσ⟩ :=
    hconjugation.symm.trans hvalue
  have hpic := constantHilbertClassFieldGaloisEquivPic0_conjugation
    v hv eK g hfield eH hbase (χ ⟨q σ, hσ⟩)
  rw [htarget] at hpic
  exact hpic.symm

end FunctionField
