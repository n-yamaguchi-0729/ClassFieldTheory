/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.Reduced.ModuleProjectiveReduced
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Nilpotent.Defs
public import Nyll.SchemeTheory.Cohomology.Sheaves.CoherentBaseChange
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Basic

/-!
Projective kernels of two-term complexes over a reduced ring.
Constant fibre-kernel dimension gives projectivity and bijective kernel base change.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const

noncomputable section

universe u v w

open scoped TensorProduct
open _root_.CoherentBaseChange

namespace CBCSol

section SplitKer

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Retract the source onto the kernel using a section of the differential. -/
def kerRetraction (d : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : d ∘ₗ s = LinearMap.id) :
    M →ₗ[R] LinearMap.ker d :=
  (LinearMap.id - s ∘ₗ d).codRestrict (LinearMap.ker d) (fun x => by
    simp only [LinearMap.mem_ker, map_sub, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, ← LinearMap.comp_apply d s, hs, sub_self])

theorem kerRetraction_apply_coe (d : M →ₗ[R] N) {s : N →ₗ[R] M}
    (hs : d ∘ₗ s = LinearMap.id) (x : M) :
    (kerRetraction d hs x : M) = x - s (d x) := rfl

theorem kerRetraction_comp_subtype (d : M →ₗ[R] N) {s : N →ₗ[R] M}
    (hs : d ∘ₗ s = LinearMap.id) :
    (kerRetraction d hs) ∘ₗ (LinearMap.ker d).subtype = LinearMap.id := by
  ext ⟨x, hx⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply,
    kerRetraction_apply_coe, LinearMap.mem_ker.mp hx, map_zero, sub_zero]

variable (A : Type*) [CommRing A] [Algebra R A]

/-- The canonical map from the base-changed kernel to the kernel of the base-changed map. -/
def kerBaseChangeHomOf (d : M →ₗ[R] N) :
    A ⊗[R] (LinearMap.ker d) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  ((LinearMap.ker d).subtype.baseChange A).codRestrict (LinearMap.ker (d.baseChange A)) (fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    suffices h : d ∘ₗ (LinearMap.ker d).subtype = 0 by
      rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply]
    ext ⟨y, hy⟩; exact hy)

theorem kerBaseChangeHomOf_apply_coe (d : M →ₗ[R] N) (x : A ⊗[R] (LinearMap.ker d)) :
    (kerBaseChangeHomOf A d x : A ⊗[R] M) = (LinearMap.ker d).subtype.baseChange A x := rfl

theorem kerBaseChangeHomOf_bijective [Module.Projective R N] (d : M →ₗ[R] N)
    (hd : Function.Surjective d) :
    Function.Bijective (kerBaseChangeHomOf A d) := by
  obtain ⟨s, hs⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hd)
  refine ⟨?_, ?_⟩
  · have hri : ((kerRetraction d hs).baseChange A) ∘ₗ ((LinearMap.ker d).subtype.baseChange A)
        = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, kerRetraction_comp_subtype, LinearMap.baseChange_id]
    intro x y hxy
    have heq : (kerRetraction d hs).baseChange A ((LinearMap.ker d).subtype.baseChange A x)
        = (kerRetraction d hs).baseChange A ((LinearMap.ker d).subtype.baseChange A y) := by
      rw [← kerBaseChangeHomOf_apply_coe, ← kerBaseChangeHomOf_apply_coe, hxy]
    simpa only [← LinearMap.comp_apply, hri, LinearMap.id_apply] using heq
  · rintro ⟨y, hy⟩
    have hyk : y ∈ LinearMap.ker (d.lTensor A) := by
      rwa [LinearMap.mem_ker, ← d.baseChange_eq_lTensor, ← LinearMap.mem_ker]
    obtain ⟨x, hx⟩ := (lTensor_exact A (LinearMap.exact_subtype_ker_map d) hd y).mp hyk
    refine ⟨x, Subtype.ext ?_⟩
    simp only [kerBaseChangeHomOf_apply_coe, LinearMap.baseChange_eq_lTensor]
    exact hx

theorem projective_ker_of_surjective_of_projective
    [Module.Projective R M] [Module.Projective R N]
    (d : M →ₗ[R] N) (hd : Function.Surjective d) :
    Module.Projective R (LinearMap.ker d) := by
  obtain ⟨s, hs⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hd)
  exact Module.Projective.of_split (LinearMap.ker d).subtype (kerRetraction d hs)
    (kerRetraction_comp_subtype d hs)

theorem finite_ker_of_surjective_of_projective
    [Module.Finite R M] [Module.Projective R N]
    (d : M →ₗ[R] N) (hd : Function.Surjective d) :
    Module.Finite R (LinearMap.ker d) := by
  obtain ⟨s, hs⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hd)
  exact Module.Finite.of_surjective (kerRetraction d hs)
    (Function.LeftInverse.surjective
      (congrFun <| congrArg DFunLike.coe <| kerRetraction_comp_subtype d hs))

end SplitKer

section FittingFree

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The residue field at a prime of the base ring. -/
abbrev κ (𝔭 : PrimeSpectrum R) : Type u := 𝔭.asIdeal.ResidueField

theorem span_one_tmul_eq_top (𝔭 : PrimeSpectrum R) :
    Submodule.span (κ 𝔭) (Set.range fun x : M => (1 : κ 𝔭) ⊗ₜ[R] x) = ⊤ :=
  open _root_.AlgebraicCurves.Foundations.Algebra.Proofs in
  open Module_projective_of_isReduced_of_finrank_fiber_const.CBCSol renaming
    span_one_tmul_eq_top → sharedProof in
  sharedProof (M := M) 𝔭

theorem exists_basis_one_tmul [Module.Finite R M] (𝔭 : PrimeSpectrum R) :
    ∃ (ι : Type v) (_ : Fintype ι) (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M)),
      ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i :=
  open _root_.AlgebraicCurves.Foundations.Algebra.Proofs in
  open Module_projective_of_isReduced_of_finrank_fiber_const.CBCSol renaming
    exists_basis_one_tmul → sharedProof in
  sharedProof (M := M) 𝔭

theorem subsingleton_residue_tensor_coker (𝔭 : PrimeSpectrum R) {ι : Type v} [Fintype ι]
    (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M)) (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) :
    Subsingleton (κ 𝔭 ⊗[R] (M ⧸ LinearMap.range (Fintype.linearCombination R m))) :=
  open _root_.AlgebraicCurves.Foundations.Algebra.Proofs in
  open Module_projective_of_isReduced_of_finrank_fiber_const.CBCSol renaming
    subsingleton_residue_tensor_coker → sharedProof in
  sharedProof 𝔭 m b hb

theorem baseChange_injective_of_le [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) {ι : Type v}
    [Fintype ι] (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) {𝔮 : PrimeSpectrum R} (hle : 𝔮 ≤ 𝔭) :
    Function.Injective ((Fintype.linearCombination R m).baseChange (κ 𝔮)) :=
  open _root_.AlgebraicCurves.Foundations.Algebra.Proofs in
  open Module_projective_of_isReduced_of_finrank_fiber_const.CBCSol renaming
    baseChange_injective_of_le → sharedProof in
  sharedProof hconst 𝔭 m b hb hle

theorem coeff_mem_of_rel [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) {ι : Type v} [Fintype ι]
    (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) {𝔮 : PrimeSpectrum R} (hle : 𝔮 ≤ 𝔭)
    (x : ι → R) (hx : Fintype.linearCombination R m x = 0) (i : ι) : x i ∈ 𝔮.asIdeal :=
  open _root_.AlgebraicCurves.Foundations.Algebra.Proofs in
  open Module_projective_of_isReduced_of_finrank_fiber_const.CBCSol renaming
    coeff_mem_of_rel → sharedProof in
  sharedProof hconst 𝔭 m b hb hle x hx i

theorem algebraMap_coeff_eq_zero [IsReduced R] [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R)
    {ι : Type v} [Fintype ι] (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i)
    (x : ι → R) (hx : Fintype.linearCombination R m x = 0) (i : ι) :
    algebraMap R (Localization.AtPrime 𝔭.asIdeal) (x i) = 0 :=
  open _root_.AlgebraicCurves.Foundations.Algebra.Proofs in
  open Module_projective_of_isReduced_of_finrank_fiber_const.CBCSol renaming
    algebraMap_coeff_eq_zero → sharedProof in
  sharedProof hconst 𝔭 m b hb x hx i

theorem free_localizedModule_of_isReduced [IsReduced R] [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) :
    Module.Free (Localization.AtPrime 𝔭.asIdeal)
      (LocalizedModule 𝔭.asIdeal.primeCompl M) :=
  _root_.Module.free_localizedModule_of_isReduced_of_finrank_fiber_const hconst 𝔭

theorem projective_of_isReduced_of_finrank_const [IsReduced R] [Module.FinitePresentation R M]
    {e : ℕ} (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e) :
    Module.Projective R M :=
  _root_.Module.projective_of_isReduced_of_finrank_fiber_const hconst

end FittingFree

end CBCSol

namespace CoherentBaseChange
open _root_.CoherentBaseChange
namespace TwoTermComplex
open _root_.CoherentBaseChange.TwoTermComplex
open _root_.CoherentBaseChange.TwoTermComplex
open _root_.CoherentBaseChange

open CBCSol

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

private def _root_.CoherentBaseChange.TwoTermComplex.fibreRank (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭)))

open _root_.CoherentBaseChange.TwoTermComplex
private theorem _root_.CoherentBaseChange.TwoTermComplex.fibreH0_add_fibreRank (𝔭 : PrimeSpectrum
    R) :
    G.fibreH0 𝔭 + G.fibreRank 𝔭 = Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange (κ 𝔭))
  change Module.finrank (κ 𝔭) (LinearMap.ker (G.d.baseChange (κ 𝔭)))
      + Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭))) = _
  omega

open _root_.CoherentBaseChange.TwoTermComplex
private theorem _root_.CoherentBaseChange.TwoTermComplex.fibreRank_add_fibreH1 (𝔭 : PrimeSpectrum
    R) :
    G.fibreRank 𝔭 + G.fibreH1 𝔭 = Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] G.C1) := by
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (G.d.baseChange (κ 𝔭)))
  change Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭)))
      + Module.finrank (κ 𝔭)
          ((κ 𝔭 ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange (κ 𝔭))) = _
  omega

open _root_.CoherentBaseChange.TwoTermComplex

private theorem _root_.CoherentBaseChange.TwoTermComplex.fibre_euler [StrongRankCondition R] (𝔭 :
    PrimeSpectrum R) :
    (G.fibreH0 𝔭 : ℤ) - (G.fibreH1 𝔭 : ℤ)
      = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ) := by
  have h0 := G.fibreH0_add_fibreRank 𝔭
  have h1 := G.fibreRank_add_fibreH1 𝔭
  rw [Module.finrank_baseChange] at h0 h1
  have h0' : (G.fibreH0 𝔭 : ℤ) + (G.fibreRank 𝔭 : ℤ) = (Module.finrank R G.C0 : ℤ) := by
    exact_mod_cast h0
  have h1' : (G.fibreRank 𝔭 : ℤ) + (G.fibreH1 𝔭 : ℤ) = (Module.finrank R G.C1 : ℤ) := by
    exact_mod_cast h1
  omega

open _root_.CoherentBaseChange.TwoTermComplex

/-- The cokernel module of the original two-term differential. -/
abbrev _root_.CoherentBaseChange.TwoTermComplex.coker : Type v := G.C1 ⧸ LinearMap.range G.d

open _root_.CoherentBaseChange.TwoTermComplex
scoped instance coker_finitePresentation : Module.FinitePresentation R G.coker :=
  have : Module.FinitePresentation R G.C1 := Module.finitePresentation_of_projective R G.C1
  Module.finitePresentation_of_surjective (LinearMap.range G.d).mkQ
    (Submodule.Quotient.mk_surjective _) (by
      rw [Submodule.ker_mkQ]; exact Submodule.fg_range G.d)

private def _root_.CoherentBaseChange.TwoTermComplex.cokerBaseChangeEquiv (𝔭 : PrimeSpectrum R) :
    ((κ 𝔭 ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange (κ 𝔭))) ≃ₗ[κ 𝔭] κ 𝔭 ⊗[R] G.coker := by
  have hexact : Function.Exact (G.d.baseChange (κ 𝔭))
      ((LinearMap.range G.d).mkQ.baseChange (κ 𝔭)) := by
    have := lTensor_exact (κ 𝔭) (LinearMap.exact_map_mkQ_range G.d)
      (Submodule.Quotient.mk_surjective _)
    simpa only [LinearMap.baseChange_eq_lTensor] using this
  have hsurj : Function.Surjective ((LinearMap.range G.d).mkQ.baseChange (κ 𝔭)) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective _ (Submodule.Quotient.mk_surjective _)
  exact hexact.linearEquivOfSurjective hsurj

open _root_.CoherentBaseChange.TwoTermComplex
private theorem _root_.CoherentBaseChange.TwoTermComplex.finrank_residue_tensor_coker (𝔭 :
    PrimeSpectrum R) :
    Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] G.coker) = G.fibreH1 𝔭 :=
  ((G.cokerBaseChangeEquiv 𝔭).finrank_eq).symm

open _root_.CoherentBaseChange.TwoTermComplex

private theorem _root_.CoherentBaseChange.TwoTermComplex.fibreH1_eq_of_fibreH0_const {c : ℕ} (h0 :
    ∀ 𝔭, G.fibreH0 𝔭 = c)
    (𝔭 𝔮 : PrimeSpectrum R) : G.fibreH1 𝔭 = G.fibreH1 𝔮 := by
  have : Nontrivial R :=
    ⟨0, 1, fun h01 => 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (h01 ▸ 𝔭.asIdeal.zero_mem))⟩
  have : StrongRankCondition R := commRing_strongRankCondition R
  have h𝔭 := G.fibre_euler 𝔭
  have h𝔮 := G.fibre_euler 𝔮
  rw [h0 𝔭] at h𝔭
  rw [h0 𝔮] at h𝔮
  omega

open _root_.CoherentBaseChange.TwoTermComplex

private theorem
    _root_.CoherentBaseChange.TwoTermComplex.projective_coker_of_isReduced_of_fibreH0_const
    [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) : Module.Projective R G.coker := by
  refine Module.projective_of_localization_maximal (fun I hI => ?_)
  let 𝔪 : PrimeSpectrum R := ⟨I, hI.isPrime⟩
  have := Module.free_localizedModule_of_isReduced_of_finrank_fiber_const
    (M := G.coker) (e := G.fibreH1 𝔪)
    (fun 𝔮 => by rw [G.finrank_residue_tensor_coker, G.fibreH1_eq_of_fibreH0_const h0 𝔮 𝔪]) 𝔪
  exact Module.Projective.of_free

open _root_.CoherentBaseChange.TwoTermComplex

private theorem _root_.CoherentBaseChange.TwoTermComplex.exists_retraction_range
    [Module.Projective R G.coker] :
    ∃ r : G.C1 →ₗ[R] LinearMap.range G.d,
      r ∘ₗ (LinearMap.range G.d).subtype = LinearMap.id := by
  obtain ⟨s, hs⟩ := (LinearMap.range G.d).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.Quotient.mk_surjective _))
  have hsec : ∀ q, (LinearMap.range G.d).mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  have hmem : ∀ x : G.C1, x - s ((LinearMap.range G.d).mkQ x) ∈ LinearMap.range G.d := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hsec, sub_self]
  let r : G.C1 →ₗ[R] LinearMap.range G.d :=
    (LinearMap.id - s ∘ₗ (LinearMap.range G.d).mkQ).codRestrict (LinearMap.range G.d) hmem
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  have hx0 : (LinearMap.range G.d).mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
  change x - s ((LinearMap.range G.d).mkQ x) = x
  rw [hx0, map_zero, sub_zero]

open _root_.CoherentBaseChange.TwoTermComplex

private theorem
    _root_.CoherentBaseChange.TwoTermComplex.projective_range_of_isReduced_of_fibreH0_const
    [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) : Module.Projective R (LinearMap.range G.d) := by
  have := G.projective_coker_of_isReduced_of_fibreH0_const h0
  obtain ⟨r, hr⟩ := G.exists_retraction_range
  exact Module.Projective.of_split (LinearMap.range G.d).subtype r hr

open _root_.CoherentBaseChange.TwoTermComplex

private theorem _root_.CoherentBaseChange.TwoTermComplex.projective_ker_of_isReduced_impl
    [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) : Module.Projective R (LinearMap.ker G.d) := by
  have := G.projective_range_of_isReduced_of_fibreH0_const h0
  rw [← LinearMap.ker_rangeRestrict]
  exact projective_ker_of_surjective_of_projective G.d.rangeRestrict
    (LinearMap.surjective_rangeRestrict G.d)

open _root_.CoherentBaseChange.TwoTermComplex

theorem kerBaseChangeHom_eq (A : Type w) [CommRing A] [Algebra R A] :
    G.kerBaseChangeHom A = kerBaseChangeHomOf A G.d := rfl

private theorem
    _root_.CoherentBaseChange.TwoTermComplex.kerBaseChangeHom_bijective_of_isReduced_impl
    [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) (A : Type w) [CommRing A] [Algebra R A] :
    Function.Bijective (G.kerBaseChangeHom A) := by
  have := G.projective_coker_of_isReduced_of_fibreH0_const h0
  have := G.projective_range_of_isReduced_of_fibreH0_const h0
  set d' := G.d.rangeRestrict with hd'
  set ι := (LinearMap.range G.d).subtype with hι
  have hfac : G.d = ι ∘ₗ d' := (LinearMap.subtype_comp_codRestrict _ _ _).symm
  obtain ⟨r, hr⟩ := G.exists_retraction_range
  have hιinj : Function.Injective (ι.baseChange A) := by
    have hri : (r.baseChange A) ∘ₗ (ι.baseChange A) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (congrFun (congrArg DFunLike.coe hri))
  have hbc : G.d.baseChange A = (ι.baseChange A) ∘ₗ (d'.baseChange A) := by
    rw [← LinearMap.baseChange_comp]; exact congrArg (LinearMap.baseChange A) hfac
  have hker : ∀ x, x ∈ LinearMap.ker (G.d.baseChange A) ↔ x ∈ LinearMap.ker (d'.baseChange A) := by
    intro x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hbc, LinearMap.comp_apply]
    exact ⟨fun h => hιinj (by rw [map_zero]; exact h), fun h => by rw [h, map_zero]⟩
  have hbij := kerBaseChangeHomOf_bijective A d' (LinearMap.surjective_rangeRestrict G.d)
  have hkd : LinearMap.ker d' = LinearMap.ker G.d := LinearMap.ker_rangeRestrict G.d
  rw [kerBaseChangeHom_eq]
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨s, hs⟩ := d'.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (LinearMap.surjective_rangeRestrict G.d))
    let ρ : G.C0 →ₗ[R] LinearMap.ker G.d :=
      (LinearEquiv.ofEq _ _ hkd).toLinearMap ∘ₗ kerRetraction d' hs
    have hρ : ρ ∘ₗ (LinearMap.ker G.d).subtype = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨w, hw⟩
      have hw' : d' w = 0 := by rw [← LinearMap.mem_ker, hkd]; exact hw
      apply Subtype.ext
      change (LinearEquiv.ofEq _ _ hkd (kerRetraction d' hs w) : G.C0) = w
      rw [LinearEquiv.coe_ofEq_apply, kerRetraction_apply_coe, hw', map_zero, sub_zero]
    have hri : (ρ.baseChange A) ∘ₗ ((LinearMap.ker G.d).subtype.baseChange A) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hρ, LinearMap.baseChange_id]
    have hsub_inj : Function.Injective ((LinearMap.ker G.d).subtype.baseChange A) :=
      Function.LeftInverse.injective (congrFun (congrArg DFunLike.coe hri))
    apply hsub_inj
    have hxy' := congrArg (fun t : LinearMap.ker (G.d.baseChange A) => (t : A ⊗[R] G.C0)) hxy
    exact hxy'
  · obtain ⟨z, hz⟩ := z
    have hz' : z ∈ LinearMap.ker (d'.baseChange A) := (hker z).mp hz
    obtain ⟨w, hw⟩ := hbij.2 ⟨z, hz'⟩
    refine ⟨((LinearEquiv.ofEq _ _ hkd).toLinearMap).baseChange A w, ?_⟩
    apply Subtype.ext
    have hw0 := congrArg (fun t : LinearMap.ker (d'.baseChange A) => (t : A ⊗[R] G.C0)) hw
    change (LinearMap.ker G.d).subtype.baseChange A
      (((LinearEquiv.ofEq _ _ hkd).toLinearMap).baseChange A w) = z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have hcomp : (LinearMap.ker G.d).subtype ∘ₗ (LinearEquiv.ofEq _ _ hkd).toLinearMap
        = (LinearMap.ker d').subtype := by
      apply LinearMap.ext
      intro x
      exact LinearEquiv.coe_ofEq_apply hkd x
    rw [hcomp]
    exact hw0

open _root_.CoherentBaseChange.TwoTermComplex

private theorem _root_.CoherentBaseChange.TwoTermComplex.finrank_residue_ker_of_isReduced_impl
    [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) (𝔭 : PrimeSpectrum R) :
    Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] LinearMap.ker G.d) = c := by
  have hb := G.kerBaseChangeHom_bijective_of_isReduced_impl h0 (κ 𝔭)
  rw [(LinearEquiv.ofBijective (G.kerBaseChangeHom (κ 𝔭)) hb).finrank_eq]
  exact h0 𝔭

open _root_.CoherentBaseChange.TwoTermComplex
end CoherentBaseChange.TwoTermComplex

theorem _root_.CoherentBaseChange.TwoTermComplex.projective_ker_of_isReduced_of_fibreH0_const
    {R : Type u} [CommRing R] [IsReduced R] (G : TwoTermComplex.{u, v} R) {c : ℕ}
    (h0 : ∀ 𝔭 : PrimeSpectrum R, G.fibreH0 𝔭 = c) :
    Module.Projective R (LinearMap.ker G.d) ∧
      (∀ (A : Type w) [CommRing A] [Algebra R A], Function.Bijective (G.kerBaseChangeHom A)) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
        (𝔭.asIdeal.ResidueField ⊗[R] LinearMap.ker G.d) = c :=
  ⟨G.projective_ker_of_isReduced_impl h0,
    fun A _ _ => G.kerBaseChangeHom_bijective_of_isReduced_impl h0 A,
    fun 𝔭 => G.finrank_residue_ker_of_isReduced_impl h0 𝔭⟩
end
end CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
