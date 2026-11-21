/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.TwoChartCechGrothendieckComplex
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Nyll.SchemeTheory.Cohomology.Sheaves.CoherentBaseChange

/-!
Finite free two-term models for Cech kernels and their base changes.
A lifted presentation of the cokernel yields a model inducing bijections on all kernels.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective

noncomputable section

open scoped TensorProduct

universe u

open _root_.AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open _root_.TwoChartCech.Mumford
open TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing.TwoChartCech.Truncation

namespace TwoChartCech
open _root_.TwoChartCech

namespace Truncation

variable {R : Type u} [CommRing R]

variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

section Free

variable [IsNoetherianRing R] [Module.Flat R C0] [Module.Flat R C1] [Module.Finite R
  (LinearMap.ker d)]

theorem projective_K0 : Module.Projective R (K0 d) := by
  have := finite_K0 d; have := flat_K0 d
  have : Module.FinitePresentation R (K0 d) := Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

/-- The chosen number of free generators of the enlarged kernel. -/
def n : ℕ := by haveI := finite_K0 d; exact (Module.Finite.exists_fin' R (K0 d)).choose

/-- The chosen finite free surjection onto the enlarged kernel. -/
def pi : (Fin (n d) → R) →ₗ[R] K0 d := by
  haveI := finite_K0 d; exact (Module.Finite.exists_fin' R (K0 d)).choose_spec.choose
omit [Module.Flat R C0] [Module.Flat R C1] in
theorem pi_surjective : Function.Surjective (pi d) := by
  have := finite_K0 d; exact (Module.Finite.exists_fin' R (K0 d)).choose_spec.choose_spec

/-- The chosen section of the finite free surjection onto the enlarged kernel. -/
def sec : K0 d →ₗ[R] (Fin (n d) → R) :=
  haveI := projective_K0 d
  (Module.projective_lifting_property (pi d) (LinearMap.id) (pi_surjective d)).choose
theorem pi_comp_sec : pi d ∘ₗ sec d = LinearMap.id :=
  haveI := projective_K0 d
  (Module.projective_lifting_property (pi d) (LinearMap.id) (pi_surjective d)).choose_spec
theorem pi_sec (k : K0 d) : pi d (sec d k) = k := by
  rw [← LinearMap.comp_apply, pi_comp_sec, LinearMap.id_apply]

/-- The differential recording the presentation projection and its splitting complement. -/
def dG : (Fin (n d) → R) →ₗ[R] (Fin (rank d) → R) × (Fin (n d) → R) :=
  (dK d ∘ₗ pi d).prod (LinearMap.id - sec d ∘ₗ pi d)

theorem fst_comp_dG : LinearMap.fst R _ _ ∘ₗ dG d = dK d ∘ₗ pi d := LinearMap.fst_prod _ _
theorem snd_comp_dG : LinearMap.snd R _ _ ∘ₗ dG d = LinearMap.id - sec d ∘ₗ pi d :=
    LinearMap.snd_prod _ _

/-- The finite free two-term complex constructed from the split presentation. -/
def freeModel : CoherentBaseChange.TwoTermComplex.{u, u} R :=
  { C0 := Fin (n d) → R, C1 := (Fin (rank d) → R) × (Fin (n d) → R), d := dG d }

theorem comm_free : d ∘ₗ (ι0 d ∘ₗ pi d) = ((-(lift d)) ∘ₗ LinearMap.fst R _ _) ∘ₗ dG d := by
  have hd := (Mumford.comm d).trans (by rw [Mumford.ι1_eq])
  rw [← LinearMap.comp_assoc, hd, LinearMap.comp_assoc, LinearMap.comp_assoc, fst_comp_dG]

variable (A : Type u) [CommRing A] [Algebra R A]

theorem mem_ker_dG_baseChange_iff (z : A ⊗[R] (Fin (n d) → R)) :
    (dG d).baseChange A z = 0 ↔
      ((dK d).baseChange A) (((pi d).baseChange A) z) = 0 ∧ z = ((sec d).baseChange A) (((pi
        d).baseChange A) z) := by
  have hinj := (TensorProduct.prodRight R A A (Fin (rank d) → R) (Fin (n d) → R)).injective
  constructor
  · intro h
    have h1 := congrArg (fun w => ((LinearMap.fst R _ _).baseChange A) w) h
    have h2 := congrArg (fun w => ((LinearMap.snd R _ _).baseChange A) w) h
    simp only [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, fst_comp_dG,
      snd_comp_dG] at h1 h2
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply] at h1
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, LinearMap.baseChange_id, LinearMap.id_apply,
      LinearMap.baseChange_comp, LinearMap.comp_apply, sub_eq_zero] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply hinj
    rw [map_zero, prodRight_apply_eq_baseChange, ← LinearMap.comp_apply, ←
      LinearMap.baseChange_comp, fst_comp_dG,
      ← LinearMap.comp_apply ((LinearMap.snd R _ _).baseChange A), ← LinearMap.baseChange_comp,
        snd_comp_dG,
      LinearMap.baseChange_comp, LinearMap.comp_apply, h1, LinearMap.baseChange_sub,
        LinearMap.sub_apply,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.baseChange_comp,
        LinearMap.comp_apply, ← h2, sub_self]
    rfl

theorem bijective_kerMap_free_to_K :
    Function.Bijective (kerMapBaseChange (dG d) (dK d) (pi d) (LinearMap.fst R _ _) (fst_comp_dG
      d).symm A) := by
  constructor
  · rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have h' : ((pi d).baseChange A) z = ((pi d).baseChange A) z' := congrArg Subtype.val h
    obtain ⟨-, hz2⟩ := (mem_ker_dG_baseChange_iff d A z).mp hz
    obtain ⟨-, hz2'⟩ := (mem_ker_dG_baseChange_iff d A z').mp hz'
    apply Subtype.ext
    change z = z'
    rw [hz2, hz2', h']
  · rintro ⟨w, hw⟩
    refine ⟨⟨((sec d).baseChange A) w, (mem_ker_dG_baseChange_iff d A _).mpr ⟨?_, ?_⟩⟩,
      Subtype.ext ?_⟩
    · have h5 : ((pi d).baseChange A) (((sec d).baseChange A) w) = w := by
        rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, pi_comp_sec,
          LinearMap.baseChange_id, LinearMap.id_apply]
      rw [h5]
      exact hw
    · rw [← LinearMap.comp_apply ((pi d).baseChange A), ← LinearMap.baseChange_comp, pi_comp_sec,
      LinearMap.baseChange_id,
        LinearMap.id_apply]
    · change ((pi d).baseChange A) (((sec d).baseChange A) w) = w
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, pi_comp_sec,
        LinearMap.baseChange_id, LinearMap.id_apply]

theorem kerMap_free_eq_comp (z : LinearMap.ker ((dG d).baseChange A)) :
    kerMapBaseChange (dG d) d (ι0 d ∘ₗ pi d) ((-(lift d)) ∘ₗ LinearMap.fst R _ _) (comm_free d)
      A z
      = kerMapBaseChange (dK d) d (ι0 d) (-(lift d)) (Mumford.comm d) A
          (kerMapBaseChange (dG d) (dK d) (pi d) (LinearMap.fst R _ _) (fst_comp_dG d).symm A z)
            := by
  apply Subtype.ext
  change ((ι0 d ∘ₗ pi d).baseChange A) z.1 =
    ((ι0 d).baseChange A) (((pi d).baseChange A) z.1)
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]

theorem bijective_kerMap_free :
    Function.Bijective
      (kerMapBaseChange (dG d) d (ι0 d ∘ₗ pi d) ((-(lift d)) ∘ₗ LinearMap.fst R _ _) (comm_free
        d) A) := by
  have h : (kerMapBaseChange (dG d) d (ι0 d ∘ₗ pi d) ((-(lift d)) ∘ₗ LinearMap.fst R _ _)
    (comm_free d) A : _ → _)
      = (kerMapBaseChange (dK d) d (ι0 d) (-(lift d)) (Mumford.comm d) A)
        ∘ (kerMapBaseChange (dG d) (dK d) (pi d) (LinearMap.fst R _ _) (fst_comp_dG d).symm A) :=
    funext (kerMap_free_eq_comp d A)
  rw [h]
  exact Function.Bijective.comp ⟨kerMap_injective d A, kerMap_surjective d A⟩
    (bijective_kerMap_free_to_K d A)

end Free

end Truncation

end TwoChartCech

theorem _root_.TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C0) (ι1 : G.C1 →ₗ[R] C1)
      (comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm A) :=
  ⟨TwoChartCech.Truncation.freeModel d, ι0 d ∘ₗ
    TwoChartCech.Truncation.pi d,
    (-(lift d)) ∘ₗ LinearMap.fst R _ _, TwoChartCech.Truncation.comm_free d,
    fun A _ _ => TwoChartCech.Truncation.bijective_kerMap_free d A⟩

end
end TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
