/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.MumfordTruncation
public import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Module.Projective
public import Nyll.SchemeTheory.Cohomology.Sheaves.CoherentBaseChange

/-!
Construct a two-chart Cech Grothendieck complex over a local ring.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing

noncomputable section

open scoped TensorProduct

universe u

namespace TwoChartCech
open _root_.TwoChartCech
open _root_.TwoChartCech.Mumford

namespace Truncation

variable {R : Type u} [CommRing R]

variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

theorem free_K0 [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R C0] [Module.Flat R C1]
    [Module.Finite R (LinearMap.ker d)] : Module.Free R (K0 d) :=
  haveI := finite_K0 d; haveI := flat_K0 d
  Module.free_of_flat_of_isLocalRing

/-- The finite free two-term complex constructed from the kernel of the combined surjection. -/
def model [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R C0] [Module.Flat R C1]
    [Module.Finite R (LinearMap.ker d)] : CoherentBaseChange.TwoTermComplex.{u, u} R :=
  haveI := finite_K0 d; haveI := free_K0 d
  { C0 := K0 d, C1 := Fin (rank d) → R, d := dK d }

section BaseChange

variable (A : Type u) [CommRing A] [Algebra R A]

theorem d_baseChange_comp_iota0_baseChange :
    (d.baseChange A) ∘ₗ ((ι0 d).baseChange A)
      = -(((lift d).baseChange A) ∘ₗ ((dK d).baseChange A)) := by
  rw [← LinearMap.baseChange_comp, Mumford.comm, Mumford.ι1_eq, LinearMap.baseChange_comp,
    LinearMap.baseChange_neg, LinearMap.neg_comp]

variable [Module.Flat R C1]

theorem subtype_baseChange_injective :
    Function.Injective ((K0 d).subtype.baseChange A) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact LinearMap.lTensor_injective_of_exact_of_flat (d.coprod (lift d))
    (surjective_coprod d) _ (K0 d).subtype_injective (LinearMap.exact_subtype_ker_map _) A
omit [Module.Flat R C1] in
theorem mem_range_subtype_baseChange (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w = 0 ↔ ∃ z, ((K0 d).subtype.baseChange A) z = w := by
  have heqι : ⇑((K0 d).subtype.baseChange A) = ⇑((K0 d).subtype.lTensor A) :=
    LinearMap.baseChange_eq_lTensor _
  have heqc : ⇑((d.coprod (lift d)).baseChange A) = ⇑((d.coprod (lift d)).lTensor A) :=
    LinearMap.baseChange_eq_lTensor _
  rw [heqc]
  simp only [heqι]
  exact lTensor_exact A (LinearMap.exact_subtype_ker_map _) (surjective_coprod d) w
omit [Module.Flat R C1] in
theorem prodRight_apply_eq_baseChange {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (w : A ⊗[R] (M × N)) :
    (TensorProduct.prodRight R A A M N) w
      = (((LinearMap.fst R M N).baseChange A) w, ((LinearMap.snd R M N).baseChange A) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a x => simp [TensorProduct.prodRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]
omit [Module.Flat R C1] in
theorem prodRight_subtype_baseChange (z : A ⊗[R] K0 d) :
    (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) (((K0 d).subtype.baseChange A) z)
      = (((ι0 d).baseChange A) z, ((dK d).baseChange A) z) := by
  rw [prodRight_apply_eq_baseChange]
  refine Prod.ext ?_ ?_
  · change ((LinearMap.fst R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A)
    z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl
  · change ((LinearMap.snd R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A)
    z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl
omit [Module.Flat R C1] in
theorem coprod_baseChange_apply (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w
      = (d.baseChange A) ((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).1
        + ((lift d).baseChange A) ((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).2 := by
  induction w using TensorProduct.inductionOn with
  | tmul a x => simp [TensorProduct.prodRight_tmul, LinearMap.coprod_apply, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add]; abel

theorem kerMap_injective :
    Function.Injective (kerMapBaseChange (dK d) d (ι0 d) (-(lift d)) (Mumford.comm d) A) := by
  rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz'
  apply Subtype.ext
  apply subtype_baseChange_injective d A
  apply (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)).injective
  rw [prodRight_subtype_baseChange d A z, prodRight_subtype_baseChange d A z']
  have h1 : ((dK d).baseChange A) z = 0 := hz
  have h2 : ((dK d).baseChange A) z' = 0 := hz'
  rw [h1, h2]
  exact congrArg (·, (0 : A ⊗[R] (Fin (rank d) → R))) (congrArg Subtype.val hzz')

omit [Module.Flat R C1] in
theorem kerMap_surjective :
    Function.Surjective (kerMapBaseChange (dK d) d (ι0 d) (-(lift d)) (Mumford.comm d) A) := by
  rintro ⟨w, hw⟩
  set w' : A ⊗[R] (C0 × (Fin (rank d) → R)) :=
    ((LinearMap.inl R C0 (Fin (rank d) → R)).baseChange A) w with hw'def
  have hker : ((d.coprod (lift d)).baseChange A) w' = 0 := by
    rw [hw'def, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.coprod_inl]
    exact hw
  obtain ⟨z, hz⟩ := (mem_range_subtype_baseChange d A w').mp hker
  have hpr : (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w' = (w, 0) := by
    rw [prodRight_apply_eq_baseChange, hw'def, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      LinearMap.fst_comp_inl R C0 (Fin (rank d) → R),
      LinearMap.snd_comp_inl R C0 (Fin (rank d) → R),
      LinearMap.baseChange_id, LinearMap.baseChange_zero, LinearMap.id_apply,
      LinearMap.zero_apply]
  have hpair : (((ι0 d).baseChange A) z, ((dK d).baseChange A) z) = (w, 0) := by
    rw [← prodRight_subtype_baseChange d A z, hz, hpr]
  refine ⟨⟨z, (Prod.ext_iff.mp hpair).2⟩, ?_⟩
  exact Subtype.ext (Prod.ext_iff.mp hpair).1

theorem cokerMap_surjective [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R C0]
    [Module.Finite R (LinearMap.ker d)] :
    Function.Surjective
      (cokerMapBaseChange (model d).d d (ι0 d) (-(lift d)) (Mumford.comm d) A) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
    have hsurj : Function.Surjective ((d.coprod (lift d)).baseChange A) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact LinearMap.lTensor_surjective A (surjective_coprod d)
    obtain ⟨w, rfl⟩ := hsurj y
    refine ⟨Submodule.Quotient.mk (-((TensorProduct.prodRight R A A C0 (Fin (rank d) → R))
      w).2), ?_⟩
    change Submodule.Quotient.mk (((-(lift d)).baseChange A) _) = _
    rw [LinearMap.baseChange_neg, LinearMap.neg_apply, map_neg, neg_neg, coprod_baseChange_apply,
      Submodule.Quotient.eq]
    refine ⟨-((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).1, ?_⟩
    rw [map_neg]; abel

theorem cokerMap_injective [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R C0]
    [Module.Finite R (LinearMap.ker d)] :
    Function.Injective
      (cokerMapBaseChange (model d).d d (ι0 d) (-(lift d)) (Mumford.comm d) A) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    have hq' : ((-(lift d)).baseChange A) v ∈ LinearMap.range (d.baseChange A) := by
      rw [← Submodule.Quotient.mk_eq_zero]; exact hq
    obtain ⟨x, hx⟩ := hq'
    have hneg := congrArg
      (fun f : A ⊗[R] (Fin (rank d) → R) →ₗ[A] A ⊗[R] C1 =>
        f (show A ⊗[R] (Fin (rank d) → R) from v))
      (LinearMap.baseChange_neg (A := A) (lift d))
    have hx' : (d.baseChange A) x =
        -((lift d).baseChange A (show A ⊗[R] (Fin (rank d) → R) from v)) :=
      hx.trans (hneg.trans (LinearMap.neg_apply ((lift d).baseChange A) _))
    set w := (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)).symm (x, v) with hwdef
    have hw : ((d.coprod (lift d)).baseChange A) w = 0 := by
      rw [coprod_baseChange_apply, hwdef, LinearEquiv.apply_symm_apply, hx', neg_add_cancel]
    obtain ⟨z, hz⟩ := (mem_range_subtype_baseChange d A w).mp hw
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨z, ?_⟩
    change ((dK d).baseChange A) z = v
    have := congrArg Prod.snd (prodRight_subtype_baseChange d A z)
    rw [hz, hwdef, LinearEquiv.apply_symm_apply] at this
    exact this.symm

end BaseChange

/-- The finite free model whose comparison maps preserve kernel and cokernel under the given
flat base changes. -/
def grothendieckComplex [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R C0] [Module.Flat R C1]
    [Module.Finite R (LinearMap.ker d)] : GrothendieckComplex d where
  G := model d
  ι0 := ι0 d
  ι1 := -(lift d)
  comm := Mumford.comm d
  bijective_kerMap A _ _ := ⟨kerMap_injective d A, kerMap_surjective d A⟩
  bijective_cokerMap A _ _ := ⟨cokerMap_injective d A, cokerMap_surjective d A⟩

end Truncation

theorem nonempty_of_isLocalRing' {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Nonempty (_root_.TwoChartCech.GrothendieckComplex d) :=
  ⟨Truncation.grothendieckComplex d⟩

end TwoChartCech

theorem _root_.TwoChartCech.GrothendieckComplex.nonempty_of_isLocalRing {R : Type u} [CommRing
    R] [IsNoetherianRing R]
    [IsLocalRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Nonempty (_root_.TwoChartCech.GrothendieckComplex d) :=
  TwoChartCech.nonempty_of_isLocalRing' d

end
end TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
