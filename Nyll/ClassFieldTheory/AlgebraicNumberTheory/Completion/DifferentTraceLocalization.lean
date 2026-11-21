/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegralDiagonalDensity
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.TraceDualFamily
public import Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition
public import Mathlib.RingTheory.DedekindDomain.Different
import Nyll.ValuedFieldTheory.Valuation.Completion.BaseChangeNormTrace
import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The number-field trace dual in finite completions -/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain ValuationTheory.Completion

noncomputable section
namespace AlgebraicNumberTheory.Valuations

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- A global codifferent element pairs integrally with each integral element
of the actual completion at any finite place. Simultaneous approximation
permits the local test element to be inserted at one place only. -/
theorem finitePlace_trace_mul_mem_integers_of_mem_globalTraceDual
    (v : HeightOneSpectrum (𝓞 K)) (d : L)
    (hd : d ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK := HeightOneSpectrum.isNonarchimedean_adicAbv K v
    let : Algebra vK.Completion w.1.Completion := AbsoluteValue.completionAlgebra vK w.1 w.2
    ∀ z : absoluteValueCompletionIntegers w.1 (absoluteValueExtension_isNonarchimedean vK hvK w),
      Algebra.trace vK.Completion w.1.Completion (AbsoluteValue.toCompletion w.1 d * z) ∈
        absoluteValueCompletionIntegers vK hvK := by
  intro vK hvK algebraOwner z
  classical
  let hvK0 : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let W := AbsoluteValueExtension vK L
  let : Fintype W := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK0
  let : ∀ u : W, Algebra vK.Completion u.1.Completion :=
    fun u => AbsoluteValue.completionAlgebra vK u.1 u.2
  let : ∀ u : W, Module.Finite vK.Completion u.1.Completion :=
    fun u => completionModuleFinite vK hvK0 u
  let : ∀ u : W, Module.Free vK.Completion u.1.Completion :=
    fun u => Module.Free.of_divisionRing vK.Completion u.1.Completion
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField vK hvK0
  let : ∀ u : W, NormedAlgebra vK.Completion u.1.Completion :=
    fun u => absoluteValueExtension_completionNormedAlgebra vK u
  let V (u : W) := absoluteValueCompletionIntegers u.1
    (absoluteValueExtension_isNonarchimedean vK hvK u)
  let T (a : ∀ u : W, V u) := ∑ u : W, Algebra.trace vK.Completion u.1.Completion
    (AbsoluteValue.toCompletion u.1 d * (a u : u.1.Completion))
  have hT : Continuous T := by
    apply continuous_finsetSum Finset.univ
    intro u hu
    exact (Algebra.trace vK.Completion u.1.Completion).continuous_of_finiteDimensional.comp
      (continuous_const.mul (continuous_subtype_val.comp (continuous_apply u)))
  have hclosed : IsClosed {a : ∀ u : W, V u | T a ∈ absoluteValueCompletionIntegers vK hvK} := by
    change IsClosed {a : ∀ u : W, V u | ‖T a‖ ≤ 1}
    exact isClosed_le (continuous_norm.comp hT) continuous_const
  have hdiag (a : 𝓞 L) :
      T (finitePlaceIntegralDiagonal v a) ∈ absoluteValueCompletionIntegers vK hvK := by
    let e := completionTensorDecomposition_left (K := K) (L := L) vK hvK0
    have he (u : W) : e (1 ⊗ₜ[K] (d * (a : L))) u =
        AbsoluteValue.toCompletion u.1 d *
          (finitePlaceIntegralDiagonal v a u : u.1.Completion) := by
      change completionTensorDecomposition_left vK hvK0 (1 ⊗ₜ[K] (d * (a : L))) u = _
      rw [completionTensorDecomposition_left_tmul_apply, map_one, one_mul, map_mul]
      rfl
    have hr : T (finitePlaceIntegralDiagonal v a) =
        algebraMap K vK.Completion (Algebra.trace K L (d * (a : L))) := by
      dsimp only [T]
      simp_rw [← he]
      rw [← algebra_trace_pi_apply (fun u : W => u.1.Completion),
        Algebra.trace_eq_of_algEquiv e, algebra_trace_baseChange_tmul]
    obtain ⟨b, hb⟩ := (Submodule.mem_traceDual.mp hd) (a : L)
      (Submodule.mem_one.mpr ⟨a, rfl⟩)
    rw [Algebra.traceForm_apply] at hb
    rw [hr, ← hb]
    let u : AbsoluteValueExtension vK K := ⟨vK, fun x => by rw [Algebra.algebraMap_self_apply]⟩
    exact (finitePlaceIntegralDiagonal v b u).2
  have h : T (Pi.single w z) ∈ absoluteValueCompletionIntegers vK hvK :=
    DenseRange.induction_on (denseRange_finitePlaceIntegralDiagonal (L := L) v)
      (Pi.single w z) hclosed hdiag
  have hsingle : T (Pi.single w z) =
      Algebra.trace vK.Completion w.1.Completion (AbsoluteValue.toCompletion w.1 d * z) := by
    dsimp only [T]
    rw [Finset.sum_eq_single w, Pi.single_eq_same]
    · intro u _ hu
      rw [Pi.single_eq_of_ne hu]
      change Algebra.trace vK.Completion u.1.Completion (AbsoluteValue.toCompletion u.1 d * 0) = 0
      rw [mul_zero, map_zero]
    · exact fun hw => (hw (Finset.mem_univ w)).elim
  rwa [hsingle] at h

omit [NumberField L] in
/-- A finite trace-dual expansion over the number field holds on each
factor of its completed scalar extension. -/
theorem finitePlace_traceDualExpansion
    {ι : Type*} [Fintype ι] (b y : ι → L)
    (h : ∀ x : L, ∑ i, Algebra.trace K L (x * b i) • y i = x)
    (v : HeightOneSpectrum (𝓞 K)) (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L)
    (z : w.1.Completion) :
    let vK := HeightOneSpectrum.adicAbv K v
    let : Algebra vK.Completion w.1.Completion := AbsoluteValue.completionAlgebra vK w.1 w.2
    ∑ i, Algebra.trace vK.Completion w.1.Completion (z * AbsoluteValue.toCompletion w.1 (b i)) •
      AbsoluteValue.toCompletion w.1 (y i) = z := by
  intro vK algebraOwner
  classical
  let hvK0 : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let W := AbsoluteValueExtension vK L
  let : Fintype W := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK0
  let : ∀ u : W, Algebra vK.Completion u.1.Completion :=
    fun u => AbsoluteValue.completionAlgebra vK u.1 u.2
  let : ∀ u : W, Module.Finite vK.Completion u.1.Completion :=
    fun u => completionModuleFinite vK hvK0 u
  let : ∀ u : W, Module.Free vK.Completion u.1.Completion :=
    fun u => Module.Free.of_divisionRing vK.Completion u.1.Completion
  let F := vK.Completion
  let e := completionTensorDecomposition_left (K := K) (L := L) vK hvK0
  have he (x : L) (u : W) : e (1 ⊗ₜ[K] x) u = AbsoluteValue.toCompletion u.1 x := by
    rw [completionTensorDecomposition_left_tmul_apply, map_one, one_mul]
    rfl
  have hsingle (x : L) :
      Algebra.trace F (F ⊗[K] L) (e.symm (Pi.single w z) * (1 ⊗ₜ[K] x)) =
        Algebra.trace F w.1.Completion (z * AbsoluteValue.toCompletion w.1 x) := by
    rw [← Algebra.trace_eq_of_algEquiv e, map_mul, AlgEquiv.apply_symm_apply,
      algebra_trace_pi_apply (fun u : W => u.1.Completion)]
    simp only [Pi.mul_apply, he]
    rw [Finset.sum_eq_single w, Pi.single_eq_same]
    · intro u _ hu
      rw [Pi.single_eq_of_ne hu, zero_mul, map_zero]
    · exact fun hw => (hw (Finset.mem_univ w)).elim
  have hTensor (ξ : F ⊗[K] L) :
      ∑ i, Algebra.trace F (F ⊗[K] L) (ξ * (1 ⊗ₜ[K] b i)) • (1 ⊗ₜ[K] y i) = ξ := by
    induction ξ using TensorProduct.inductionOn with
    | tmul a x =>
      conv_rhs => rw [← h x, TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have ha : a ⊗ₜ[K] (x * b i) = a • ((1 : F) ⊗ₜ[K] (x * b i)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, map_smul, algebra_trace_baseChange_tmul]
      simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one, mul_comm a,
        ← Algebra.smul_def, TensorProduct.smul_tmul]
    | add ξ η hξ hη =>
      conv_rhs => rw [← hξ, ← hη]
      simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib]
  have hp := congrArg (fun ξ => e ξ w) (hTensor (e.symm (Pi.single w z)))
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, AlgEquiv.apply_symm_apply,
    Pi.single_eq_same, hsingle, he] using hp

/-- At every finite place the global trace dual spans the actual local trace
dual. The characterization on the right uses the specified local field
trace, including at ramified places. -/
theorem finitePlace_span_globalTraceDual_eq_localTraceDual
    (v : HeightOneSpectrum (𝓞 K)) (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK := HeightOneSpectrum.isNonarchimedean_adicAbv K v
    let : Algebra vK.Completion w.1.Completion := AbsoluteValue.completionAlgebra vK w.1 w.2
    let O := absoluteValueCompletionIntegers w.1 (absoluteValueExtension_isNonarchimedean vK hvK w)
    (Submodule.span O (AbsoluteValue.toCompletion w.1 ''
      (Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L) : Set L)) : Set w.1.Completion) =
      {z | ∀ a : O, Algebra.trace vK.Completion w.1.Completion (z * a) ∈
        absoluteValueCompletionIntegers vK hvK} := by
  intro vK hvK algebraOwner O
  classical
  let E := w.1.Completion
  let F := vK.Completion
  let D := Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)
  let S := Submodule.span O (AbsoluteValue.toCompletion w.1 '' (D : Set L))
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    change z ∈ S at hz
    change ∀ a : O, Algebra.trace F E (z * a) ∈ absoluteValueCompletionIntegers vK hvK
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨d, hd, rfl⟩ := hz
      exact finitePlace_trace_mul_mem_integers_of_mem_globalTraceDual v d hd w
    | zero =>
      intro a
      rw [zero_mul, map_zero]
      exact (absoluteValueCompletionIntegers vK hvK).zero_mem
    | add x y _ _ hx hy =>
      intro a
      rw [add_mul, map_add]
      exact (absoluteValueCompletionIntegers vK hvK).add_mem _ _ (hx a) (hy a)
    | smul c x _ hx =>
      intro a
      change Algebra.trace F E ((c : E) * x * (a : E)) ∈ absoluteValueCompletionIntegers vK hvK
      rw [mul_comm (c : E) x, mul_assoc]
      exact hx (c * a)
  · intro z hz
    change ∀ a : O, Algebra.trace F E (z * a) ∈ absoluteValueCompletionIntegers vK hvK at hz
    change z ∈ S
    obtain ⟨n, b, y, hy, hb⟩ := Discriminant.exists_ringOfIntegers_traceDual_expansion K L
    rw [← finitePlace_traceDualExpansion (fun i => (b i : L)) y hb v w z]
    apply Submodule.sum_mem
    intro i _
    let a := finitePlaceIntegralDiagonal v (b i) w
    let t := Algebra.trace F E (z * (a : E))
    have ht : (algebraMap F E t) ∈ O := by
      change ‖algebraMap F E t‖ ≤ 1
      change AbsoluteValue.completionAbsoluteValue w.1 (algebraMap F E t) ≤ 1
      rw [AbsoluteValue.completionAbsoluteValue_extends vK w.1 w.2]
      exact hz a
    exact S.smul_mem (⟨algebraMap F E t, ht⟩ : O)
      (Submodule.subset_span ⟨y i, hy i, rfl⟩)

end AlgebraicNumberTheory.Valuations
