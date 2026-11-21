/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Differentials.Local.Order
public import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
public import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
public import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
public import Nyll.AlgebraicCurves.Differentials.Residues.Basic
public import Nyll.ValuedFieldTheory.Valuation.Completion.AdicCompletion
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.Abel
public import Nyll.AlgebraicCurves.Places.Completion
public import Nyll.AlgebraicCurves.Places.CompletionQuotientFiniteness

/-!
# Differentials, residues, and divisor correspondences

Finite-rank traces and Tate commutators on completions, with residue agreement and completed trace
identities.
-/

@[expose] public section

open AlgebraicCurve.Place.CompletionQuotients

open LinearMap Submodule

noncomputable section

namespace ModularCurve.KwF4gRRTate

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The trace of an endomorphism restricted to its finite-dimensional range. -/
def finrankTrace (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] : K :=
  LinearMap.trace K (LinearMap.range φ)
    (φ.restrict (fun x _ => LinearMap.mem_range_self φ x))

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The difference of the two projected composites defining the Tate commutator. -/
def tateComm (pA φ ψ : V →ₗ[K] V) : V →ₗ[K] V :=
  pA ∘ₗ φ ∘ₗ pA ∘ₗ ψ - pA ∘ₗ ψ ∘ₗ pA ∘ₗ φ

theorem tateComm_apply (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateComm pA φ ψ x = pA (φ (pA (ψ x))) - pA (ψ (pA (φ x))) := rfl

theorem tateComm_mem_range (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateComm pA φ ψ x ∈ LinearMap.range pA :=
  sub_mem (LinearMap.mem_range_self pA _) (LinearMap.mem_range_self pA _)

theorem tateComm_antisymm (pA φ ψ : V →ₗ[K] V) :
    tateComm pA φ ψ = - tateComm pA ψ φ := by
  unfold tateComm; rw [neg_sub]

/-- The Tate commutator restricted to the range of the projection. -/
def tateCommRestrict (pA φ ψ : V →ₗ[K] V) :
    LinearMap.range pA →ₗ[K] LinearMap.range pA :=
  (tateComm pA φ ψ).restrict (fun x _ => tateComm_mem_range pA φ ψ x)

theorem tateCommRestrict_apply (pA φ ψ : V →ₗ[K] V) (a : LinearMap.range pA) :
    (tateCommRestrict pA φ ψ a : V) = tateComm pA φ ψ (a : V) := rfl

/-- The trace of the Tate commutator on the finite-dimensional range of its restriction. -/
def tateCommTrace (pA φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ))] : K :=
  finrankTrace (tateCommRestrict pA φ ψ)

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem tateComm_eq_of_commute {pA φ ψ : V →ₗ[K] V}
    (hcomm : φ ∘ₗ ψ = ψ ∘ₗ φ) (a : V) :
    tateComm pA φ ψ a
      = pA (ψ (φ a - pA (φ a))) - pA (φ (ψ a - pA (ψ a))) := by
  have hφψ : φ (ψ a) = ψ (φ a) := by
    have := congrArg (fun f => f a) (congrArg DFunLike.coe hcomm)
    simpa using this
  rw [tateComm_apply, map_sub, map_sub, map_sub, map_sub, hφψ]
  abel

end TateFactoring

end ModularCurve.KwF4gRRTate

end


noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

/-- Pullback of a Kähler differential along the scalar tower. -/
def kaehlerPullback (ωE : Ω[E⁄K]) : Ω[F⁄K] :=
  KaehlerDifferential.map K K E F ωE

variable {K F E}

variable (K F E)
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end CorrectedCarrier

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Functions whose product with the differential coefficient is integral at the chosen
place. -/
def regularSubmodule (w : Place K F) (ωF : Ω[F⁄K]) : Submodule K F where
  carrier := {f : F | f * w.differentialCoeff ωF ∈ w.toValuationSubring}
  zero_mem' := by simp only [Set.mem_ofPred_eq, zero_mul]; exact zero_mem _
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, add_mul]; exact add_mem hf hg
  smul_mem' c f hf := by
    simp only [Set.mem_ofPred_eq, Algebra.smul_def, mul_assoc]
    exact mul_mem (w.algebraMap_mem' c) hf

end Place

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

section KaehlerCotrace

variable (K E F : Type*) [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- The scalar-linear Kähler differential map along the field extension. -/
abbrev kaehlerCotrace : Ω[E⁄K] →ₗ[E] Ω[F⁄K] :=
  KaehlerDifferential.map K K E F

variable {K E F}

end KaehlerCotrace

end AlgebraicCurve

end

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain

noncomputable section

namespace AlgebraicCurve

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

/-- The residue of a chosen field representative of a completion element modulo the
completion integers. -/
def kwHgfV352_localResidueCompletion (v : Place K E) (xh : v.adicCompletion) :
    v.ResidueField :=
  v.localResidue (exists_sub_mem_adicCompletionIntegers v xh).choose

end LocalResidueCompletion

section CompletionTraceAt

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

/-- The completed field trace at a place, transported to the completion of its base place. -/
def kwHgfV352_completionTraceAt [FiniteDimensional E F]
    (v : Place K E) (w' : Place K F) (hw' : w' ∈ v.fiber F) (g : F) :
    v.adicCompletion :=
  Place.mem_fiber.mp hw' ▸ completionTraceF' E w' g

end CompletionTraceAt

section MPGKPowBasisLocalMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

/-- The local residue and completed-trace identity for powers of an integral element
multiplied by inverse uniformizer powers. -/
def KwHgfV352R3MPGKPowBasisLocal : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [∀ w : Place K F, w.FiniteResidue]
    [FiniteDimensional E F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F)
    (_ : ∀ w'' ∈ v.fiber F,
      w''.differentialCoeff (kaehlerPullback K F E ωE) ∈ w''.toValuationSubring)
    (θ : F) (_ : ∀ w' ∈ v.fiber F, θ ∈ w'.toValuationSubring)
    (π : F) (_ : π ≠ 0) (_ : w.ord π = 1)
    (_ : ∀ w' ∈ v.fiber F, w' ≠ w → w'.ord π = 0)
    (j : ℕ) (_ : j < Module.finrank K w.ResidueField) (k : ℕ),
    kaehlerResidueTerm (kaehlerPullback K F E ωE)
        (diagonalHom K F (θ ^ j * (π ^ (k + 1))⁻¹)) w
      = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (kwHgfV352_completionTraceAt v w hw (θ ^ j * (π ^ (k + 1))⁻¹)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE)))

end MPGKPowBasisLocalMint

section CompletionTraceSumMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

/-- The field trace in a base completion equals the sum of the completed traces over its
place fibre. -/
def KwHgfV352CompletionTraceSum : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (g : F),
    algebraMap E v.adicCompletion (Algebra.trace E F g)
      = ∑ w' ∈ (v.fiber F).attach, kwHgfV352_completionTraceAt v w'.1 w'.2 g

end CompletionTraceSumMint

end AlgebraicCurve

open AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule
open ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve.KwF4gRRTate

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- A projection onto the completion integers along a chosen complementary submodule. -/
def tateProj : u.adicCompletion →ₗ[K] u.adicCompletion :=
  letI B := Classical.choose (Submodule.exists_isCompl (adicIntegersKSubmod u))
  (adicIntegersKSubmod u).subtype ∘ₗ
    Submodule.projectionOnto (adicIntegersKSubmod u) B
      (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))

theorem tateProj_mem_integers (x : u.adicCompletion) :
    tateProj u x ∈ u.adicCompletionIntegers :=
  (mem_adicIntegersKSubmod_iff u _).mp
    (Submodule.coe_mem
      (Submodule.projectionOnto (adicIntegersKSubmod u) _
        (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u))) x))

theorem tateProj_of_mem {x : u.adicCompletion} (hx : x ∈ u.adicCompletionIntegers) :
    tateProj u x = x := by
  have h := Submodule.projectionOnto_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))
    (⟨x, (mem_adicIntegersKSubmod_iff u x).mpr hx⟩ : adicIntegersKSubmod u)
  have hcoe := congrArg (Subtype.val (p := fun y => y ∈ adicIntegersKSubmod u)) h
  exact hcoe

theorem tateProj_idem : tateProj u ∘ₗ tateProj u = tateProj u := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact tateProj_of_mem u (tateProj_mem_integers u x)

theorem range_tateProj : LinearMap.range (tateProj u) = adicIntegersKSubmod u := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact tateProj_mem_integers u y
  · intro x hx
    exact ⟨x, tateProj_of_mem u hx⟩

end TateProj

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- Multiplication by a completion element as a base-field linear endomorphism. -/
abbrev lmulK (fh : u.adicCompletion) : u.adicCompletion →ₗ[K] u.adicCompletion :=
  (Algebra.lmul K u.adicCompletion) fh

/-- The Tate commutator trace of two multiplication endomorphisms with respect to the
integer projection. -/
def tateRes (fh gh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))] : K :=
  tateCommTrace (tateProj u) (lmulK u fh) (lmulK u gh)

end TateResDef

section PoleWindowImage

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- Finite dimensionality of the principal-part image of integral completion elements after
multiplication. -/
def PoleWindowImageFinite : Prop :=
  ∀ (fh : u.adicCompletion),
    FiniteDimensional K (Submodule.map (adicIntegersKSubmod u).mkQ
      (Submodule.map (lmulK u fh) (adicIntegersKSubmod u)))

theorem lmul_adicIntegers_subset_poleWindow (fh : u.adicCompletion)
    (πh : u.adicCompletionIntegers) (M : ℕ)
    (hfhM : (πh : u.adicCompletion) ^ M * fh ∈ u.adicCompletionIntegers) :
    Submodule.map (lmulK u fh) (adicIntegersKSubmod u) ≤ poleWindowKSubmod u πh M := by
  rintro x ⟨a, ha, rfl⟩
  rw [mem_poleWindowKSubmod_iff]
  show (πh : u.adicCompletion)^M * (lmulK u fh) a ∈ u.adicCompletionIntegers
  have : (lmulK u fh) a = fh * a := rfl
  rw [this, ← mul_assoc]
  exact mul_mem hfhM (show a ∈ u.adicCompletionIntegers from ha)

variable [u.FiniteResidue]

theorem poleWindowImageFinite :
    PoleWindowImageFinite u := by
  intro fh
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hfhM⟩ := _root_.ModularCurve.KwF4gRRTate.clearPole u πh hπh fh
  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  have hsub : Submodule.map A.mkQ (Submodule.map (lmulK u fh) A)
      ≤ Submodule.map A.mkQ P :=
    Submodule.map_mono (lmul_adicIntegers_subset_poleWindow u fh πh M hfhM)
  suffices hPim : FiniteDimensional K (Submodule.map A.mkQ P : Submodule K _) by
    exact Submodule.finiteDimensional_of_le hsub
  have : FiniteDimensional K (P ⧸ (A.comap P.subtype)) :=
    poleWindowFinite (K := K) (L := L) u πh hπh M
  let r : P →ₗ[K] (u.adicCompletion ⧸ A) := A.mkQ ∘ₗ P.subtype
  have hrange : LinearMap.range r = Submodule.map A.mkQ P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker r = A.comap P.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e : (P ⧸ (A.comap P.subtype)) ≃ₗ[K] LinearMap.range r := hker ▸ r.quotKerEquivRange
  rw [← hrange]
  exact e.finiteDimensional

end PoleWindowImage

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- All the projected Tate commutators have finite-dimensional range. -/
def KwF4gRRTateCommFinite : Prop :=
  ∀ (u : Place K L) (fh gh : u.adicCompletion),
    FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))

variable [HasCanonicalLocalResidueKStar K L]

/-- The Tate residue against the uniformizer agrees with the traced local completion
residue. -/
def KwF4gRRTateAgreement (hfin : KwF4gRRTateCommFinite K L) : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (fh : u.adicCompletion),
    haveI := hfin u fh (algebraMap L u.adicCompletion u.uniformizer)
    tateRes u fh (algebraMap L u.adicCompletion u.uniformizer)
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh)

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

/-- The Tate residue transforms by the pulled-back differential coefficient under a place
extension. -/
def KwF4gRRTateChainRule (hfinF : KwF4gRRTateCommFinite K F) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] [Nontrivial Ω[F⁄K]]
    (v : Place K E) [v.DCoordGenerates] (w : Place K F) [w.DCoordGenerates]
    (_ : w ∈ v.fiber F) (fh : w.adicCompletion),
    haveI := hfinF w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    haveI := hfinF w (fh * algebraMap F w.adicCompletion
      (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
      (algebraMap F w.adicCompletion w.uniformizer)
    tateRes w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes w (fh * algebraMap F w.adicCompletion
          (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
          (algebraMap F w.adicCompletion w.uniformizer)

/-- The upstairs Tate residue agrees with the downstairs Tate residue of the completed
trace. -/
def KwF4gRRTateTraceCompat (hfinF : KwF4gRRTateCommFinite K F)
    (hfinE : KwF4gRRTateCommFinite K E) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F),
    haveI := hfinF w (algebraMap F w.adicCompletion g)
      (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    haveI := hfinE v (kwHgfV352_completionTraceAt v w hw g)
      (algebraMap E v.adicCompletion v.uniformizer)
    tateRes w (algebraMap F w.adicCompletion g)
        (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes v (kwHgfV352_completionTraceAt v w hw g)
          (algebraMap E v.adicCompletion v.uniformizer)

end TateAtoms

end ModularCurve.KwF4gRRTate

end

open AlgebraicCurve AlgebraicCurve.Place KaehlerDifferential

noncomputable section

namespace ModularCurve.KwF4R1V391a

section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

/-- A pulled-back coordinate differential residue equals the base completion residue of the
completed trace. -/
def KwF4R1V391aResidueTraceCompletionCommute
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] : Prop :=
  ∀ [∀ w : Place K F, w.FiniteResidue] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] (v : Place K E) [v.DCoordGenerates]
    (w : Place K F) [w.DCoordGenerates] (_ : w ∈ v.fiber F) (g : F),
    kaehlerResidueTerm (kaehlerPullback K F E v.dCoord) (diagonalHom K F g) w
      = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (kwHgfV352_completionTraceAt v w ‹w ∈ v.fiber F› g))

end Mint

end ModularCurve.KwF4R1V391a

noncomputable section

namespace AlgebraicCurve

open scoped Polynomial

section KCurrencyRow

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

/-- An upstairs canonical residue family induces a base residue family compatible with
differential pullback and the trace over each place fibre. -/
def FiberKaehlerCotraceResidueIdentityK : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0),
    ∃ RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK,
      ∀ (v : Place K E) (f : F),
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F f) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F f)) v

end KCurrencyRow

end AlgebraicCurve

end

noncomputable section

namespace AlgebraicCurve

open scoped Polynomial

section KCurrencyRowA

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

/-- A base canonical residue family satisfies the fibre trace identity for functions
singular at at most one place of each fibre. -/
def CotraceResidueIdentityOnFiberLocalizedK : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0),
    ∃ RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK,
      ∀ (v : Place K E) (p : F),
        (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
          p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
          p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F p) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v

end KCurrencyRowA

end AlgebraicCurve

end
