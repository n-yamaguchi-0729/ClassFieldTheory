/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Authors: Salvatore Mercuri, Kevin Buzzard
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Tactic.Ring.RingNF
public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.Ext
public import Lean.Elab.Tactic.RCases
public import Aesop.Frontend.Tactic
public import Aesop.BuiltinRules
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Differentials.Local.Order
public import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
public import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
public import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
public import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
public import Nyll.AlgebraicCurves.Differentials.Residues.Basic
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.ValuedFieldTheory.Valuation.Completion.AdicCompletion
public import Nyll.AlgebraicCurves.Places.Completion
public import Nyll.AlgebraicCurves.Places.CompletionQuotientFiniteness
public import Nyll.AlgebraicCurves.Differentials.Residues.TateTrace
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR

/-!
Compatibility of Tate constructions with finite extensions.
-/

@[expose] public section

open AlgebraicCurve.Place.CompletionQuotients

section ProofImplementation

attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
namespace AlgebraicCurves.Differentials.Residues.Proofs.TateCommFinite

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve
end AlgebraicCurve.Place
namespace Filter
open _root_.Filter
open _root_.Filter
end Filter
namespace IsDedekindDomain
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain
end IsDedekindDomain
namespace IsDedekindDomain
open _root_.IsDedekindDomain
namespace HeightOneSpectrum
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain
end IsDedekindDomain.HeightOneSpectrum
namespace IsLocalRing
open _root_.IsLocalRing
open _root_.IsLocalRing
end IsLocalRing
namespace LinearMap
open _root_.LinearMap
open _root_.LinearMap
end LinearMap
namespace ModularCurve
open _root_.ModularCurve
namespace KwF4R1V410a
open _root_.ModularCurve
end ModularCurve.KwF4R1V410a
namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve
end ModularCurve.KwF4gRRTate
namespace ModularCurve
open _root_.ModularCurve
namespace Lg37
open _root_.ModularCurve
end ModularCurve.Lg37
namespace MonoidWithZeroHom
open _root_.MonoidWithZeroHom
open _root_.MonoidWithZeroHom
end MonoidWithZeroHom
namespace Multiplicative
open _root_.Multiplicative
open _root_.Multiplicative
end Multiplicative
namespace NumberField
open _root_.NumberField
open _root_.NumberField
end NumberField
namespace Pointwise
open _root_.Pointwise
end Pointwise
namespace Submodule
open _root_.Submodule
open _root_.Submodule
end Submodule
namespace Topology
open _root_.Topology
end Topology
namespace WithZero
open _root_.WithZero
open _root_.WithZero
end WithZero

section
namespace IsLocalRing
open _root_.IsLocalRing
end IsLocalRing
open scoped _root_.IsLocalRing in
theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R

end

section
section


open _root_.LinearMap
open _root_.Submodule

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateFactoring

end ModularCurve.KwF4gRRTate

end

end

end

section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F}

variable (v : Place K F)

end Place

namespace Divisor
open _root_.AlgebraicCurve.Divisor
open _root_.AlgebraicCurve.Divisor

variable {K F}

end Divisor

namespace Pic0
open _root_.AlgebraicCurve.Pic0
open _root_.AlgebraicCurve.Pic0

variable {K F}

end Pic0

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

open scoped _root_.Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

variable (v : Place K F)

end Place

namespace Divisor
open _root_.AlgebraicCurve.Divisor
open _root_.AlgebraicCurve.Divisor

open scoped _root_.Pointwise

variable {K F}

end Divisor

namespace Pic0
open _root_.AlgebraicCurve.Pic0
open _root_.AlgebraicCurve.Pic0

open scoped _root_.Pointwise

variable {K F}

end Pic0

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

end Place

end AlgebraicCurve

end
end

end

section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f :=
  _root_.AlgebraicCurve.Place.ord_nonneg_of_mem v hf

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

variable (w : Place K F')

variable [Algebra.IsIntegral F F']

section RestrictDef

variable [Algebra K F] [IsScalarTower K F F']

end RestrictDef

end Restrict

end Place

end AlgebraicCurve

end
end

end

section
section

end

end

section
section


noncomputable section

open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.WithZero
open _root_.MonoidWithZeroHom

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section AdicCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end AdicCompletion

section Henselian

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end Henselian

section WithValLevel

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end WithValLevel

section CompletionComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end CompletionComap

section Bridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end Bridge

end AlgebraicCurve.Place

end
end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateResDef

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable [HasCanonicalLocalResidueKStar K L]

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

end TateAtoms

end ModularCurve.KwF4gRRTate

end

end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section PoleWindow

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

variable (K L) in
/-- Every completed element has a pole cleared by some power of an irreducible completed integer. -/
def KwF4gRRTateClearPole : Prop :=
  ∀ (u : Place K L) (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (fh : u.adicCompletion),
    ∃ M : ℕ, (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers

theorem clearPole_discharged : KwF4gRRTateClearPole K L :=
  fun u πh hπh fh => _root_.ModularCurve.KwF4gRRTate.clearPole u πh hπh fh

theorem lmul_mem_poleWindow (πh : u.adicCompletionIntegers) (M : ℕ) (fh : u.adicCompletion)
    (hM : (πh : u.adicCompletion) ^ M * fh ∈ u.adicCompletionIntegers)
    {a : u.adicCompletion} (ha : a ∈ u.adicCompletionIntegers) :
    fh * a ∈ poleWindowKSubmod u πh M := by
  rw [mem_poleWindowKSubmod_iff, ← mul_assoc]; exact mul_mem hM ha

theorem ker_tateProj_inf_integers :
    LinearMap.ker (tateProj u) ⊓ adicIntegersKSubmod u = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hker, hint⟩ := Submodule.mem_inf.mp hx
  have h0 : tateProj u x = 0 := LinearMap.mem_ker.mp hker
  rw [Submodule.mem_bot, ← tateProj_of_mem u hint, h0]

theorem finiteDimensional_ker_inf_poleWindow [u.FiniteResidue]
    (hPW : PoleWindowFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      ((LinearMap.ker (tateProj u) ⊓ poleWindowKSubmod u πh M : Submodule K _)) := by
  have := hPW u πh hπh M
  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  let A' : Submodule K P := A.comap P.subtype
  let ι : (LinearMap.ker (tateProj u) ⊓ P : Submodule K _) →ₗ[K] P ⧸ A' :=
    (A'.mkQ).comp (Submodule.inclusion inf_le_right)
  refine FiniteDimensional.of_injective ι ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro xh hxker
  obtain ⟨x, hxkp⟩ := xh
  obtain ⟨hxk, hxp⟩ := Submodule.mem_inf.mp hxkp
  simp only [ι, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.inclusion_apply] at hxker
  have hxA : x ∈ A := hxker
  have hx0 : x = 0 := by
    have hbot : x ∈ (⊥ : Submodule K u.adicCompletion) := by
      rw [← ker_tateProj_inf_integers u]; exact Submodule.mem_inf.mpr ⟨hxk, hxA⟩
    exact (Submodule.mem_bot K).mp hbot
  exact Subtype.ext hx0

theorem finiteDimensional_principalPart_range [u.FiniteResidue]
    (hCP : KwF4gRRTateClearPole K L) (hPW : PoleWindowFinite K L)
    (fh : u.adicCompletion) :
    FiniteDimensional K
      (LinearMap.range
        ((LinearMap.id - tateProj u) ∘ₗ lmulK u fh ∘ₗ (adicIntegersKSubmod u).subtype)) := by
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hM⟩ := hCP u πh hπh fh
  have := finiteDimensional_ker_inf_poleWindow u hPW πh hπh M
  refine Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.ker (tateProj u) ⊓ poleWindowKSubmod u πh M) ?_
  rintro y ⟨⟨a, ha⟩, rfl⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
    LinearMap.id_apply]
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, tateProj_of_mem u (tateProj_mem_integers u _), sub_self]
  · exact sub_mem (lmul_mem_poleWindow u πh M fh hM ha)
      (adicIntegersKSubmod_le_poleWindowKSubmod u πh M (tateProj_mem_integers u _))

theorem tateComm_target_le_range (pA φ ψ : u.adicCompletion →ₗ[K] u.adicCompletion)
    (Rf Rg : Submodule K u.adicCompletion) :
    Submodule.map (pA ∘ₗ ψ) Rf ⊔ Submodule.map (pA ∘ₗ φ) Rg ≤ LinearMap.range pA := by
  refine sup_le ?_ ?_ <;>
  · rintro y ⟨x, _, rfl⟩; exact LinearMap.mem_range_self pA _

theorem commFinite_of_clearPole_of_poleWindowFinite
    [∀ u : Place K L, u.FiniteResidue]
    (hCP : KwF4gRRTateClearPole K L) (hPW : PoleWindowFinite K L) :
    KwF4gRRTateCommFinite K L := by
  intro u fh gh
  have hcomm : lmulK u fh ∘ₗ lmulK u gh = lmulK u gh ∘ₗ lmulK u fh := by
    ext x
    change fh * (gh * x) = gh * (fh * x)
    ring
  have hRf := finiteDimensional_principalPart_range u hCP hPW fh
  have hRg := finiteDimensional_principalPart_range u hCP hPW gh
  set pA := tateProj u
  set A := adicIntegersKSubmod u
  set Rf := LinearMap.range ((LinearMap.id - pA) ∘ₗ lmulK u fh ∘ₗ A.subtype)
  set Rg := LinearMap.range ((LinearMap.id - pA) ∘ₗ lmulK u gh ∘ₗ A.subtype)
  set S : Submodule K u.adicCompletion :=
    Submodule.map (pA ∘ₗ lmulK u gh) Rf ⊔ Submodule.map (pA ∘ₗ lmulK u fh) Rg
  have : FiniteDimensional K (Submodule.map (pA ∘ₗ lmulK u gh) Rf) := Module.Finite.map _ _
  have : FiniteDimensional K (Submodule.map (pA ∘ₗ lmulK u fh) Rg) := Module.Finite.map _ _
  have hSfin : FiniteDimensional K S := Submodule.finiteDimensional_sup _ _
  have hSle : S ≤ LinearMap.range pA :=
    tateComm_target_le_range u pA (lmulK u fh) (lmulK u gh) Rf Rg
  have : FiniteDimensional K (S.comap (LinearMap.range pA).subtype) := by
    have e := Submodule.comapSubtypeEquivOfLe hSle
    exact FiniteDimensional.of_injective e.toLinearMap e.injective
  refine Submodule.finiteDimensional_of_le (S₂ := S.comap (LinearMap.range pA).subtype) ?_
  rintro y ⟨⟨a, haR⟩, rfl⟩
  have haA : a ∈ adicIntegersKSubmod u := range_tateProj u ▸ haR
  rw [Submodule.mem_comap, Submodule.subtype_apply, tateCommRestrict_apply,
    tateComm_eq_of_commute hcomm a]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact ⟨(lmulK u fh) a - pA ((lmulK u fh) a), ⟨⟨a, haA⟩, rfl⟩, rfl⟩
  · exact ⟨(lmulK u gh) a - pA ((lmulK u gh) a), ⟨⟨a, haA⟩, rfl⟩, rfl⟩

theorem commFinite_of_poleWindowFinite [∀ u : Place K L, u.FiniteResidue]
    (hPW : PoleWindowFinite K L) :
    KwF4gRRTateCommFinite K L :=
  commFinite_of_clearPole_of_poleWindowFinite
    clearPole_discharged hPW

end PoleWindow

end ModularCurve.KwF4gRRTate

end

end

end

section
section


open scoped _root_.WithZero _root_.Multiplicative _root_.Topology
open _root_.Filter

namespace IsDedekindDomain
open _root_.IsDedekindDomain
namespace HeightOneSpectrum
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

namespace adicCompletion
open _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion
open _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion

end adicCompletion

section NumberField

open _root_.NumberField

variable (F : Type*) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

end NumberField

end IsDedekindDomain.HeightOneSpectrum

section AxiomAudit

open _root_.IsDedekindDomain.HeightOneSpectrum

end AxiomAudit

end

end

section
section


noncomputable section

open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.WithZero
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4R1V410a
open _root_.ModularCurve

section Bridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

local notation "O_w" => w.toValuationSubring
local notation "𝔪_w" => IsLocalRing.maximalIdeal w.toValuationSubring
local notation "O_W" => w.adicCompletionIntegers
local notation "𝔪_W" => w.heightOneSpectrum.completionIdeal F

end Bridge

end ModularCurve.KwF4R1V410a

end
end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section PoleWindowShift

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem commFinite_of_DVRQuotPowKFinite [∀ u : Place K L, u.FiniteResidue]
    (hDVR : QuotientPowersFinite K L) :
    KwF4gRRTateCommFinite K L :=
  commFinite_of_poleWindowFinite
    (poleWindowFinite_of_quotientPowersFinite hDVR)

end PoleWindowShift

end ModularCurve.KwF4gRRTate

end

end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DVRQuotDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem commFinite_of_cotangent [∀ u : Place K L, u.FiniteResidue]
    (hCot : CotangentQuotientFinite K L) :
    KwF4gRRTateCommFinite K L :=
  commFinite_of_DVRQuotPowKFinite
    (quotientPowersFinite_of_cotangent hCot)

end DVRQuotDischarge

end ModularCurve.KwF4gRRTate

end

end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DVRCotangentDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem commFinite [∀ u : Place K L, u.FiniteResidue] :
    KwF4gRRTateCommFinite K L :=
  commFinite_of_cotangent cotangentQuotientFinite

end DVRCotangentDischarge

end ModularCurve.KwF4gRRTate

end

end

end

theorem _root_.AlgebraicCurve.tateCommFinite {K L : Type*} [Field K] [Field L] [Algebra K L]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue] :
    ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L :=
  ModularCurve.KwF4gRRTate.commFinite
end AlgebraicCurves.Differentials.Residues.Proofs.TateCommFinite
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp]
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
