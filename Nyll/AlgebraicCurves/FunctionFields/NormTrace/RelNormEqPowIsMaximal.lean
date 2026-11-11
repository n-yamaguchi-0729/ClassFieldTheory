/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.NormalClosure
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Rel Norm eq pow of is Maximal of is Separable
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.RelNorm_eq_pow_of_isMaximal_of_isSeparable

noncomputable section

namespace AlgebraicCurve

namespace F10d

section Closure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]

-- Register only the required fraction-field map, as in Ring.NormalClosure.
local instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra R (FractionRing S)

local notation3 "𝕂" => FractionRing R
local notation3 "𝕃" => FractionRing S
local notation3 "𝔼" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)
    (AlgebraicClosure (FractionRing S))
local notation3 "𝕋" => Ring.NormalClosure R S

local instance : Algebra S 𝔼 := ((algebraMap 𝕃 𝔼).comp (algebraMap S 𝕃)).toAlgebra

local instance : IsScalarTower S 𝕃 𝔼 := IsScalarTower.of_algebraMap_eq' rfl

local instance : Algebra 𝕋 𝔼 := inferInstanceAs (Algebra (integralClosure S 𝔼) 𝔼)
local instance : IsScalarTower S 𝕋 𝔼 := by
  change IsScalarTower S (integralClosure S 𝔼) 𝔼
  infer_instance

local instance : IsIntegralClosure 𝕋 S 𝔼 := integralClosure.isIntegralClosure S 𝔼

local instance : IsScalarTower R 𝕋 𝔼 :=
  IsScalarTower.of_algebraMap_eq fun r => Subtype.ext <| by
    change algebraMap R (AlgebraicClosure 𝕃) r
      = algebraMap 𝕃 (AlgebraicClosure 𝕃) (algebraMap S 𝕃 (algebraMap R S r))
    rw [IsScalarTower.algebraMap_apply R 𝕃 (AlgebraicClosure 𝕃), IsScalarTower.algebraMap_apply R
      S 𝕃]

local instance : FaithfulSMul S 𝔼 := (faithfulSMul_iff_algebraMap_injective S 𝔼).mpr <|
      (FaithfulSMul.algebraMap_injective 𝕃 𝔼).comp (FaithfulSMul.algebraMap_injective S 𝕃)

variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

private theorem isSeparable_normalClosure : Algebra.IsSeparable 𝕂 𝔼 := by
  rw [← le_separableClosure_iff, normalClosure_le_iff]
  intro f x hx
  obtain ⟨y, rfl⟩ := f.mem_fieldRange.mp hx
  rw [mem_separableClosure_iff]
  exact IsSeparable.map f (f : 𝕃 →+* AlgebraicClosure 𝕃).injective
    (Algebra.IsSeparable.isSeparable 𝕂 y)

local instance : Algebra.IsSeparable 𝕂 𝔼 := isSeparable_normalClosure R S

local instance : Algebra.IsSeparable 𝕃 𝔼 := Algebra.isSeparable_tower_top_of_isSeparable 𝕂 𝕃 𝔼

variable [Module.Finite R S]

local instance : FiniteDimensional 𝕃 𝔼 := Module.Finite.right 𝕂 𝕃 𝔼
local instance : IsFractionRing 𝕋 𝔼 := by
  change IsFractionRing (integralClosure S 𝔼) 𝔼
  exact integralClosure.isFractionRing_of_finite_extension 𝕃 𝔼

local instance : IsAlgClosure 𝕂 (AlgebraicClosure 𝕃) :=
  IsAlgClosure.ofAlgebraic 𝕂 𝕃 (AlgebraicClosure 𝕃)

local instance : Normal 𝕂 𝔼 := normalClosure.normal _ _ _

local instance : IsGalois 𝕂 𝔼 := IsGalois.mk
local instance : Algebra 𝕂 (FractionRing 𝕋) := FractionRing.liftAlgebra R (FractionRing 𝕋)

local instance : Algebra 𝕃 (FractionRing 𝕋) := FractionRing.liftAlgebra S (FractionRing 𝕋)

variable {R S}
private theorem relNorm_eq_pow_of_isMaximal_fractionRing
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R :=
  Ideal.relNorm_eq_pow_of_isMaximal P p

end Closure

section Transport

variable {R S : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]
  [IsDedekindDomain R] [IsDedekindDomain S]

-- Register only the required fraction-field map, as in Ring.NormalClosure.
local instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra R (FractionRing S)

private theorem relNorm_eq_pow_of_isMaximal_of_isSeparable (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv (by
        ext x
        simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
          (FractionRing.algEquiv S L).symm x)
  exact relNorm_eq_pow_of_isMaximal_fractionRing P p

end Transport

end F10d

end AlgebraicCurve

end

theorem _root_.AlgebraicCurve.relNorm_eq_pow_of_isMaximal_of_isSeparable {R S : Type*} [CommRing
  R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
      [Module.IsTorsionFree R S]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
      [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K
      L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R :=
  AlgebraicCurve.F10d.relNorm_eq_pow_of_isMaximal_of_isSeparable K L P p

end AlgebraicCurves.FunctionFields.Proofs.RelNorm_eq_pow_of_isMaximal_of_isSeparable
end ProofImplementation
