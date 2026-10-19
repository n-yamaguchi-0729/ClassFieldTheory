/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnitKernel
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnitLatticeAction
import Nyll.GaloisCohomology.Cyclic.Herbrand.FiniteErrors

/-!
# Herbrand comparison for actual S-units

Any finite cyclic semilinear action preserving the actual set `S` acts on its
S-units and on its supported degree-zero divisor lattice. Their actual divisor
map has the finite kernel and cokernel already proved geometrically. The
generic finite-error theorem therefore identifies their Herbrand quotients.
-/

noncomputable section

namespace FunctionField.SUnits

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The actual S-unit action restricted along a group of semilinear automorphisms preserving `S`. -/
@[reducible]
def unitsAction {G : Type*} [Group G] (S : Finset (Place k K))
    (ρ : G →* stabilizer k K S) : MulDistribMulAction G (units k K S) :=
  MulDistribMulAction.compHom (units k K S) ρ

/-- The same group acts on the multiplicative form of the actual divisor lattice. -/
@[reducible]
def latticeAction {G : Type*} [Group G] (S : Finset (Place k K))
    (ρ : G →* stabilizer k K S) :
    MulDistribMulAction G (Multiplicative (divisorLattice k K S)) := by
  let : DistribMulAction G (divisorLattice k K S) :=
    DistribMulAction.compHom (divisorLattice k K S) ρ
  exact multiplicativeMulDistribMulActionOfDistribMulAction G (divisorLattice k K S)

variable [HasPrincipalDivisors k K]

/-- The actual S-unit divisor homomorphism in multiplicative group notation. -/
def multiplicativeDivisor (S : Finset (Place k K)) :
    units k K S →* Multiplicative (divisorLattice k K S) :=
  (divisor S).toMultiplicativeRight

/-- The finite-field divisor theorem supplies the finite kernel in multiplicative notation. -/
theorem finite_ker_multiplicativeDivisor [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K] (S : Finset (Place k K)) :
    Finite (multiplicativeDivisor S).ker := by
  have : Finite (divisor S).ker := finite_ker_divisor k K S
  let f : (multiplicativeDivisor S).ker → (divisor S).ker :=
    fun x => ⟨Additive.ofMul x.val, x.2⟩
  exact Finite.of_injective f (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

/-- The multiplicative divisor image is the kernel of the actual Picard class map. -/
theorem range_multiplicativeDivisor_eq_ker (S : Finset (Place k K)) :
    (multiplicativeDivisor S).range = (classMap S).toMultiplicative.ker := by
  ext D
  change D.toAdd ∈ (divisor S).range ↔ D.toAdd ∈ (classMap S).ker
  rw [range_divisor_eq_ker_classMap]

/-- The actual finite Picard group also supplies the multiplicative divisor cokernel. -/
theorem finite_cokernel_multiplicativeDivisor [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K] (S : Finset (Place k K)) :
    Finite (Multiplicative (divisorLattice k K S) ⧸ (multiplicativeDivisor S).range) := by
  have : Finite (Pic0 k K) := FunctionField.finite_pic0 k K
  rw [range_multiplicativeDivisor_eq_ker]
  exact Finite.of_equiv (classMap S).toMultiplicative.range
    (QuotientGroup.quotientKerEquivRange (classMap S).toMultiplicative).symm.toEquiv

/-- The multiplicative divisor map respects the concrete restricted semilinear actions. -/
theorem multiplicativeDivisor_equivariant {G : Type*} [Group G]
    (S : Finset (Place k K)) (ρ : G →* stabilizer k K S) :
    let _ : MulDistribMulAction G (units k K S) := unitsAction S ρ
    let _ : MulDistribMulAction G (Multiplicative (divisorLattice k K S)) := latticeAction S ρ
    ∀ (g : G) (x : units k K S), multiplicativeDivisor S (g • x) =
      g • multiplicativeDivisor S x := by
  intro hUnits hLattice g x
  exact congrArg Multiplicative.ofAdd (divisor_smul S (ρ g) x)

end FunctionField.SUnits

namespace FunctionField.SUnits

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K G : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] [Group G] [Fintype G]

/-- The actual S-units have finite Tate quotients exactly when their actual divisor lattice does. -/
theorem herbrandQuotientDefined_iff_lattice (S : Finset (Place k K))
    (ρ : G →* stabilizer k K S) (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    let _ : MulDistribMulAction G (units k K S) := unitsAction S ρ
    let _ : MulDistribMulAction G (Multiplicative (divisorLattice k K S)) := latticeAction S ρ
    HerbrandQuotientDefined G (units k K S) σ ↔
      HerbrandQuotientDefined G (Multiplicative (divisorLattice k K S)) σ := by
  let : MulDistribMulAction G (units k K S) := unitsAction S ρ
  let : MulDistribMulAction G (Multiplicative (divisorLattice k K S)) := latticeAction S ρ
  have : Finite (multiplicativeDivisor S).ker := finite_ker_multiplicativeDivisor S
  have : Finite (Multiplicative (divisorLattice k K S) ⧸ (multiplicativeDivisor S).range) :=
    finite_cokernel_multiplicativeDivisor S
  exact herbrandQuotientDefined_iff_of_finite_kernel_cokernel
    (multiplicativeDivisor S) (multiplicativeDivisor_equivariant S ρ) σ hgen

/-- Actual S-units and their actual divisor lattice have the same defined Herbrand quotient. -/
theorem herbrandQuotient_eq_lattice (S : Finset (Place k K))
    (ρ : G →* stabilizer k K S) (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    let _ : MulDistribMulAction G (units k K S) := unitsAction S ρ
    let _ : MulDistribMulAction G (Multiplicative (divisorLattice k K S)) := latticeAction S ρ
    ∀ hL : HerbrandQuotientDefined G (Multiplicative (divisorLattice k K S)) σ,
      ∃ hU : HerbrandQuotientDefined G (units k K S) σ,
        let _ : Finite (HerbrandH0 G (units k K S)) := hU.1
        let _ : Finite (HerbrandHMinusOne G (units k K S) σ) := hU.2
        let _ : Finite (HerbrandH0 G (Multiplicative (divisorLattice k K S))) := hL.1
        let _ : Finite (HerbrandHMinusOne G (Multiplicative (divisorLattice k K S)) σ) := hL.2
        herbrandQuotient (G := G) (A := units k K S) σ =
          herbrandQuotient (G := G) (A := Multiplicative (divisorLattice k K S)) σ := by
  intro hUnits hLattice hL
  have hU := (herbrandQuotientDefined_iff_lattice S ρ σ hgen).mpr hL
  refine ⟨hU, ?_⟩
  intro hU0 hUm hL0 hLm
  have : Finite (multiplicativeDivisor S).ker := finite_ker_multiplicativeDivisor S
  have : Finite (Multiplicative (divisorLattice k K S) ⧸ (multiplicativeDivisor S).range) :=
    finite_cokernel_multiplicativeDivisor S
  exact herbrandQuotient_eq_of_finite_kernel_cokernel
    (multiplicativeDivisor S) (multiplicativeDivisor_equivariant S ρ) σ hgen

end FunctionField.SUnits
