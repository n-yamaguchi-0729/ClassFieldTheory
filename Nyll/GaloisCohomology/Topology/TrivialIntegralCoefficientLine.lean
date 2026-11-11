/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ProP.TrivialZModP
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.ULift
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Module.NatInt

/-!
# Actual trivial integral coefficient lines

An invariant element killed by p gives a continuous equivariant integral
map from the existing lifted mod-p coefficient object. If p is prime and
the element is nonzero, this map is injective.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory ContRepresentation

namespace TopRep

variable (G : Type u) [Group G] (X : TopRep.{u} ℤ G) (p : ℕ)

/-- The actual coefficient morphism determined by an invariant p-torsion element. -/
def trivialIntegralCoefficientLineHom (v : X) (hpv : p • v = 0)
    (hv : ∀ g : G, X.ρ g v = v) :
    ClassFieldTower.Cohomology.trivialIntegralZModPLifted p G ⟶ X := by
  let T := ClassFieldTower.Cohomology.trivialIntegralZModPLifted p G
  have : DiscreteTopology T := inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))
  let a : ℤ →+ X :=
    { toFun := fun m => m • v
      map_zero' := zero_zsmul v
      map_add' := fun m n => add_zsmul v m n }
  have ha : a p = 0 := by
    let : Module ℤ X := X.hV2
    change (p : ℤ) • v = 0
    exact ((Int.cast_smul_eq_zsmul ℤ (p : ℤ) v).symm.trans
      (Nat.cast_smul_eq_nsmul ℤ p v)).trans hpv
  let f : ZMod p →+ X := ZMod.lift p ⟨a, ha⟩
  let e : ULift.{u} (ZMod p) →+ X :=
    f.comp (AddEquiv.ulift : ULift.{u} (ZMod p) ≃+ ZMod p).toAddMonoidHom
  let : Module ℤ X := X.hV2
  let l : T →ₗ[ℤ] X :=
    { toFun := fun z => e z
      map_add' := fun z w => e.map_add z w
      map_smul' := fun m z => map_intCast_smul e ℤ ℤ m z }
  let q : T.ρ →ⁱL X.ρ :=
    { toLinearMap := l
      cont := continuous_of_discreteTopology
      isIntertwining' := fun g => by
        apply ContinuousLinearMap.ext
        intro z
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        change e (T.ρ g z) = X.ρ g (e z)
        have hT : T.ρ g z = z := rfl
        rw [hT]
        obtain ⟨m, hm⟩ := ZMod.intCast_surjective z.down
        have hz : z = ULift.up (m : ZMod p) := ULift.ext hm.symm
        rw [hz]
        change f (m : ZMod p) = X.ρ g (f (m : ZMod p))
        rw [ZMod.lift_coe]
        change @SMul.smul ℤ X ZSMul.toSMul m v =
          X.ρ g (@SMul.smul ℤ X ZSMul.toSMul m v)
        calc
          @SMul.smul ℤ X ZSMul.toSMul m v =
              @SMul.smul ℤ X ZSMul.toSMul m (X.ρ g v) := by rw [hv g]
          _ = X.ρ g (@SMul.smul ℤ X ZSMul.toSMul m v) := by
            exact (AddMonoidHom.map_zsmul (X.ρ g).toAddMonoidHom m v).symm }
  exact ConcreteCategory.ofHom (C := TopRep ℤ G) q

/-- Evaluation on an integer residue recovers the corresponding multiple
of the chosen invariant coefficient. -/
theorem trivialIntegralCoefficientLineHom_intCast
    (v : X) (hpv : p • v = 0) (hv : ∀ g : G, X.ρ g v = v) (m : ℤ) :
    trivialIntegralCoefficientLineHom G X p v hpv hv
      (ULift.up (m : ZMod p)) = m • v := by
  let a : ℤ →+ X :=
    { toFun := fun n => n • v
      map_zero' := zero_zsmul v
      map_add' := fun n k => add_zsmul v n k }
  have ha : a p = 0 := by
    let : Module ℤ X := X.hV2
    change (p : ℤ) • v = 0
    exact ((Int.cast_smul_eq_zsmul ℤ (p : ℤ) v).symm.trans
      (Nat.cast_smul_eq_nsmul ℤ p v)).trans hpv
  exact ZMod.lift_coe p ⟨a, ha⟩ m

/-- A nonzero invariant coefficient of prime order embeds the actual
trivial mod-p coefficient object. -/
theorem trivialIntegralCoefficientLineHom_injective [Fact p.Prime]
    (v : X) (hpv : p • v = 0) (hv : ∀ g : G, X.ρ g v = v) (hv0 : v ≠ 0) :
    Function.Injective (trivialIntegralCoefficientLineHom G X p v hpv hv) := by
  intro a b hab
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  apply ULift.ext
  change a = b
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective b
  have hmn : m • v = n • v :=
    (trivialIntegralCoefficientLineHom_intCast G X p v hpv hv m).symm.trans
      (hab.trans (trivialIntegralCoefficientLineHom_intCast G X p v hpv hv n))
  have hz : (m - n) • v = 0 := by
    rw [sub_smul, hmn, sub_self]
  have hd : (p : ℤ) ∣ m - n := by
    rw [← addOrderOf_eq_prime hpv hv0]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  apply sub_eq_zero.mp
  rw [← Int.cast_sub]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (m - n) p).mpr hd

end TopRep
