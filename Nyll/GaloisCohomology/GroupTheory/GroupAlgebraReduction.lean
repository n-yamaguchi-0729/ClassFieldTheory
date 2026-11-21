/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-! # Reduction of the scalar ring on annihilated group-algebra modules -/

@[expose] public section

open scoped Ring

noncomputable section

namespace MonoidAlgebra

variable (G : Type*) [Group G] (n : ℕ)

/-- The original integral group algebra, reduced coefficientwise. -/
def intReduction : ℤ[G] →+* (ZMod n)[G] := mapRingHom G (Int.castRingHom (ZMod n))

theorem intReduction_surjective : Function.Surjective (intReduction G n) :=
  MonoidAlgebra.map_surjective (Int.castRingHom (ZMod n)).toAddMonoidHom ZMod.intCast_surjective

/-- A change between residue rings commutes with integral reduction. -/
theorem mapRingHom_castHom_intReduction {d : ℕ} (h : d ∣ n) (r : ℤ[G]) :
    mapRingHom G (ZMod.castHom h (ZMod d)) (intReduction G n r) = intReduction G d r := by
  ext g
  simp only [intReduction, coeff_mapRingHom, Int.coe_castRingHom, map_intCast]

variable [Finite G]

private theorem exists_nsmul_of_intReduction_eq_zero (x : ℤ[G]) (hx : intReduction G n x = 0) :
    ∃ y : ℤ[G], n • y = x := by
  have hc (g : G) : ∃ a : ℤ, n • a = x.coeff g := by
    have h := congrArg (fun z : (ZMod n)[G] => z.coeff g) hx
    rw [intReduction, coeff_mapRingHom] at h
    have hz : (x.coeff g : ZMod n) = 0 := h
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    refine ⟨a, (natCast_zsmul a n).symm.trans ((Int.zsmul_eq_mul _ _).trans ha.symm)⟩
  choose a ha using hc
  let y : ℤ[G] := ofCoeff (Finsupp.ofSupportFinite a (Set.toFinite _))
  refine ⟨y, ?_⟩
  ext g
  let ev : ℤ[G] →+ ℤ :=
    { toFun := fun z => z.coeff g
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (n • y) = ev x
  rw [map_nsmul]
  exact ha g

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℤ[G] A] [Module ℤ[G] B]

/-- The kernel of integral coefficient reduction acts by zero. -/
theorem intReduction_ker_le_smulEnd (hA : ∀ a : A, n • a = 0) :
    RingHom.ker (intReduction G n) ≤ RingHom.ker (Module.toModuleEnd ℤ A (S := ℤ[G])) := by
  intro x hx
  obtain ⟨r, rfl⟩ := exists_nsmul_of_intReduction_eq_zero G n x (RingHom.mem_ker.mp hx)
  refine RingHom.mem_ker.mpr ?_
  rw [map_nsmul]
  apply LinearMap.ext
  exact fun a => hA (r • a)

/-- The actual module on the same carrier, defined by descending its scalar action. -/
@[instance_reducible]
def modModule (hA : ∀ a : A, n • a = 0) : Module (ZMod n)[G] A :=
  Module.compHom A ((intReduction G n).liftOfSurjective (intReduction_surjective G n)
    ⟨Module.toModuleEnd ℤ A, intReduction_ker_le_smulEnd G n hA⟩)

theorem modModule_smul (hA : ∀ a : A, n • a = 0) (r : ℤ[G]) (a : A) :
    letI := modModule G n hA
    intReduction G n r • a = r • a := by
  change (((intReduction G n).liftOfSurjective (intReduction_surjective G n)
    ⟨Module.toModuleEnd ℤ A, intReduction_ker_le_smulEnd G n hA⟩)
      (intReduction G n r)) a = r • a
  exact DFunLike.congr_fun ((intReduction G n).liftOfSurjective_comp_apply
    (intReduction_surjective G n)
      ⟨Module.toModuleEnd ℤ A, intReduction_ker_le_smulEnd G n hA⟩ r) a

/-- The descended scalar actions of two bounds agree by coefficient reduction. -/
theorem modModule_smul_change {d : ℕ} (h : d ∣ n) (hA : ∀ a : A, n • a = 0)
    (hA' : ∀ a : A, d • a = 0) (r : (ZMod n)[G]) (a : A) :
    letI := modModule G n hA
    letI := modModule G d hA'
    mapRingHom G (ZMod.castHom h (ZMod d)) r • a = r • a := by
  let := modModule G n hA
  let := modModule G d hA'
  obtain ⟨t, rfl⟩ := intReduction_surjective G n r
  rw [mapRingHom_castHom_intReduction, modModule_smul G d hA', modModule_smul G n hA]

/-- An original group-algebra map remains linear after descending the
coefficient rings of the same source and target. -/
def modModuleMap (hA : ∀ a : A, n • a = 0) (hB : ∀ b : B, n • b = 0) (f : A →ₗ[ℤ[G]] B) :
    letI := modModule G n hA
    letI := modModule G n hB
    A →ₗ[(ZMod n)[G]] B := by
  letI := modModule G n hA
  letI := modModule G n hB
  refine { toFun := f, map_add' := map_add f, map_smul' := ?_ }
  intro z a
  obtain ⟨r, rfl⟩ := intReduction_surjective G n z
  change f (intReduction G n r • a) = intReduction G n r • f a
  rw [modModule_smul G n hA, modModule_smul G n hB]
  exact map_smul f r a

/-- Descending the scalar action leaves exactly the same linear maps. -/
def modModuleHomEquiv (hA : ∀ a : A, n • a = 0) (hB : ∀ b : B, n • b = 0) :
    letI := modModule G n hA
    letI := modModule G n hB
    (A →ₗ[ℤ[G]] B) ≃ (A →ₗ[(ZMod n)[G]] B) := by
  letI := modModule G n hA
  letI := modModule G n hB
  exact
    { toFun := modModuleMap G n hA hB
      invFun := fun f =>
        { toFun := f
          map_add' := map_add f
          map_smul' := fun r a => by
            change f (r • a) = r • f a
            rw [← modModule_smul G n hA r a, ← modModule_smul G n hB r (f a)]
            exact map_smul f (intReduction G n r) a }
      left_inv := fun _ => LinearMap.ext fun _ => rfl
      right_inv := fun _ => LinearMap.ext fun _ => rfl }

end MonoidAlgebra
