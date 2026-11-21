/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-! # Exact reduction of an invariant lattice inclusion -/

@[expose] public section

noncomputable section

open Function

namespace LinearMap

/-- The scalar map whose kernel and cokernel are the torsion and power quotient. -/
abbrev nsmulLinear {R : Type*} [Ring R] (n : ℕ) (A : Type*)
    [AddCommGroup A] [Module R A] : A →ₗ[R] A :=
  n • (LinearMap.id : A →ₗ[R] A)

section ExactSequence

variable {R : Type*} [CommRing R]
variable {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

local notation "N[" n "," X "]" => nsmulLinear (R := R) n X
local notation "T[" n "," X "]" => LinearMap.ker (N[n,X])
local notation "Q[" n "," X "]" => X ⧸ LinearMap.range (N[n,X])

/-- An original linear map commutes with integral multiplication. -/
theorem comp_nsmulLinear (n : ℕ) (f : A →ₗ[R] B) :
    f.comp (N[n,A]) = (N[n,B]).comp f := by
  ext x
  exact map_nsmul f n x

/-- An equivariant lattice map induces a map on its power quotient. -/
def powerReductionMap (n : ℕ) (f : A →ₗ[R] B) : Q[n,A] →ₗ[R] Q[n,B] :=
  (LinearMap.range (N[n,A])).mapQ (LinearMap.range (N[n,B])) f (by
    rintro a ⟨x, rfl⟩
    exact ⟨f x, (LinearMap.congr_fun (comp_nsmulLinear n f) x).symm⟩)

theorem powerReductionMap_mkQ (n : ℕ) (f : A →ₗ[R] B) (x : A) :
    powerReductionMap n f ((LinearMap.range (N[n,A])).mkQ x) =
      (LinearMap.range (N[n,B])).mkQ (f x) := rfl

theorem powerReductionMap_comp (n : ℕ) (g : B →ₗ[R] C) (f : A →ₗ[R] B) :
    powerReductionMap n (g.comp f) = (powerReductionMap n g).comp (powerReductionMap n f) := by
  apply LinearMap.ext
  intro a
  obtain ⟨a, rfl⟩ := (LinearMap.range (N[n,A])).mkQ_surjective a
  simp only [powerReductionMap_mkQ, LinearMap.comp_apply]

theorem powerReductionMap_id (n : ℕ) :
    powerReductionMap n (LinearMap.id : A →ₗ[R] A) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  obtain ⟨a, rfl⟩ := (LinearMap.range (N[n,A])).mkQ_surjective a
  exact powerReductionMap_mkQ n _ a

theorem powerReductionMap_surjective (n : ℕ) (f : A →ₗ[R] B) (hf : Surjective f) :
    Surjective (powerReductionMap n f) := by
  intro y
  obtain ⟨b, rfl⟩ := (LinearMap.range (N[n,B])).mkQ_surjective y
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨(LinearMap.range (N[n,A])).mkQ a, powerReductionMap_mkQ n f a⟩

/-- An equivariant map restricts to the actual torsion submodules. -/
def powerTorsionMap (n : ℕ) (f : A →ₗ[R] B) : T[n,A] →ₗ[R] T[n,B] :=
  f.restrict (fun x hx => by
    change n • f x = 0
    change n • x = 0 at hx
    rw [← map_nsmul, hx, map_zero])

variable (n : ℕ) (i : A →ₗ[R] B) (q : B →ₗ[R] C)
  (hi : Injective i) (hq : Surjective q) (h : Exact i q)

/-- A torsion class in the quotient maps to the reduced multiple of any lift. -/
def powerReductionConnecting : T[n,C] →ₗ[R] Q[n,A] :=
  SnakeLemma.δ' (N[n,A]) (N[n,B]) (N[n,C]) i q h i q h
    (comp_nsmulLinear n i) (comp_nsmulLinear n q)
    (LinearMap.ker (N[n,C])).subtype (LinearMap.exact_subtype_ker_map (N[n,C]))
    (LinearMap.range (N[n,A])).mkQ (LinearMap.exact_map_mkQ_range (N[n,A])) hq hi

theorem powerReductionConnecting_apply (c : T[n,C]) (b : B) (a : A)
    (hb : q b = c.val) (ha : i a = n • b) :
    powerReductionConnecting n i q hi hq h c = (LinearMap.range (N[n,A])).mkQ a :=
  SnakeLemma.δ'_eq (N[n,A]) (N[n,B]) (N[n,C]) i q h i q h
    (comp_nsmulLinear n i) (comp_nsmulLinear n q)
    (LinearMap.ker (N[n,C])).subtype (LinearMap.exact_subtype_ker_map (N[n,C]))
    (LinearMap.range (N[n,A])).mkQ (LinearMap.exact_map_mkQ_range (N[n,A])) hq hi
    c b hb a ha

theorem powerReduction_exact_connecting :
    Exact (powerReductionConnecting n i q hi hq h) (powerReductionMap n i) :=
  SnakeLemma.exact_δ'_left (N[n,A]) (N[n,B]) (N[n,C]) i q h i q h
    (comp_nsmulLinear n i) (comp_nsmulLinear n q)
    (LinearMap.ker (N[n,C])).subtype (LinearMap.exact_subtype_ker_map (N[n,C]))
    (LinearMap.range (N[n,A])).mkQ (LinearMap.exact_map_mkQ_range (N[n,A]))
    (LinearMap.range (N[n,B])).mkQ (LinearMap.exact_map_mkQ_range (N[n,B])) hq hi
    (powerReductionMap n i) (by ext x; rfl) (LinearMap.range (N[n,A])).mkQ_surjective

theorem powerTorsion_exact_connecting :
    Exact (powerTorsionMap n q) (powerReductionConnecting n i q hi hq h) :=
  SnakeLemma.exact_δ'_right (N[n,A]) (N[n,B]) (N[n,C]) i q h i q h
    (comp_nsmulLinear n i) (comp_nsmulLinear n q)
    (LinearMap.ker (N[n,B])).subtype (LinearMap.exact_subtype_ker_map (N[n,B]))
    (LinearMap.ker (N[n,C])).subtype (LinearMap.exact_subtype_ker_map (N[n,C]))
    (LinearMap.range (N[n,A])).mkQ (LinearMap.exact_map_mkQ_range (N[n,A])) hq hi
    (powerTorsionMap n q) (by ext x; rfl) Subtype.val_injective

include hi h in
theorem powerTorsionMap_injective_of_source (hA : Injective (N[n,A])) :
    Injective (powerTorsionMap n q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  have hy₀ : q y.val = 0 := congrArg Subtype.val hy
  obtain ⟨x, hx⟩ := (h _).mp hy₀
  have hx₀ : n • x = 0 := by
    apply hi
    rw [map_nsmul, hx, map_zero]
    exact y.property
  have hx' : x = 0 := hA (hx₀.trans (map_zero (N[n,A])).symm)
  apply Subtype.ext
  exact hx.symm.trans ((congrArg i hx').trans (map_zero i))

include hq h in
/-- Reduction is exact on the right, using the original quotient map. -/
theorem powerReduction_exact : Exact (powerReductionMap n i) (powerReductionMap n q) := by
  intro y
  obtain ⟨b, rfl⟩ := (LinearMap.range (N[n,B])).mkQ_surjective y
  rw [powerReductionMap_mkQ]
  constructor
  · intro hb
    obtain ⟨c, hc⟩ := (Submodule.Quotient.mk_eq_zero _).mp hb
    obtain ⟨d, rfl⟩ := hq c
    have hbd : q (b - n • d) = 0 := by
      rw [map_sub, map_nsmul]
      exact sub_eq_zero.mpr hc.symm
    obtain ⟨a, ha⟩ := (h _).mp hbd
    refine ⟨(LinearMap.range (N[n,A])).mkQ a, ?_⟩
    rw [powerReductionMap_mkQ, ha, map_sub]
    have hd : (LinearMap.range (N[n,B])).mkQ (n • d) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨d, rfl⟩
    rw [hd, sub_zero]
  · rintro ⟨a, ha⟩
    obtain ⟨c, rfl⟩ := (LinearMap.range (N[n,A])).mkQ_surjective a
    rw [powerReductionMap_mkQ] at ha
    have hh := congrArg (powerReductionMap n q) ha
    rw [powerReductionMap_mkQ, powerReductionMap_mkQ, h.apply_apply_eq_zero, map_zero] at hh
    exact hh.symm

/-- If the middle lattice has no torsion, the connecting map is injective. -/
theorem powerReductionConnecting_injective (hB : Injective (N[n,B])) :
    Injective (powerReductionConnecting n i q hi hq h) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  obtain ⟨b, hb⟩ := hq c.val
  have hb' : q (n • b) = 0 := by
    rw [map_nsmul, hb]
    exact c.property
  obtain ⟨a, ha⟩ := (h _).mp hb'
  rw [powerReductionConnecting_apply n i q hi hq h c b a hb ha] at hc
  obtain ⟨a', ha'⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
  have hsub : n • i a' = n • b := by
    rw [← map_nsmul, show n • a' = a from ha', ha]
  have hib : i a' = b := hB hsub
  apply Subtype.ext
  change c.val = 0
  exact hb.symm.trans (hib ▸ h.apply_apply_eq_zero a')

include hi hq h in
/-- If the quotient has no corresponding torsion, lattice reduction stays injective. -/
theorem powerReductionMap_injective_of_quotient (hC : Injective (N[n,C])) :
    Injective (powerReductionMap n i) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c, rfl⟩ := (powerReduction_exact_connecting n i q hi hq h _).mp hx
  have hc : c = 0 := by
    apply Subtype.ext
    apply hC
    exact c.property.trans (map_zero (N[n,C])).symm
  rw [hc, map_zero]

end ExactSequence

section Values

universe u v w

variable {R : Type v} [CommRing R] {A B C : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

local notation "N[" n "," X "]" => nsmulLinear (R := R) n X
local notation "T[" n "," X "]" => LinearMap.ker (N[n,X])
local notation "Q[" n "," X "]" => X ⧸ LinearMap.range (N[n,X])
local notation "Mod[" X "]" => ModuleCat.of R X

/-- A finite quotient changes reduction by exactly the torsion of the
middle term, measured by any invariant additive on finite exact sequences. -/
theorem powerReduction_value_of_finite_quotient {W : Type w} [AddCommGroup W]
    (value : ∀ X : ModuleCat.{u} R, [Finite X] → W)
    (additive : ∀ (X Y Z : ModuleCat.{u} R) [Finite X] [Finite Y] [Finite Z]
      (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z), Injective f → Surjective g → Exact f g →
      value Y = value X + value Z)
    (n : ℕ) (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Injective i) (hq : Surjective q) (h : Exact i q)
    (hA : Injective (N[n,A])) [Finite C] [Finite (T[n,B])] [Finite (Q[n,A])] [Finite (Q[n,B])] :
    value (Mod[Q[n,B]]) = value (Mod[Q[n,A]]) + value (Mod[T[n,B]]) := by
  let Ctor := T[n,C]
  let nC := N[n,C]
  let imageN := LinearMap.range nC
  let δ := powerReductionConnecting n i q hi hq h
  let D := LinearMap.range δ
  let i' := powerReductionMap n i
  let q' := powerReductionMap n q
  let I := LinearMap.range i'
  let : Finite (Q[n,C]) := Finite.of_surjective imageN.mkQ imageN.mkQ_surjective
  have hker : Exact (LinearMap.ker nC).subtype nC.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hcok : Exact imageN.subtype imageN.mkQ := by
    apply LinearMap.exact_iff.mpr
    rw [Submodule.ker_mkQ, Submodule.range_subtype]
  have hC₁ : value (Mod[C]) = value (Mod[Ctor]) + value (Mod[imageN]) :=
    additive _ _ _ _ _ Subtype.val_injective nC.surjective_rangeRestrict hker
  have hC₂ : value (Mod[C]) = value (Mod[imageN]) + value (Mod[Q[n,C]]) :=
    additive _ _ _ _ _ Subtype.val_injective imageN.mkQ_surjective hcok
  have hC : value (Mod[Ctor]) = value (Mod[Q[n,C]]) :=
    add_right_cancel (hC₁.symm.trans (hC₂.trans (add_comm _ _)))
  have et : Exact (powerTorsionMap n q) δ.rangeRestrict :=
    LinearMap.exact_iff.mpr (δ.ker_rangeRestrict.trans
      (powerTorsion_exact_connecting n i q hi hq h).linearMap_ker_eq)
  have e₁ : Exact D.subtype i'.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    rw [i'.ker_rangeRestrict, Submodule.range_subtype]
    exact (powerReduction_exact_connecting n i q hi hq h).linearMap_ker_eq
  have e₂ : Exact I.subtype q' := by
    apply LinearMap.exact_iff.mpr
    rw [Submodule.range_subtype]
    exact (powerReduction_exact n i q hq h).linearMap_ker_eq
  have ht : value (Mod[Ctor]) = value (Mod[T[n,B]]) + value (Mod[D]) :=
    additive _ _ _ _ _ (powerTorsionMap_injective_of_source n i q hi h hA)
      δ.surjective_rangeRestrict et
  have hA' : value (Mod[Q[n,A]]) = value (Mod[D]) + value (Mod[I]) :=
    additive _ _ _ _ _ Subtype.val_injective
      i'.surjective_rangeRestrict e₁
  have hB' : value (Mod[Q[n,B]]) = value (Mod[I]) + value (Mod[Q[n,C]]) :=
    additive _ _ _ _ _ Subtype.val_injective (powerReductionMap_surjective n q hq) e₂
  rw [hA', hB', ← hC, ht]
  abel

end Values

end LinearMap

namespace Rep

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- Reduce an actual representation by the image of its integral power map. -/
def powerReduction (A : Rep.{v} R G) (n : ℕ) : Rep.{v} R G :=
  Rep.of
    { toFun := fun g => LinearMap.powerReductionMap n (A.ρ g)
      map_one' := by
        rw [map_one]
        exact LinearMap.powerReductionMap_id n
      map_mul' := fun g h => by
        rw [map_mul]
        exact LinearMap.powerReductionMap_comp n (A.ρ g) (A.ρ h) }

/-- The original intertwining map induces the same map on power quotients. -/
def powerReductionHom {A B : Rep.{v} R G} (n : ℕ) (f : A ⟶ B) :
    powerReduction A n ⟶ powerReduction B n :=
  Rep.ofHom
    { toLinearMap := LinearMap.powerReductionMap n f.hom.toLinearMap
      isIntertwining' g := by
        change (LinearMap.powerReductionMap n f.hom.toLinearMap).comp
            (LinearMap.powerReductionMap n (A.ρ g)) =
          (LinearMap.powerReductionMap n (B.ρ g)).comp
            (LinearMap.powerReductionMap n f.hom.toLinearMap)
        rw [← LinearMap.powerReductionMap_comp, ← LinearMap.powerReductionMap_comp,
          f.hom.isIntertwining' g] }

end Rep
