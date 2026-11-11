/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseSemilinearNaturality
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension

/-!
# The named local Hilbert pairing and the specified Artin action

The named pairing uses the specified general local Artin map.  Its action on
every radical in the same simple extension is given explicitly; the existence
statement is a consequence of that value identity.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The specified general Artin map acts on every root in the actual simple
Kummer extension by the named Hilbert value. The Artin input is the first
pairing argument; changing the root does not change this value. -/
theorem localHilbertPairing_artin_action
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
    let : FiniteDimensional K E :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
    let : IsAbelianGalois K E :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
    ∀ (β : Eˣ), β ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom a →
      LocalClassFieldTheory.Universe.abelianLocalArtinMap K E b (β : E) =
        algebraMap K E
          ((localHilbertPairing K n hnK hmu
            (powerClass K n b) (powerClass K n a)).1 : K) * (β : E) := by
  intro E sharedFinite sharedGalois β hβ
  let σ := LocalClassFieldTheory.Universe.abelianLocalArtinMap K E b
  have hroot := localHilbertPairing_artin_rootQuotient_of_same_pow
    K n hnK hmu a b β hβ
  change Units.map (algebraMap K E).toMonoidHom
      (localHilbertPairing K n hnK hmu
        (powerClass K n b) (powerClass K n a)).1 =
    KummerTheory.rootQuotient (K := K) (L := E) β σ at hroot
  have hact : Units.map σ.toMonoidHom β =
      Units.map (algebraMap K E).toMonoidHom
        (localHilbertPairing K n hnK hmu
          (powerClass K n b) (powerClass K n a)).1 * β := by
    rw [hroot]
    change Units.map σ.toMonoidHom β = (Units.map σ.toMonoidHom β / β) * β
    rw [div_mul_cancel]
  exact congrArg Units.val hact

/-- Transport the radical and the actual Artin action along a specified
algebra equivalence, including when its target has a different universe. -/
theorem localHilbertPairing_artin_action_of_algEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ)
    (F : Type v) [Field F] [Algebra K F]
    [FiniteDimensional K F] [IsAbelianGalois K F] :
    let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
    ∀ (e : E ≃ₐ[K] F) (β : Eˣ),
      β ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom a →
      LocalClassFieldTheory.Universe.abelianLocalArtinMap K F b (e (β : E)) =
        algebraMap K F
          ((localHilbertPairing K n hnK hmu
            (powerClass K n b) (powerClass K n a)).1 : K) * e (β : E) := by
  intro E e β hβ
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  have hnat := DFunLike.congr_fun
    (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_autCongr K E F e) b
  have heval := congrArg (fun σ : Gal(F/K) => σ (e (β : E))) hnat
  change e (LocalClassFieldTheory.Universe.abelianLocalArtinMap K E b
      (e.symm (e (β : E)))) =
    LocalClassFieldTheory.Universe.abelianLocalArtinMap K F b (e (β : E)) at heval
  rw [e.symm_apply_apply] at heval
  rw [← heval, localHilbertPairing_artin_action K n hnK hmu a b β hβ,
    map_mul, e.commutes]

/-- A compatible equivalence of the base fields and their actual simple
Kummer extensions transports the Hilbert value through the roots-of-unity
map. The proof compares the same Artin actions on the transported radical. -/
theorem localHilbertPairing_value_semilinear
    (K : Type u) (K' : Type v) [Field K] [Field K']
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
    (eK : K ≃+* K')
    (hExt : LocalClassFieldTheory.SemilinearValuationCompatible K K' eK)
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hnK' : ((n : ℕ) : K') ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmu' : (primitiveRoots (n : ℕ) K').Nonempty) (a b : Kˣ)
    (eL : KummerTheory.chosenSimpleKummerExtension K n hnK a ≃+*
      KummerTheory.chosenSimpleKummerExtension K' n hnK'
        (Units.map eK.toMonoidHom a))
    (hcomm : ∀ x : K, eL (algebraMap K _ x) = algebraMap K' _ (eK x)) :
    rootsOfUnityEquivOfRingEquiv eK n hmu
      (localHilbertPairing K n hnK hmu (powerClass K n b) (powerClass K n a)) =
    localHilbertPairing K' n hnK' hmu'
      (powerClass K' n (Units.map eK.toMonoidHom b))
      (powerClass K' n (Units.map eK.toMonoidHom a)) := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let a' := Units.map eK.toMonoidHom a
  let b' := Units.map eK.toMonoidHom b
  let E' := KummerTheory.chosenSimpleKummerExtension K' n hnK' a'
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  let : FiniteDimensional K' E' :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K' n hnK' a'
  let : IsAbelianGalois K' E' :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K' n hnK' hmu' a'
  let β : Eˣ := KummerTheory.chosenSimpleKummerRootUnit K n hnK a
  let β' : E'ˣ := Units.map eL.toMonoidHom β
  have hβ := KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK a
  have hβ' : β' ^ (n : ℕ) = Units.map (algebraMap K' E').toMonoidHom a' := by
    change (Units.map eL.toMonoidHom β) ^ (n : ℕ) = _
    rw [← map_pow, hβ]
    apply Units.ext
    exact hcomm (a : K)
  have hsource := congrArg eL (localHilbertPairing_artin_action K n hnK hmu a b β hβ)
  have htarget := localHilbertPairing_artin_action K' n hnK' hmu' a' b' β' hβ'
  have hnat := LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_semilinear_action
    K K' E E' eK eL hcomm hExt b (β : E)
  change eL (LocalClassFieldTheory.Universe.abelianLocalArtinMap K E b (β : E)) =
    LocalClassFieldTheory.Universe.abelianLocalArtinMap K' E' b' (β' : E') at hnat
  rw [hnat, htarget, map_mul, hcomm] at hsource
  have hvalue := mul_right_cancel₀ (show eL (β : E) ≠ 0 from
    (map_ne_zero eL).2 β.ne_zero) hsource
  apply Subtype.ext
  apply Units.ext
  change eK ((localHilbertPairing K n hnK hmu
      (powerClass K n b) (powerClass K n a)).1 : K) =
    ((localHilbertPairing K' n hnK' hmu'
      (powerClass K' n b') (powerClass K' n a')).1 : K')
  exact (algebraMap K' E').injective hvalue.symm

/-- In the radical-first convention the multiplier is the inverse Hilbert
value. This follows from the actual Artin-first action, with no sign change
to the reciprocity map. -/
theorem localHilbertPairing_artin_action_radical_first
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
    let : FiniteDimensional K E :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
    let : IsAbelianGalois K E :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
    ∀ (β : Eˣ), β ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom a →
      LocalClassFieldTheory.Universe.abelianLocalArtinMap K E b (β : E) =
        algebraMap K E
          (((localHilbertPairing K n hnK hmu
            (powerClass K n a) (powerClass K n b))⁻¹).1 : K) * (β : E) := by
  intro E sharedFinite sharedGalois β hβ
  have h := localHilbertPairing_artin_action K n hnK hmu a b β hβ
  rw [(localHilbertPairing_isLocalHilbertPairing K n hnK hmu).2.1] at h
  exact h

/-- One local Hilbert pairing is compatible, at the level of values, with
continuous local Artin maps on its simple Kummer extensions. The first
pairing argument in the displayed action is the Artin input; the second
determines the radical. Thus the symbol with the radical first is the
inverse of the displayed Artin action ratio, by skew-symmetry. This is the
geometric local convention used in the local--global comparison. -/
theorem exists_localHilbertPairing_artinNormalization
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ B : HilbertPairing K n,
      HilbertPairing.IsLocalHilbertPairing B ∧
      ∀ a : Kˣ, ∃ β : SeparableClosure K,
        β ^ (n : ℕ) = algebraMap K (SeparableClosure K) (a : K) ∧
        let E := IntermediateField.adjoin K {β}
        ∃ artin : Kˣ →ₜ* (E ≃ₐ[K] E),
          Function.Surjective artin ∧
          ∀ b : Kˣ,
            artin b
                (⟨β, IntermediateField.subset_adjoin K {β}
                  (Set.mem_singleton β)⟩ : E) =
              algebraMap K E
                  ((B (powerClass K n b) (powerClass K n a)).1 : K) *
                (⟨β, IntermediateField.subset_adjoin K {β}
                  (Set.mem_singleton β)⟩ : E) := by
  let B : HilbertPairing K n := localHilbertPairing K n hnK hmu
  refine ⟨B, localHilbertPairing_isLocalHilbertPairing K n hnK hmu, ?_⟩
  intro a
  let β : SeparableClosure K := KummerTheory.chosenSimpleKummerRoot K n hnK a
  have hβ : β ^ (n : ℕ) = algebraMap K (SeparableClosure K) (a : K) :=
    KummerTheory.chosenSimpleKummerRoot_pow K n hnK a
  refine ⟨β, hβ, ?_⟩
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  let artin : Kˣ →ₜ* (E ≃ₐ[K] E) :=
    LocalClassFieldTheory.Universe.abelianLocalArtinMap K E
  refine ⟨artin,
    LocalClassFieldTheory.Universe.abelianLocalArtinMap_surjective K E, ?_⟩
  intro b
  exact localHilbertPairing_artin_action K n hnK hmu a b
    (KummerTheory.chosenSimpleKummerRootUnit K n hnK a)
    (KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK a)

end ClassFieldTheory
