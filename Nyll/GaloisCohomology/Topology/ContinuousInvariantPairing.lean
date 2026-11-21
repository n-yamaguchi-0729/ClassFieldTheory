/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives

/-! # Cohomology maps obtained by substituting an invariant coefficient -/

@[expose] public section

noncomputable section

open CategoryTheory TopRep

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : TopRep.{u} ℤ G}
    (p : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (hp : Continuous (fun t : A × B => p t.1 t.2))
    (he : ∀ (g : G) (a : A) (b : B), p (A.ρ g a) (B.ρ g b) = C.ρ g (p a b))

/-- Substituting an invariant right coefficient in an equivariant pairing
gives a morphism of the original representations. -/
def rightInvariantCoefficientMap (b : B.invariants) : A ⟶ C := by
  let add : A →+ C :=
    { toFun := fun a => p a b.val
      map_zero' := congrArg (fun f : B →ₗ[ℤ] C => f b.val) (map_zero p)
      map_add' := fun a a' => congrArg (fun f : B →ₗ[ℤ] C => f b.val) (map_add p a a') }
  let : Module ℤ A := A.hV2
  let : Module ℤ C := C.hV2
  refine TopRep.ofHom { toLinearMap := ?_, cont := ?_, isIntertwining' := ?_ }
  · exact
      { toFun := add
        map_add' := add.map_add
        map_smul' := fun z a => (congrArg add (int_smul_eq_zsmul A.hV2 z a)).trans
          ((map_zsmul add z a).trans (int_smul_eq_zsmul C.hV2 z (add a)).symm) }
  · change Continuous (fun a : A => p a b.val)
    exact hp.comp (continuous_id.prodMk continuous_const)
  · intro g
    apply ContinuousLinearMap.ext
    intro a
    change p (A.ρ g a) b.val = C.ρ g (p a b.val)
    exact (congrArg (p (A.ρ g a)) (b.property g).symm).trans (he g a b.val)

/-- Right multiplication by an invariant on degree-two continuous cohomology. -/
def degreeTwoInvariantMap (b : B.invariants) :
    continuousCohomology 2 A →+ continuousCohomology 2 C :=
  (map (ContinuousMonoidHom.id G) (rightInvariantCoefficientMap p hp he b) 2).hom.toLinearMap
    |>.toAddMonoidHom

theorem degreeTwoInvariantMap_π (b : B.invariants) (z : cocycles A 2) :
    degreeTwoInvariantMap p hp he b (π A 2 z) =
      π C 2 (cocyclesMap (ContinuousMonoidHom.id G)
        (rightInvariantCoefficientMap p hp he b) 2 z) := by
  let i := ContinuousMonoidHom.id G
  let f : TopRep.res i.toMonoidHom A ⟶ C := rightInvariantCoefficientMap p hp he b
  exact ConcreteCategory.congr_hom (π_map (X := A) (Y := C) i f 2) z

end ContinuousCohomology
