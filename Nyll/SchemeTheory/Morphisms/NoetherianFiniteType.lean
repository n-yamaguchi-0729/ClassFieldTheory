/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian sources of finite type morphisms -/

public section

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-compact, locally finite type morphism over a Noetherian scheme has Noetherian source. -/
theorem LocallyOfFiniteType.isNoetherian {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsNoetherian Y] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

end AlgebraicGeometry
