/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtin
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteNonabelianRestriction
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteTransfer
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiltered
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.CharacterConductor
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteAbelianQuotientKernels
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteGaloisArtin
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteReciprocityDiagram
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.LocalMultiplicativeCompletion
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.NormFiltration
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilGroup
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilReciprocityDegree
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilReciprocity
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilRestriction
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilNormNaturality
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilFiniteExtension
import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Infinite local class field theory

Public aggregate for the topological profinite completion, compatible finite
Artin maps, the absolute local Artin map, and the profinite local reciprocity
equivalence.
-/
