import AbstractClassFieldTheory.Degree
import AbstractClassFieldTheory.Reciprocity

/-!
# Abstract class field theory

Public root for abstract degree data, class formations, reciprocity, and the construction and
naturality of Artin maps. The public declarations live in the `ClassFormation` namespace. This
library is independent of local class field theory.

The representation-free degree, field, extension, and topological-generation
APIs are universe-polymorphic.  The boundary that uses Mathlib's `Rep ℤ G` is
necessarily universe zero because `Rep` currently places its coefficient ring
and acting group in the same universe; the affected source sections state that
constraint explicitly.
-/
