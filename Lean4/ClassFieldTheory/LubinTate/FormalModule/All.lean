import ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
import ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
import ClassFieldTheory.LubinTate.FormalModule.Intertwiner
import ClassFieldTheory.LubinTate.FormalModule.LinearTerm
import ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
import ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
import ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
import ClassFieldTheory.LubinTate.FormalModule.Reduction
import ClassFieldTheory.LubinTate.FormalModule.Series
import ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
import ClassFieldTheory.LubinTate.FormalModule.StandardSeries

set_option autoImplicit false

/-!
# Lubin--Tate formal modules

Public aggregate for the formal-series constructions used by Lubin--Tate
theory: composition, linear terms, intertwiners, coefficient equations,
reduction, the standard Lubin--Tate series, and the coefficientwise recursive
existence-and-uniqueness construction, including the resulting standard
commutative formal group and its coefficient-ring endomorphisms.
-/
