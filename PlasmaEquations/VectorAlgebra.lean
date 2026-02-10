/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Vector Algebra for Plasma Physics

Cross product, dot product, and field-level algebra on ℝ³ vector fields,
built atop Mathlib's `crossProduct` and `dotProduct`.
-/
import MaxwellWave.VectorCalculus
import Mathlib.LinearAlgebra.CrossProduct

noncomputable section

open scoped BigOperators

namespace PlasmaEquations

open MaxwellWave

/-! ## Pointwise vector operations on fields -/

def vec3Cross (a b : Vec3) : Vec3 := crossProduct a b

def vec3Dot (a b : Vec3) : ℝ := dotProduct a b

def fieldCross (F G : VectorField) (x : Vec3) : Vec3 :=
  vec3Cross (F x) (G x)

def fieldDot (F G : VectorField) (x : Vec3) : ℝ :=
  vec3Dot (F x) (G x)

def scalarMul (c : ScalarField) (F : VectorField) (x : Vec3) : Vec3 :=
  fun i => c x * F x i

def fieldAdd (F G : VectorField) (x : Vec3) : Vec3 :=
  fun i => F x i + G x i

def fieldSub (F G : VectorField) (x : Vec3) : Vec3 :=
  fun i => F x i - G x i

def fieldNeg (F : VectorField) (x : Vec3) : Vec3 :=
  fun i => -(F x i)

/-! ## Time-dependent variants -/

def tdFieldCross (F G : TDVectorField) (t : ℝ) (x : Vec3) : Vec3 :=
  vec3Cross (F t x) (G t x)

def tdScalarMul (c : TDScalarField) (F : TDVectorField) (t : ℝ) (x : Vec3) : Vec3 :=
  fun i => c t x * F t x i

def tdFieldAdd (F G : TDVectorField) (t : ℝ) (x : Vec3) : Vec3 :=
  fun i => F t x i + G t x i

/-! ## Cross product identities -/

/-- Cross product is anti-commutative: a × b = -(b × a). -/
lemma cross_anticomm (a b : Vec3) :
    vec3Cross a b = fieldNeg (fun _ => vec3Cross b a) (0 : Vec3) := by
  funext i
  simp only [vec3Cross, fieldNeg, crossProduct]
  fin_cases i <;> simp <;> ring

/-- Anti-commutativity at the field level. -/
lemma cross_anticomm_field (F G : VectorField) (x : Vec3) :
    fieldCross F G x = fieldNeg (fieldCross G F) x := by
  funext i
  simp only [fieldCross, fieldNeg, vec3Cross, crossProduct]
  fin_cases i <;> simp <;> ring

/-- v · (v × w) = 0 — a vector is perpendicular to its own cross product. -/
lemma dot_self_cross_eq_zero (a b : Vec3) :
    vec3Dot a (vec3Cross a b) = 0 := by
  simp only [vec3Dot, vec3Cross, dotProduct, crossProduct]
  simp [Fin.sum_univ_three]
  ring

/-- (v × w) · w = 0 — the cross product is perpendicular to its second argument. -/
lemma dot_cross_self_eq_zero (a b : Vec3) :
    vec3Dot (vec3Cross a b) b = 0 := by
  simp only [vec3Dot, vec3Cross, dotProduct, crossProduct]
  simp [Fin.sum_univ_three]
  ring

/-- Field-level: F(x) · (F(x) × G(x)) = 0. -/
lemma fieldDot_self_cross_eq_zero (F G : VectorField) (x : Vec3) :
    fieldDot F (fieldCross F G) x = 0 :=
  dot_self_cross_eq_zero (F x) (G x)

/-- Field-level: (F(x) × G(x)) · G(x) = 0. -/
lemma fieldDot_cross_self_eq_zero (F G : VectorField) (x : Vec3) :
    fieldDot (fieldCross F G) G x = 0 :=
  dot_cross_self_eq_zero (F x) (G x)

end PlasmaEquations
