/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# MHD Equilibrium

Static MHD equilibrium: the force balance equation ∇p = J×B,
combined with Ampère's law ∇×B = μ₀J and ∇·B = 0.

Key consequences:
  - B · ∇p = 0 (B lies on pressure surfaces)
  - J · ∇p = 0 (J lies on pressure surfaces)
  - ∇p = (1/μ₀)(∇×B)×B (force balance in terms of B alone)
-/
import PlasmaEquations.SingleFluidMHD
import PlasmaEquations.CylindricalCoords

noncomputable section

open scoped BigOperators

namespace PlasmaEquations

open MaxwellWave

/-! ## Equilibrium structure -/

/-- Static MHD equilibrium.

In a time-independent equilibrium, the plasma is in force balance:
  ∇p = J×B
together with the magnetostatic equations ∇×B = μ₀J and ∇·B = 0. -/
structure MHDEquilibrium (c : MHDConstants) where
  /-- Equilibrium pressure p(x). -/
  p : ScalarField
  /-- Equilibrium magnetic field B(x). -/
  B : VectorField
  /-- Equilibrium current density J(x). -/
  J : VectorField
  /-- Force balance: (∇p)_j = (J×B)_j for each component. -/
  force_balance : ∀ x j,
    partialDeriv p j x = fieldCross J B x j
  /-- Ampère's law: (∇×B)_j = μ₀ J_j. -/
  ampere : ∀ x j, curl B x j = c.μ₀ * J x j
  /-- Solenoidal: ∇·B = 0. -/
  solenoidal : ∀ x, divergence B x = 0
  /-- B is C² smooth. -/
  hB_smooth : IsC2Vector B

namespace MHDEquilibrium

variable {c : MHDConstants} (eq : MHDEquilibrium c)

/-- B · ∇p = 0: the magnetic field is tangent to pressure surfaces.

Proof: B · ∇p = B · (J×B) = 0 by the vector identity a·(b×a) = 0. -/
theorem B_dot_grad_p_eq_zero (x : Vec3) :
    vec3Dot (eq.B x) (gradient eq.p x) = 0 := by
  have hgrad : gradient eq.p x = fun j => fieldCross eq.J eq.B x j := by
    funext j; exact eq.force_balance x j
  rw [hgrad]
  simp only [vec3Dot, dotProduct, fieldCross, vec3Cross, crossProduct]
  simp [Fin.sum_univ_three]
  ring

/-- J · ∇p = 0: the current density is tangent to pressure surfaces.

Proof: J · ∇p = J · (J×B) = 0 by the identity a·(a×b) = 0. -/
theorem J_dot_grad_p_eq_zero (x : Vec3) :
    vec3Dot (eq.J x) (gradient eq.p x) = 0 := by
  have hgrad : gradient eq.p x = fun j => fieldCross eq.J eq.B x j := by
    funext j
    exact eq.force_balance x j
  rw [hgrad]
  exact fieldDot_self_cross_eq_zero eq.J eq.B x

/-- Force balance in terms of B alone: ∇p = (1/μ₀)(∇×B)×B.

Substituting J = (1/μ₀)∇×B from Ampère's law into ∇p = J×B. -/
theorem force_balance_cross_form (x : Vec3) (j : Fin 3) :
    partialDeriv eq.p j x =
      fieldCross (fun y => fun i => (1 / c.μ₀) * curl eq.B y i) eq.B x j := by
  rw [eq.force_balance x j]
  simp only [fieldCross, vec3Cross, crossProduct]
  have hJ : ∀ i, eq.J x i = (1 / c.μ₀) * curl eq.B x i := by
    intro i
    have h := eq.ampere x i
    have hμ := c.μ₀_ne_zero
    field_simp; linarith
  fin_cases j <;> simp [Fin.isValue] <;> rw [hJ, hJ] <;> ring

/-- Magnetic pressure form of force balance:
    ∇p = (1/μ₀)((B·∇)B - ∇(B²/2)).
    This uses the vector identity (∇×B)×B = (B·∇)B - ∇(|B|²/2).
    (Requires the vector identity — left as sorry.) -/
theorem magnetic_pressure_form (x : Vec3) (j : Fin 3) :
    partialDeriv eq.p j x =
      (1 / c.μ₀) * (advectiveDerivVector eq.B eq.B x j -
        partialDeriv (fun y => (1/2) * vec3Dot (eq.B y) (eq.B y)) j x) := by
  sorry

end MHDEquilibrium

end PlasmaEquations
