/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Ideal MHD Equations

The ideal magnetohydrodynamics (MHD) system treats a plasma as a single
conducting fluid. It is obtained from the two-fluid equations by taking
mass-weighted averages and assuming:
  - Quasi-neutrality (n_i ≈ n_e)
  - Small electron inertia (m_e → 0)
  - Ideal Ohm's law: E + v × B = 0

The resulting system couples fluid dynamics with Maxwell's equations.
-/
import PlasmaEquations.FluidOperators
import PlasmaEquations.LorentzForce

noncomputable section

open scoped BigOperators

namespace PlasmaEquations

open MaxwellWave

/-! ## MHD Constants -/

/-- Physical constants appearing in the MHD equations. -/
structure MHDConstants where
  /-- Vacuum permeability μ₀ (H/m). -/
  μ₀ : ℝ
  /-- Adiabatic index γ (ratio of specific heats). -/
  γ : ℝ
  /-- μ₀ is positive. -/
  hμ₀ : 0 < μ₀
  /-- γ > 1 for a physical gas. -/
  hγ : 1 < γ

namespace MHDConstants
variable (c : MHDConstants)

lemma μ₀_ne_zero : c.μ₀ ≠ 0 := ne_of_gt c.hμ₀
lemma μ₀_pos : 0 < c.μ₀ := c.hμ₀
lemma γ_pos : 0 < c.γ := lt_trans one_pos c.hγ

end MHDConstants

/-! ## Ideal MHD System -/

/-- The ideal MHD system.

Fields: mass density `ρ`, velocity `v`, pressure `p`, magnetic field `B`,
current density `J`. The six equations are:

1. **Mass conservation**: ∂ρ/∂t + ∇·(ρv) = 0
2. **Momentum**: ρ(Dv/Dt)_j = (J×B)_j - ∂p/∂x_j
3. **Energy (adiabatic)**: ∂p/∂t + v·∇p + γp(∇·v) = 0
4. **Induction**: ∂B/∂t = ∇×(v×B)
5. **Solenoidal**: ∇·B = 0
6. **Ampère (MHD limit)**: ∇×B = μ₀J -/
structure IdealMHD (c : MHDConstants) where
  /-- Mass density ρ(t, x). -/
  ρ : TDScalarField
  /-- Fluid velocity v(t, x). -/
  v : TDVectorField
  /-- Scalar pressure p(t, x). -/
  p : TDScalarField
  /-- Magnetic field B(t, x). -/
  B : TDVectorField
  /-- Current density J(t, x). -/
  J : TDVectorField
  /-- Mass conservation: ∂ρ/∂t + ∇·(ρv) = 0. -/
  mass_conservation : ∀ t x,
    timeDeriv ρ t x + divergence (fun y => fun i => ρ t y * v t y i) x = 0
  /-- Momentum equation: ρ (Dv/Dt)_j = (J×B)_j - ∂p/∂x_j. -/
  momentum : ∀ t x j,
    ρ t x * materialDerivVector v v t x j =
      fieldCross (J t) (B t) x j - partialDeriv (p t) j x
  /-- Adiabatic energy equation: ∂p/∂t + v·∇p + γp∇·v = 0. -/
  energy : ∀ t x,
    timeDeriv p t x +
      advectiveDerivScalar (v t) (p t) x +
      c.γ * p t x * divergence (v t) x = 0
  /-- Induction equation: (∂B/∂t)_j = (∇×(v×B))_j. -/
  induction_eq : ∀ t x j,
    timeDerivComp B j t x = curl (fun y => vec3Cross (v t y) (B t y)) x j
  /-- Solenoidal constraint: ∇·B = 0. -/
  solenoidal : ∀ t x, divergence (B t) x = 0
  /-- Ampère's law (MHD limit, no displacement current): ∇×B = μ₀J. -/
  ampere : ∀ t x j, curl (B t) x j = c.μ₀ * J t x j
  /-- B is spatially smooth. -/
  hB_smooth : ∀ t, IsC2Vector (B t)

namespace IdealMHD

variable {c : MHDConstants} (sys : IdealMHD c)

/-- The induction equation follows from Faraday's law + ideal Ohm's law.
    If ∂B/∂t = -∇×E and E = -v×B, then ∂B/∂t = ∇×(v×B). -/
theorem ideal_induction_from_faraday_ohm
    (faraday : ∀ t x j, timeDerivComp sys.B j t x = -(curl (fun y => -(vec3Cross (sys.v t y) (sys.B t y))) x j))
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    timeDerivComp sys.B j t x = curl (fun y => vec3Cross (sys.v t y) (sys.B t y)) x j := by
  rw [faraday t x j]
  have h : curl (fun y => -(vec3Cross (sys.v t y) (sys.B t y))) x j =
           -(curl (fun y => vec3Cross (sys.v t y) (sys.B t y)) x j) :=
    curl_neg (fun y => vec3Cross (sys.v t y) (sys.B t y)) x j
  linarith

/-- Current density is determined by Ampère's law: J = (∇×B)/μ₀. -/
theorem J_from_ampere (t : ℝ) (x : Vec3) (j : Fin 3) :
    sys.J t x j = (1 / c.μ₀) * curl (sys.B t) x j := by
  have h := sys.ampere t x j
  have hμ := c.μ₀_ne_zero
  field_simp
  linarith

/-- Divergence of B is preserved by the ideal induction equation.
    (Requires time integration — left as sorry.) -/
theorem div_B_preserved
    (h₀ : ∀ x, divergence (sys.B 0) x = 0)
    (t : ℝ) (x : Vec3) :
    divergence (sys.B t) x = 0 := by
  sorry

end IdealMHD

end PlasmaEquations
