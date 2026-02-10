/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Two-Fluid Plasma Equations

The two-fluid model treats a plasma as two interpenetrating fluids:
ions and electrons. Each species satisfies its own continuity and
momentum equations, coupled through electromagnetic fields.
-/
import PlasmaEquations.FluidOperators
import PlasmaEquations.LorentzForce

noncomputable section

open scoped BigOperators

namespace PlasmaEquations

open MaxwellWave

/-! ## Plasma species -/

/-- A plasma species (ion or electron) characterized by charge and mass. -/
structure PlasmaSpecies where
  /-- Charge per particle (Coulombs). Positive for ions, negative for electrons. -/
  q : ℝ
  /-- Mass per particle (kg). -/
  m : ℝ
  /-- Mass is positive. -/
  hm : 0 < m

/-! ## Two-fluid system -/

/-- The two-fluid plasma equations for a single species.

Each species `s` has number density `n_s`, velocity `v_s`, and pressure `p_s`.
The equations are:
  - Continuity: `∂n_s/∂t + ∇·(n_s v_s) = 0`
  - Momentum: `m_s n_s Dv_s/Dt = q_s n_s (E + v_s × B) - ∇p_s`

These are axioms (the equations are assumed to hold). -/
structure TwoFluidSystem (sp : PlasmaSpecies) where
  /-- Number density n_s(t, x). -/
  n : TDScalarField
  /-- Velocity v_s(t, x). -/
  v : TDVectorField
  /-- Scalar pressure p_s(t, x). -/
  p : TDScalarField
  /-- Electric field E(t, x). -/
  E : TDVectorField
  /-- Magnetic field B(t, x). -/
  B : TDVectorField
  /-- Continuity equation: ∂n/∂t + ∇·(nv) = 0.
      Here ∇·(nv) = n(∇·v) + v·∇n, but we state it in conservation form. -/
  continuity : ∀ t x,
    timeDeriv n t x + divergence (fun y => fun i => n t y * v t y i) x = 0
  /-- Momentum equation: m n (Dv/Dt)_j = q n (E + v×B)_j - ∂p/∂x_j.
      The LHS uses the material derivative; the RHS has Lorentz force + pressure gradient. -/
  momentum : ∀ t x j,
    sp.m * n t x * materialDerivVector v v t x j =
      sp.q * n t x * (E t x j + fieldCross (v t) (B t) x j) -
      partialDeriv (p t) j x

end PlasmaEquations
