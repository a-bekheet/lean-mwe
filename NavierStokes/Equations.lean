/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Incompressible Navier-Stokes Equations

The incompressible Navier-Stokes equations govern the motion of a viscous
incompressible fluid with constant density ρ and dynamic viscosity μ:

  ∇·v = 0                                           (incompressibility)
  ρ Dv/Dt = -∇p + μ∇²v + f                         (momentum)

where Dv/Dt = ∂v/∂t + (v·∇)v is the material derivative.

Setting μ = 0 recovers the Euler equations for inviscid flow.
-/
import PlasmaEquations.FluidOperators

noncomputable section

open scoped BigOperators

namespace NavierStokes

open MaxwellWave PlasmaEquations

/-! ## Fluid Constants -/

/-- Physical constants for an incompressible Newtonian fluid. -/
structure FluidConstants where
  /-- Constant mass density ρ (kg/m³). -/
  ρ : ℝ
  /-- Dynamic viscosity μ (Pa·s). -/
  μ : ℝ
  /-- ρ is positive. -/
  hρ : 0 < ρ
  /-- μ is non-negative (μ = 0 gives Euler equations). -/
  hμ : 0 ≤ μ

namespace FluidConstants
variable (c : FluidConstants)

lemma ρ_ne_zero : c.ρ ≠ 0 := ne_of_gt c.hρ
lemma ρ_pos : 0 < c.ρ := c.hρ

/-- Kinematic viscosity ν = μ/ρ. -/
def ν : ℝ := c.μ / c.ρ

lemma ν_nonneg : 0 ≤ c.ν := div_nonneg c.hμ (le_of_lt c.hρ)

end FluidConstants

/-! ## Incompressible Navier-Stokes System -/

/-- The incompressible Navier-Stokes system.

Fields: velocity `v`, pressure `p`, body force `f` (per unit volume).
The two equations are:
1. **Incompressibility**: ∇·v = 0
2. **Momentum**: ρ(Dv/Dt)_j = -∂p/∂x_j + μ(∇²v)_j + f_j -/
structure IncompressibleNS (c : FluidConstants) where
  /-- Velocity field v(t, x). -/
  v : TDVectorField
  /-- Pressure field p(t, x). -/
  p : TDScalarField
  /-- Body force per unit volume f(t, x). -/
  f : TDVectorField
  /-- Incompressibility: ∇·v = 0. -/
  incompressibility : ∀ t x, divergence (v t) x = 0
  /-- Momentum equation: ρ(Dv/Dt)_j = -∂p/∂x_j + μ(∇²v)_j + f_j. -/
  momentum : ∀ t x j,
    c.ρ * materialDerivVector v v t x j =
      -(partialDeriv (p t) j x) + c.μ * vectorLaplacian (v t) x j + f t x j
  /-- Velocity is spatially C². -/
  hv_smooth : ∀ t, IsC2Vector (v t)
  /-- Pressure is spatially C². -/
  hp_smooth : ∀ t, IsC2Scalar (p t)
  /-- Body force is spatially C². -/
  hf_smooth : ∀ t, IsC2Vector (f t)

namespace IncompressibleNS

variable {c : FluidConstants} (sys : IncompressibleNS c)

/-- Momentum equation per unit mass: dividing by ρ gives
    (Dv/Dt)_j = -(1/ρ)∂p/∂x_j + ν(∇²v)_j + (1/ρ)f_j. -/
theorem momentum_per_unit_mass (t : ℝ) (x : Vec3) (j : Fin 3) :
    materialDerivVector sys.v sys.v t x j =
      -(1 / c.ρ) * partialDeriv (sys.p t) j x +
        c.ν * vectorLaplacian (sys.v t) x j +
        (1 / c.ρ) * sys.f t x j := by
  have hρ := c.ρ_ne_zero
  have hmom := sys.momentum t x j
  simp only [FluidConstants.ν]
  field_simp
  linarith

/-- Mass conservation ∂ρ/∂t + ∇·(ρv) = 0 is trivially satisfied:
    ρ is constant so ∂ρ/∂t = 0, and ∇·(ρv) = ρ∇·v = 0. -/
theorem continuity_from_incompressible (t : ℝ) (x : Vec3) :
    divergence (fun y i => c.ρ * sys.v t y i) x = 0 := by
  simp only [divergence, partialDerivComp, Fin.sum_univ_three]
  have hv := sys.hv_smooth t
  have hdiff : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => sys.v t y j) x :=
    fun j => hv.differentiableAt j x
  simp only [show ∀ j : Fin 3, (fun y => c.ρ * sys.v t y j) =
    (c.ρ • (fun y => sys.v t y j)) from fun j => rfl,
    fderiv_const_smul (hdiff _), ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hinc := sys.incompressibility t x
  simp only [divergence, partialDerivComp, Fin.sum_univ_three] at hinc
  have hρ := c.hρ
  nlinarith [mul_eq_zero_of_right c.ρ hinc]

end IncompressibleNS

end NavierStokes
