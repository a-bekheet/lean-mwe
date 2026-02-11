/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Euler Equations (Inviscid Limit)

Setting μ = 0 in the incompressible Navier-Stokes equations recovers
the Euler equations for inviscid incompressible flow:

  ∇·v = 0
  ρ Dv/Dt = -∇p + f
-/
import NavierStokes.Equations

noncomputable section

open scoped BigOperators

namespace NavierStokes

open MaxwellWave PlasmaEquations

namespace IncompressibleNS

variable {c : FluidConstants} (sys : IncompressibleNS c)

/-- Euler momentum equation: when μ = 0, the viscous term vanishes.
    ρ(Dv/Dt)_j = -∂p/∂x_j + f_j. -/
theorem euler_momentum (hμ : c.μ = 0) (t : ℝ) (x : Vec3) (j : Fin 3) :
    c.ρ * materialDerivVector sys.v sys.v t x j =
      -(partialDeriv (sys.p t) j x) + sys.f t x j := by
  have h := sys.momentum t x j
  rw [hμ] at h
  linarith

/-- Euler momentum per unit mass: (Dv/Dt)_j = -(1/ρ)∂p/∂x_j + (1/ρ)f_j. -/
theorem euler_momentum_per_unit_mass (hμ : c.μ = 0) (t : ℝ) (x : Vec3) (j : Fin 3) :
    materialDerivVector sys.v sys.v t x j =
      -(1 / c.ρ) * partialDeriv (sys.p t) j x +
        (1 / c.ρ) * sys.f t x j := by
  have h := sys.momentum_per_unit_mass t x j
  simp only [FluidConstants.ν, hμ, zero_div, zero_mul, add_zero] at h
  linarith

end IncompressibleNS

end NavierStokes
