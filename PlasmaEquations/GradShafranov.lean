/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Grad-Shafranov Equation (Tokamak Equilibrium)

The Grad-Shafranov equation governs axisymmetric MHD equilibria in tokamaks:
  Δ*ψ = -μ₀ R² p'(ψ) - g(ψ) g'(ψ)

where:
  - ψ(R,Z) is the poloidal magnetic flux
  - Δ* = ∂²/∂R² - (1/R)∂/∂R + ∂²/∂Z² is the Grad-Shafranov operator
  - p(ψ) is the pressure profile (free function)
  - g(ψ) = R B_φ is the poloidal current function (free function)
  - R is the major radius

This is the central equation of tokamak equilibrium theory.
-/
import PlasmaEquations.MHDEquilibrium

noncomputable section

namespace PlasmaEquations

open MaxwellWave

/-! ## Grad-Shafranov equation structure -/

/-- The Grad-Shafranov equation for tokamak axisymmetric equilibrium.

The equation `Δ*ψ = -μ₀ R² p'(ψ) - g(ψ) g'(ψ)` is an elliptic PDE
for the poloidal flux function ψ(R,Z). The free functions p(ψ) and g(ψ)
determine the equilibrium profiles.

We use the convention x₀ = R, x₁ = φ, x₂ = Z. -/
structure GradShafranovEquation (c : MHDConstants) where
  /-- Poloidal flux function ψ(R,Z). -/
  flux : PoloidalFlux
  /-- Pressure as a function of flux: p(ψ). -/
  p_of_ψ : ℝ → ℝ
  /-- Poloidal current function: g(ψ) = R B_φ. -/
  g_of_ψ : ℝ → ℝ
  /-- p is differentiable. -/
  hp_diff : Differentiable ℝ p_of_ψ
  /-- g is differentiable. -/
  hg_diff : Differentiable ℝ g_of_ψ
  /-- The Grad-Shafranov equation:
      Δ*ψ(R,Z) = -μ₀ R² p'(ψ) - g(ψ) g'(ψ).
      Here R = cylR x = x₀. -/
  gs_equation : ∀ x : Vec3,
    GradShafranovOp flux.ψ x =
      -(c.μ₀ * (cylR x)^2 * deriv p_of_ψ (flux.ψ x)) -
        g_of_ψ (flux.ψ x) * deriv g_of_ψ (flux.ψ x)

namespace GradShafranovEquation

variable {c : MHDConstants} (gs : GradShafranovEquation c)

/-- The pressure profile p(x) = p(ψ(x)). -/
def pressure : ScalarField := fun x => gs.p_of_ψ (gs.flux.ψ x)

/-- Pressure is constant on flux surfaces: p(x) depends only on ψ(x).
    This is trivially true by construction — p is defined as p(ψ(x)). -/
theorem gs_pressure_flux_surface (x y : Vec3) (hψ : gs.flux.ψ x = gs.flux.ψ y) :
    gs.pressure x = gs.pressure y := by
  simp only [pressure, hψ]

/-- g is constant on flux surfaces (by the same argument). -/
theorem gs_g_flux_surface (x y : Vec3) (hψ : gs.flux.ψ x = gs.flux.ψ y) :
    gs.g_of_ψ (gs.flux.ψ x) = gs.g_of_ψ (gs.flux.ψ y) := by
  simp only [hψ]

/-- The GS equation implies MHD equilibrium ∇p = J×B in cylindrical geometry.
    (Requires expanding the cylindrical curl and cross product — sorry.) -/
theorem gs_is_equilibrium (x : Vec3) :
    ∀ j, partialDeriv gs.pressure j x =
      fieldCross
        (fun y => fun i => (1 / c.μ₀) * curl (fun z => fun k =>
          -- Magnetic field in (R,φ,Z) from ψ and g
          match k with
          | ⟨0, _⟩ => -(1 / cylR z) * partialDeriv gs.flux.ψ 2 z
          | ⟨1, _⟩ => gs.g_of_ψ (gs.flux.ψ z) / cylR z
          | ⟨2, _⟩ => (1 / cylR z) * partialDeriv gs.flux.ψ 0 z
          ) y i)
        (fun y => fun k =>
          match k with
          | ⟨0, _⟩ => -(1 / cylR y) * partialDeriv gs.flux.ψ 2 y
          | ⟨1, _⟩ => gs.g_of_ψ (gs.flux.ψ y) / cylR y
          | ⟨2, _⟩ => (1 / cylR y) * partialDeriv gs.flux.ψ 0 y
          ) x j := by
  sorry

/-- Solov'ev solution: when p(ψ) = p₀ψ and g²(ψ) = g₀² + 2αψ are linear,
    the GS equation becomes linear with constant coefficients on the RHS.
    (Straightforward but tedious differentiation — sorry.) -/
theorem gs_solovev_linear
    (p₀ g₀_sq α : ℝ)
    (hp : gs.p_of_ψ = fun ψ_val => p₀ * ψ_val)
    (hg_sq : ∀ ψ_val, (gs.g_of_ψ ψ_val)^2 = g₀_sq + 2 * α * ψ_val)
    (x : Vec3) :
    GradShafranovOp gs.flux.ψ x =
      -(c.μ₀ * (cylR x)^2 * p₀) - α := by
  -- From the GS equation axiom
  have hgs := gs.gs_equation x
  set ψ₀ := gs.flux.ψ x
  -- Compute deriv p_of_ψ(ψ₀) = p₀ (derivative of linear function)
  have hp_deriv : deriv gs.p_of_ψ ψ₀ = p₀ := by
    rw [hp]
    have hd : HasDerivAt (fun ψ_val => p₀ * ψ_val) p₀ ψ₀ := by
      have := (hasDerivAt_id ψ₀).const_mul p₀
      simpa [mul_one] using this
    exact hd.deriv
  -- Compute g(ψ₀) * g'(ψ₀) = α from g²(ψ) = g₀² + 2αψ
  -- Differentiating: 2g·g' = 2α, so g·g' = α
  have hgg : gs.g_of_ψ ψ₀ * deriv gs.g_of_ψ ψ₀ = α := by
    have hgd : DifferentiableAt ℝ gs.g_of_ψ ψ₀ := gs.hg_diff.differentiableAt
    have hg_sq_fn : (fun t => (gs.g_of_ψ t)^2) = (fun t => g₀_sq + 2 * α * t) :=
      funext hg_sq
    -- Derivatives must be equal
    have hdeq : deriv (fun t => (gs.g_of_ψ t)^2) ψ₀ = deriv (fun t => g₀_sq + 2 * α * t) ψ₀ :=
      congrArg (fun f => deriv f ψ₀) hg_sq_fn
    -- LHS: deriv(g²) = 2·g·g' via product rule on g·g
    have hLHS : deriv (fun t => (gs.g_of_ψ t)^2) ψ₀ =
                2 * gs.g_of_ψ ψ₀ * deriv gs.g_of_ψ ψ₀ := by
      have hsq : (fun t => (gs.g_of_ψ t)^2) = gs.g_of_ψ * gs.g_of_ψ := by
        funext t; simp [Pi.mul_apply]; ring
      rw [hsq, deriv_mul hgd hgd]; ring
    -- RHS: deriv(g₀² + 2α·t) = 2α
    have hRHS : deriv (fun t => g₀_sq + 2 * α * t) ψ₀ = 2 * α := by
      have hd : HasDerivAt (fun t => g₀_sq + 2 * α * t) (2 * α) ψ₀ := by
        have := ((hasDerivAt_id ψ₀).const_mul (2 * α)).const_add g₀_sq
        simp only [mul_one] at this
        convert this using 1
      exact hd.deriv
    linarith
  rw [hgs, hp_deriv, hgg]

end GradShafranovEquation

end PlasmaEquations
