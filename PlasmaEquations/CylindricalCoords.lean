/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Cylindrical Coordinate Infrastructure

Minimal cylindrical coordinate definitions for tokamak and rotamak
equilibrium equations. We define coordinate extraction, axisymmetry,
and the Grad-Shafranov operator.
-/
import MaxwellWave.VectorCalculus

noncomputable section

namespace PlasmaEquations

open MaxwellWave

/-! ## Coordinate extraction

We embed cylindrical coordinates in Cartesian ℝ³ using
x₀ = R, x₁ = φ (toroidal angle), x₂ = Z. Functions are defined
on the (R, Z) plane for axisymmetric quantities. -/

/-- Extract the major radius R from a point (R, φ, Z). -/
def cylR (x : Vec3) : ℝ := x 0

/-- Extract the vertical coordinate Z from a point (R, φ, Z). -/
def cylZ (x : Vec3) : ℝ := x 2

/-! ## Axisymmetry -/

/-- A scalar field is axisymmetric if it depends only on R and Z (index 0 and 2),
    not on φ (index 1). Formally: ∂f/∂φ = 0 everywhere. -/
def IsAxisymmetric (f : ScalarField) : Prop :=
  ∀ x : Vec3, partialDeriv f 1 x = 0

/-! ## Poloidal flux function -/

/-- A poloidal flux function ψ(R, Z) used in axisymmetric equilibria.
    Packages the function with its smoothness and axisymmetry. -/
structure PoloidalFlux where
  /-- The flux function ψ : ℝ³ → ℝ (depends only on R, Z). -/
  ψ : ScalarField
  /-- ψ is C² smooth. -/
  smooth : IsC2Scalar ψ
  /-- ψ is axisymmetric (independent of toroidal angle). -/
  axisym : IsAxisymmetric ψ

/-! ## Grad-Shafranov operator

The Grad-Shafranov operator Δ* is defined as:
  Δ*ψ = ∂²ψ/∂R² - (1/R)∂ψ/∂R + ∂²ψ/∂Z²

This is the elliptic operator governing axisymmetric MHD equilibria
in tokamaks. It differs from the standard Laplacian by the sign of
the 1/R term (reflecting the toroidal geometry). -/

/-- The Grad-Shafranov operator: `Δ*ψ = ∂²ψ/∂R² - (1/R)∂ψ/∂R + ∂²ψ/∂Z²`.
    Here R = x₀, Z = x₂ in our coordinate convention. -/
def GradShafranovOp (ψ : ScalarField) (x : Vec3) : ℝ :=
  partialDeriv2 ψ 0 x - (1 / cylR x) * partialDeriv ψ 0 x + partialDeriv2 ψ 2 x

end PlasmaEquations
