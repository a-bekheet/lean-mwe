/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Resistive MHD

Extends ideal MHD with finite resistivity η, giving the generalized
Ohm's law E + v×B = ηJ. The induction equation becomes:
  ∂B/∂t = ∇×(v×B - ηJ)
which includes magnetic diffusion.
-/
import PlasmaEquations.SingleFluidMHD

noncomputable section

open scoped BigOperators

namespace PlasmaEquations

open MaxwellWave

/-! ## Ohm's Law -/

/-- Ohm's law parameters for a resistive plasma. -/
structure OhmsLaw where
  /-- Resistivity η (Ω·m). -/
  η : ℝ
  /-- Resistivity is non-negative. -/
  hη : 0 ≤ η

/-! ## Resistive MHD System -/

/-- The resistive MHD system.

Same as ideal MHD but with resistive Ohm's law E + v×B = ηJ.
The induction equation becomes: ∂B/∂t = ∇×(v×B - ηJ),
adding a magnetic diffusion term. -/
structure ResistiveMHD (c : MHDConstants) (ohm : OhmsLaw) where
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
  /-- Adiabatic energy equation. -/
  energy : ∀ t x,
    timeDeriv p t x +
      advectiveDerivScalar (v t) (p t) x +
      c.γ * p t x * divergence (v t) x = 0
  /-- Resistive induction equation: (∂B/∂t)_j = (∇×(v×B - ηJ))_j. -/
  induction_eq : ∀ t x j,
    timeDerivComp B j t x =
      curl (fun y => fun i =>
        vec3Cross (v t y) (B t y) i - ohm.η * J t y i) x j
  /-- Solenoidal constraint: ∇·B = 0. -/
  solenoidal : ∀ t x, divergence (B t) x = 0
  /-- Ampère's law: ∇×B = μ₀J. -/
  ampere : ∀ t x j, curl (B t) x j = c.μ₀ * J t x j
  /-- B is spatially smooth. -/
  hB_smooth : ∀ t, IsC2Vector (B t)
  /-- J is spatially smooth. -/
  hJ_smooth : ∀ t, IsC2Vector (J t)

namespace ResistiveMHD

variable {c : MHDConstants} {ohm : OhmsLaw} (sys : ResistiveMHD c ohm)

/-- When η = 0, the resistive induction equation reduces to the ideal one.
    This is because v×B - 0·J = v×B. -/
theorem resistive_reduces_to_ideal
    (hη : ohm.η = 0) (t : ℝ) (x : Vec3) (j : Fin 3) :
    timeDerivComp sys.B j t x =
      curl (fun y => vec3Cross (sys.v t y) (sys.B t y)) x j := by
  have h := sys.induction_eq t x j
  simp only [hη, zero_mul, sub_zero] at h
  exact h

/-- The resistive induction equation in diffusion form:
    ∂B/∂t = ∇×(v×B) - η∇×J.
    Splits curl(v×B - ηJ) = curl(v×B) - η·curl(J) using curl linearity. -/
theorem resistive_induction_diffusion_form (t : ℝ) (x : Vec3) (j : Fin 3)
    (hvxB : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun y => vec3Cross (sys.v t y) (sys.B t y) i) x) :
    timeDerivComp sys.B j t x =
      curl (fun y => vec3Cross (sys.v t y) (sys.B t y)) x j -
        ohm.η * curl (sys.J t) x j := by
  have hinduction := sys.induction_eq t x j
  rw [hinduction]
  have hJ_diff : ∀ i : Fin 3, DifferentiableAt ℝ (fun y => sys.J t y i) x :=
    fun i => (sys.hJ_smooth t).differentiableAt i x
  have hηJ_diff : ∀ i : Fin 3, DifferentiableAt ℝ (fun y => (-ohm.η) * sys.J t y i) x :=
    fun i => (differentiableAt_const (-ohm.η)).mul (hJ_diff i)
  have step1 : curl (fun y i => vec3Cross (sys.v t y) (sys.B t y) i - ohm.η * sys.J t y i) x j =
               curl (fun y i => vec3Cross (sys.v t y) (sys.B t y) i + (-ohm.η) * sys.J t y i) x j := by
    congr 1; funext y; funext i; ring
  rw [step1]
  rw [curl_add _ _ x hvxB hηJ_diff j]
  rw [curl_const_mul (-ohm.η) (sys.J t) x hJ_diff j]
  ring

end ResistiveMHD

end PlasmaEquations
