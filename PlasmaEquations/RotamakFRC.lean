/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Rotamak / Field-Reversed Configuration (FRC) Equations

A Field-Reversed Configuration (FRC) is a compact toroid plasma where
the poloidal magnetic field reverses direction. A Rotamak is an FRC
sustained by a Rotating Magnetic Field (RMF) drive.

## FRC Equilibrium
The radial pressure balance in a cylindrical FRC is:
  dp/dR + (1/μ₀) B_z dB_z/dR + (1/μ₀) B_θ dB_θ/dR = 0

At the separatrix R = R_s, B_z(R_s) = 0 (field reversal), giving β = 1.

## Rotamak Drive
The RMF with amplitude B_ω and frequency ω drives toroidal current J_θ,
which sustains the FRC against resistive decay.
-/
import PlasmaEquations.MHDEquilibrium

noncomputable section

namespace PlasmaEquations

open MaxwellWave

/-! ## FRC Equilibrium -/

/-- FRC equilibrium in cylindrical geometry.

Radial profiles `p(R)`, `B_z(R)`, `B_θ(R)` satisfying radial
pressure balance and field reversal at the separatrix. -/
structure FRCEquilibrium (c : MHDConstants) where
  /-- Pressure profile p(R). -/
  p : ℝ → ℝ
  /-- Axial (poloidal) field B_z(R). -/
  B_z : ℝ → ℝ
  /-- Toroidal field B_θ(R). -/
  B_θ : ℝ → ℝ
  /-- Separatrix radius. -/
  R_s : ℝ
  /-- External axial field (at R → ∞ or edge). -/
  B_ext : ℝ
  /-- p is differentiable. -/
  hp_diff : Differentiable ℝ p
  /-- B_z is differentiable. -/
  hBz_diff : Differentiable ℝ B_z
  /-- B_θ is differentiable. -/
  hBθ_diff : Differentiable ℝ B_θ
  /-- Field reversal at separatrix: B_z(R_s) = 0. -/
  field_reversal : B_z R_s = 0
  /-- R_s is positive. -/
  hRs_pos : 0 < R_s
  /-- B_ext is positive. -/
  hBext_pos : 0 < B_ext
  /-- Radial pressure balance:
      dp/dR + (1/μ₀)(B_z dB_z/dR + B_θ dB_θ/dR) = 0.
      This is the 1D equilibrium condition in cylindrical geometry. -/
  radial_balance : ∀ R : ℝ,
    deriv p R + (1 / c.μ₀) * (B_z R * deriv B_z R + B_θ R * deriv B_θ R) = 0
  /-- Pressure at the edge equals magnetic pressure:
      p(edge) = 0, giving total pressure = B_ext²/(2μ₀). -/
  edge_pressure : p R_s = B_ext^2 / (2 * c.μ₀)

namespace FRCEquilibrium

variable {c : MHDConstants} (frc : FRCEquilibrium c)

/-- In a pure FRC with no toroidal field (B_θ = 0), the radial balance
    simplifies to dp/dR + (1/μ₀) B_z dB_z/dR = 0. -/
theorem frc_no_toroidal_balance
    (hBθ_zero : ∀ R, frc.B_θ R = 0)
    (R : ℝ) :
    deriv frc.p R + (1 / c.μ₀) * (frc.B_z R * deriv frc.B_z R) = 0 := by
  have h := frc.radial_balance R
  have hBθ : frc.B_θ R = 0 := hBθ_zero R
  have hderiv_Bθ : deriv frc.B_θ R = 0 := by
    have : frc.B_θ = fun _ => 0 := funext hBθ_zero
    rw [this]; simp
  rw [hBθ, hderiv_Bθ] at h
  linarith

/-- Total pressure conservation in the θ-pinch (B_θ = 0) limit:
    p(R) + B_z(R)²/(2μ₀) = B_ext²/(2μ₀).

    This is the integrated form of the radial pressure balance
    assuming p → 0 and B_z → B_ext at the separatrix/edge.

    Note: This is stated as an axiom-consequence pairing. We prove it
    assuming the integrated form holds from the edge condition. -/
theorem frc_total_pressure_conservation
    (htotal : ∀ R, frc.p R + frc.B_z R ^ 2 / (2 * c.μ₀) =
                    frc.B_ext ^ 2 / (2 * c.μ₀))
    (R : ℝ) :
    frc.p R = (frc.B_ext ^ 2 - frc.B_z R ^ 2) / (2 * c.μ₀) := by
  have h := htotal R
  have hμ₀ : (0 : ℝ) < c.μ₀ := c.hμ₀
  field_simp at h ⊢
  linarith

/-- β = 1 at the separatrix: since B_z(R_s) = 0, the kinetic pressure
    equals the total magnetic pressure.

    β = 2μ₀p / B² = 2μ₀p / B_ext² = 1 at R = R_s. -/
theorem frc_beta_at_separatrix :
    2 * c.μ₀ * frc.p frc.R_s = frc.B_ext ^ 2 := by
  have h := frc.edge_pressure
  have hμ₀ : (0 : ℝ) < c.μ₀ := c.hμ₀
  field_simp at h ⊢
  linarith

end FRCEquilibrium

/-! ## Rotating Magnetic Field (RMF) Drive -/

/-- Parameters of the Rotating Magnetic Field drive. -/
structure RotamakDrive where
  /-- RMF amplitude (Tesla). -/
  B_ω : ℝ
  /-- RMF angular frequency (rad/s). -/
  ω : ℝ
  /-- Amplitude is positive. -/
  hBω_pos : 0 < B_ω
  /-- Frequency is positive. -/
  hω_pos : 0 < ω

/-! ## Rotamak System -/

/-- A Rotamak system: an FRC driven by a rotating magnetic field.

The RMF penetrates the plasma and drives a toroidal current J_θ via
electron drag, which sustains the FRC poloidal field against
resistive decay.

Ampère's law in 1D cylindrical: dB_z/dR = -μ₀ J_θ(R). -/
structure RotamakSystem (c : MHDConstants) extends FRCEquilibrium c where
  /-- RMF drive parameters. -/
  drive : RotamakDrive
  /-- Toroidal current density J_θ(R) driven by RMF. -/
  J_θ : ℝ → ℝ
  /-- Ampère's law relates B_z gradient to toroidal current:
      dB_z/dR = -μ₀ J_θ(R). -/
  ampere_1d : ∀ R : ℝ, deriv B_z R = -(c.μ₀ * J_θ R)

namespace RotamakSystem

variable {c : MHDConstants} (rot : RotamakSystem c)

/-- Ampère consistency: the current direction must be consistent with
    field reversal. Specifically, J_θ > 0 in the region where B_z
    decreases (inside the separatrix).
    (Requires analysis of the sign of dB_z/dR — left as sorry.) -/
theorem rotamak_ampere_consistency
    (R : ℝ) (hR : 0 < R) (hR_lt : R < rot.R_s)
    (hBz_decreasing : deriv rot.B_z R < 0) :
    0 < rot.J_θ R := by
  sorry

end RotamakSystem

end PlasmaEquations
