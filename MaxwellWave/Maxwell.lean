/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Maxwell's Equations in Linear Media

We formalize Maxwell's equations in differential form for linear, isotropic,
homogeneous media. Three types of medium are considered:

1. **Vacuum**: ε = ε₀, μ = μ₀, σ = 0, ρ = 0, J = 0
2. **Dielectric**: general ε, μ, σ = 0, ρ_free = 0, J_free = 0
3. **Conductor**: general ε, μ, σ > 0, ρ_free = 0, J = σE

## Maxwell's Equations in Matter (differential form)

  (1) ∇·E = ρ / ε           — Gauss's law
  (2) ∇·B = 0               — No magnetic monopoles
  (3) ∇×E = −∂B/∂t          — Faraday's law
  (4) ∇×B = μJ + με ∂E/∂t   — Ampère-Maxwell law

## Constitutive Relations (linear, isotropic, homogeneous)

  D = εE,  B = μH,  J_cond = σE
-/
import MaxwellWave.VectorCalculus

noncomputable section

namespace MaxwellWave

open scoped BigOperators

/-! ## Linear Medium Parameters -/

/-- Parameters of a linear, isotropic, homogeneous electromagnetic medium.
    - `ε` : electric permittivity (F/m)
    - `μ` : magnetic permeability (H/m)
    - `σ` : electrical conductivity (S/m)
    All must be positive reals (physically meaningful). -/
structure Medium where
  ε : ℝ
  μ : ℝ
  σ : ℝ
  hε : 0 < ε
  hμ : 0 < μ
  hσ : 0 ≤ σ

namespace Medium

variable (m : Medium)

/-- The wave speed in the medium: v = 1/√(με). -/
def waveSpeed : ℝ := 1 / Real.sqrt (m.μ * m.ε)

/-- v² = 1/(με). -/
def waveSpeedSq : ℝ := 1 / (m.μ * m.ε)

lemma waveSpeedSq_pos : 0 < m.waveSpeedSq := by
  unfold waveSpeedSq
  apply div_pos one_pos (mul_pos m.hμ m.hε)

lemma mu_epsilon_pos : 0 < m.μ * m.ε := mul_pos m.hμ m.hε

lemma mu_ne_zero : m.μ ≠ 0 := ne_of_gt m.hμ

lemma epsilon_ne_zero : m.ε ≠ 0 := ne_of_gt m.hε

end Medium

/-- Vacuum medium with standard constants ε₀, μ₀. -/
def vacuum (ε₀ μ₀ : ℝ) (hε₀ : 0 < ε₀) (hμ₀ : 0 < μ₀) : Medium where
  ε := ε₀
  μ := μ₀
  σ := 0
  hε := hε₀
  hμ := hμ₀
  hσ := le_refl 0

/-- A lossless dielectric medium (σ = 0). -/
def dielectric (ε μ : ℝ) (hε : 0 < ε) (hμ : 0 < μ) : Medium where
  ε := ε
  μ := μ
  σ := 0
  hε := hε
  hμ := hμ
  hσ := le_refl 0

/-- A conducting medium (σ > 0). Used for "lossy" dielectrics and imperfect
    insulators. The conductivity introduces a damping term in the wave equation. -/
def conductor (ε μ σ : ℝ) (hε : 0 < ε) (hμ : 0 < μ) (hσ : 0 < σ) : Medium where
  ε := ε
  μ := μ
  σ := σ
  hε := hε
  hμ := hμ
  hσ := le_of_lt hσ

/-! ## Maxwell's Equations -/

/-- Maxwell's equations in a linear, isotropic, homogeneous medium.

Given a medium `m`, electric field `E`, magnetic field `B`, free charge
density `ρ`, and free current density `J_free`, this structure packages the
four equations plus the Ohm's law constitutive relation J_cond = σE.

The total current is J_total = J_free + σE. In source-free regions
(ρ = 0, J_free = 0), the only current comes from conductivity. -/
structure MaxwellSystem (m : Medium) where
  /-- Electric field E(t, x) -/
  E : TDVectorField
  /-- Magnetic field B(t, x) -/
  B : TDVectorField
  /-- Free charge density ρ(t, x) -/
  ρ : TDScalarField
  /-- Free current density J_free(t, x) -/
  J_free : TDVectorField
  /-- Gauss's law: ∇·E = ρ/ε -/
  gauss : ∀ t x, divergence (E t) x = ρ t x / m.ε
  /-- No magnetic monopoles: ∇·B = 0 -/
  no_monopole : ∀ t x, divergence (B t) x = 0
  /-- Faraday's law: ∇×E = −∂B/∂t -/
  faraday : ∀ t x j,
    curl (E t) x j = -(timeDerivComp B j t x)
  /-- Ampère-Maxwell law: ∇×B = μ(J_free + σE) + με ∂E/∂t -/
  ampere : ∀ t x j,
    curl (B t) x j =
      m.μ * (J_free t x j + m.σ * E t x j) +
      m.μ * m.ε * timeDerivComp E j t x
  /-- E is smooth (C² in space for each fixed t) -/
  hE_smooth : ∀ t, IsC2Vector (E t)
  /-- B is smooth (C² in space for each fixed t) -/
  hB_smooth : ∀ t, IsC2Vector (B t)

/-- A source-free Maxwell system: ρ = 0 and J_free = 0.
    The only current is the conduction current σE. -/
structure SourceFreeMaxwell (m : Medium) extends MaxwellSystem m where
  /-- No free charges -/
  charge_free : ∀ t x, ρ t x = 0
  /-- No free currents -/
  current_free : ∀ t x, J_free t x = 0

namespace SourceFreeMaxwell

variable {m : Medium} (sys : SourceFreeMaxwell m)

/-- In a source-free system, Gauss's law simplifies to ∇·E = 0. -/
lemma gauss_simplified (t : ℝ) (x : Vec3) :
    divergence (sys.E t) x = 0 := by
  rw [sys.gauss t x, sys.charge_free t x]
  simp

/-- In a source-free system, Ampère's law simplifies to
    ∇×B = μσE + με ∂E/∂t. -/
lemma ampere_simplified (t : ℝ) (x : Vec3) (j : Fin 3) :
    curl (sys.B t) x j =
      m.μ * m.σ * sys.E t x j +
      m.μ * m.ε * timeDerivComp sys.E j t x := by
  rw [sys.ampere t x j, sys.current_free t x]
  simp [mul_comm]
  ring

end SourceFreeMaxwell

end MaxwellWave
