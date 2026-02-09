/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Derivation of Electromagnetic Wave Equations

We derive the wave equations for E and B from Maxwell's equations in three media:

1. **Vacuum** (σ = 0, ρ = 0, J = 0):
     ∇²E = μ₀ε₀ ∂²E/∂t²
     ∇²B = μ₀ε₀ ∂²B/∂t²
   with wave speed c = 1/√(μ₀ε₀).

2. **Lossless dielectric** (σ = 0, ρ_free = 0, J_free = 0):
     ∇²E = με ∂²E/∂t²
     ∇²B = με ∂²B/∂t²
   with wave speed v = 1/√(με) = c/n where n = √(εᵣμᵣ).

3. **Lossy medium / conductor** (σ > 0, ρ_free = 0, J_free = 0):
     ∇²E = με ∂²E/∂t² + μσ ∂E/∂t
     ∇²B = με ∂²B/∂t² + μσ ∂B/∂t
   This is the telegraph equation / damped wave equation.

## Derivation Strategy

For all three cases:
  1. Take curl of Faraday's law: ∇×(∇×E) = −∂(∇×B)/∂t
  2. Apply: ∇×(∇×E) = ∇(∇·E) − ∇²E
  3. Use ∇·E = 0 (source-free): −∇²E = −∂(∇×B)/∂t
  4. Substitute Ampère-Maxwell for ∇×B
  5. Rearrange to obtain the wave equation
-/
import MaxwellWave.Maxwell

noncomputable section

namespace MaxwellWave

open scoped BigOperators

/-! ## Smoothness Assumptions -/

/-- Sufficient smoothness for the wave equation derivation.
    Bundles the commutativity of curl/time derivatives and C² conditions. -/
structure SufficientlySmooth {m : Medium} (sys : SourceFreeMaxwell m) where
  curl_time_commute_E : ∀ t x j,
    timeDerivComp (fun t x => curl (sys.E t) x) j t x =
    curl (fun x => fun k => timeDerivComp sys.E k t x) x j
  curl_time_commute_B : ∀ t x j,
    timeDerivComp (fun t x => curl (sys.B t) x) j t x =
    curl (fun x => fun k => timeDerivComp sys.B k t x) x j
  hE_C2 : ∀ t, IsC2Vector (sys.E t)
  hB_C2 : ∀ t, IsC2Vector (sys.B t)
  hEt_C2 : ∀ t, IsC2Vector (fun x => fun j => timeDerivComp sys.E j t x)
  hBt_C2 : ∀ t, IsC2Vector (fun x => fun j => timeDerivComp sys.B j t x)
  hE_time_diff : ∀ t x j, DifferentiableAt ℝ (fun s => sys.E s x j) t
  hEt_time_diff : ∀ t x j, DifferentiableAt ℝ (fun s => timeDerivComp sys.E j s x) t
  hB_time_diff : ∀ t x j, DifferentiableAt ℝ (fun s => sys.B s x j) t
  hBt_time_diff : ∀ t x j, DifferentiableAt ℝ (fun s => timeDerivComp sys.B j s x) t

/-! ## IV. General Wave Equation (Unified)

All three cases are instances of the general damped wave equation:
  ∇²F = με ∂²F/∂t² + μσ ∂F/∂t
-/

/-- **General electromagnetic wave equation for E in a source-free linear medium.**

    ∇²E(t,x)ⱼ = με · ∂²Eⱼ/∂t² + μσ · ∂Eⱼ/∂t

    Derivation:
    1. Curl of Faraday: ∇×(∇×E) = −∂(∇×B)/∂t
    2. Curl-curl identity + ∇·E = 0: −∇²E = −∂(∇×B)/∂t
    3. Substitute Ampère: ∇×B = μσE + με ∂E/∂t
    4. Therefore: ∇²E = με ∂²E/∂t² + μσ ∂E/∂t -/
private lemma partialDeriv_of_zero (j : Fin 3) (x : Vec3) :
    partialDeriv (fun _ => (0 : ℝ)) j x = 0 := by
  simp [partialDeriv]

theorem general_wave_equation_E
    (m : Medium) (sys : SourceFreeMaxwell m) (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    vectorLaplacian (sys.E t) x j =
      m.μ * m.ε * timeDerivComp2 sys.E j t x +
      m.μ * m.σ * timeDerivComp sys.E j t x := by
  -- Step 1: curl-curl identity → ∇²E = ∇(div E) - curl(curl E)
  have hcc_j : curl (curl (sys.E t)) x j =
      partialDeriv (divergence (sys.E t)) j x - vectorLaplacian (sys.E t) x j :=
    congr_fun (curl_curl_eq_grad_div_sub_laplacian (sys.E t) (sm.hE_C2 t) x) j
  -- Step 2: div E = 0 ⟹ ∂(div E) = 0
  have hpd0 : partialDeriv (divergence (sys.E t)) j x = 0 := by
    rw [show divergence (sys.E t) = fun _ => 0 from funext (sys.gauss_simplified t)]
    exact partialDeriv_of_zero j x
  -- Step 3: ∇²E = -curl(curl E)
  have hlapl : vectorLaplacian (sys.E t) x j = -(curl (curl (sys.E t)) x j) := by
    linarith
  -- Step 4: Faraday as function equality: curl E = -∂B/∂t
  have hfar : curl (sys.E t) = fun y k => -(timeDerivComp sys.B k t y) :=
    funext fun y => funext fun k => sys.faraday t y k
  -- Step 5: curl(curl E) = curl(-∂B/∂t) = -(curl(∂B/∂t)) by curl_neg
  have hcn : curl (curl (sys.E t)) x j =
      -(curl (fun y k => timeDerivComp sys.B k t y) x j) := by
    conv_lhs => rw [hfar]
    exact curl_neg _ x j
  -- Step 6: Commute curl and ∂/∂t using SufficientlySmooth
  have hcomm : curl (fun y k => timeDerivComp sys.B k t y) x j =
      timeDerivComp (fun s y => curl (sys.B s) y) j t x :=
    (sm.curl_time_commute_B t x j).symm
  -- Step 7: Combine: ∇²E = ∂/∂t(curl B)
  have hstep7 : vectorLaplacian (sys.E t) x j =
      timeDerivComp (fun s y => curl (sys.B s) y) j t x := by
    rw [hlapl, hcn, hcomm]; ring
  -- Step 8: Ampère → rewrite curl B componentwise
  have hamp : (fun s => curl (sys.B s) x j) =
      (fun s => m.μ * m.σ * sys.E s x j + m.μ * m.ε * timeDerivComp sys.E j s x) :=
    funext fun s => sys.ampere_simplified s x j
  -- Step 9: Substitute Ampère into time derivative
  have hstep9 : timeDerivComp (fun s y => curl (sys.B s) y) j t x =
      deriv (fun s => m.μ * m.σ * sys.E s x j +
        m.μ * m.ε * timeDerivComp sys.E j s x) t := by
    unfold timeDerivComp; congr 1
  -- Step 10: Linearity of deriv → split into components
  have hstep10 : deriv (fun s => m.μ * m.σ * sys.E s x j +
      m.μ * m.ε * timeDerivComp sys.E j s x) t =
      m.μ * m.σ * timeDerivComp sys.E j t x +
      m.μ * m.ε * timeDerivComp2 sys.E j t x := by
    have hd1 := sm.hE_time_diff t x j
    have hd2 := sm.hEt_time_diff t x j
    rw [show (fun s => m.μ * m.σ * sys.E s x j + m.μ * m.ε * timeDerivComp sys.E j s x) =
      ((m.μ * m.σ) • (fun s => sys.E s x j) + (m.μ * m.ε) • (fun s => timeDerivComp sys.E j s x))
      from rfl]
    rw [deriv_add (DifferentiableAt.const_smul hd1 _) (DifferentiableAt.const_smul hd2 _),
        deriv_const_smul _ hd1, deriv_const_smul _ hd2]
    simp [smul_eq_mul, timeDerivComp, timeDerivComp2]
  -- Final assembly
  rw [hstep7, hstep9, hstep10]; ring

/-- **General electromagnetic wave equation for B.**

    Derivation:
    1. curl-curl + ∇·B = 0: ∇²B = -curl(curl B)
    2. Ampère as fn equality: curl B = μσE + με ∂E/∂t
    3. curl linearity: curl(curl B) = μσ curl(E) + με curl(∂E/∂t)
    4. Time commutativity: curl(∂E/∂t) = ∂(curl E)/∂t
    5. Faraday: curl E = -∂B/∂t
    6. Therefore: ∇²B = με ∂²B/∂t² + μσ ∂B/∂t -/
theorem general_wave_equation_B
    (m : Medium) (sys : SourceFreeMaxwell m) (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    vectorLaplacian (sys.B t) x j =
      m.μ * m.ε * timeDerivComp2 sys.B j t x +
      m.μ * m.σ * timeDerivComp sys.B j t x := by
  -- Step 1: curl-curl + div B = 0 → ∇²B = -curl(curl B)
  have hcc_j : curl (curl (sys.B t)) x j =
      partialDeriv (divergence (sys.B t)) j x - vectorLaplacian (sys.B t) x j :=
    congr_fun (curl_curl_eq_grad_div_sub_laplacian (sys.B t) (sm.hB_C2 t) x) j
  have hpd0 : partialDeriv (divergence (sys.B t)) j x = 0 := by
    rw [show divergence (sys.B t) = fun _ => 0 from funext (sys.no_monopole t)]
    exact partialDeriv_of_zero j x
  have hlapl : vectorLaplacian (sys.B t) x j = -(curl (curl (sys.B t)) x j) := by
    linarith
  -- Step 2: Ampère as function equality: curl(B t) = fun y k => μσ E y k + με ∂E_k/∂t
  have hamp_fn : curl (sys.B t) = fun y k =>
      m.μ * m.σ * sys.E t y k + m.μ * m.ε * timeDerivComp sys.E k t y :=
    funext fun y => funext fun k => sys.ampere_simplified t y k
  -- Step 3: curl(curl B) = curl(Ampere RHS) = μσ curl(E) + με curl(∂E/∂t)
  have hE_diff : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => sys.E t y k) x :=
    fun k => (sm.hE_C2 t).differentiableAt k x
  have hEt_diff : ∀ k : Fin 3, DifferentiableAt ℝ
      (fun y => timeDerivComp sys.E k t y) x :=
    fun k => (sm.hEt_C2 t).differentiableAt k x
  have hcurl_split : curl (curl (sys.B t)) x j =
      m.μ * m.σ * curl (sys.E t) x j +
      m.μ * m.ε * curl (fun y k => timeDerivComp sys.E k t y) x j := by
    conv_lhs => rw [hamp_fn]
    rw [curl_add _ _ x (fun k => (hE_diff k).const_mul _) (fun k => (hEt_diff k).const_mul _) j,
        curl_const_mul _ _ x hE_diff j, curl_const_mul _ _ x hEt_diff j]
  -- Step 4: Faraday componentwise: curl(E t) x j = -(∂B_j/∂t)
  have hfar_j : curl (sys.E t) x j = -(timeDerivComp sys.B j t x) :=
    sys.faraday t x j
  -- Step 5: curl(∂E/∂t) = ∂(curl E)/∂t by time commutativity
  have hcomm_E : curl (fun y k => timeDerivComp sys.E k t y) x j =
      timeDerivComp (fun s y => curl (sys.E s) y) j t x :=
    (sm.curl_time_commute_E t x j).symm
  -- Step 6: ∂(curl E)/∂t = ∂(-∂B/∂t)/∂t = -∂²B/∂t²
  have hfar_deriv : timeDerivComp (fun s y => curl (sys.E s) y) j t x =
      -(timeDerivComp2 sys.B j t x) := by
    unfold timeDerivComp timeDerivComp2
    rw [show (fun s => curl (sys.E s) x j) =
      (fun s => -(timeDerivComp sys.B j s x)) from funext fun s => sys.faraday s x j]
    simp
  -- Final assembly: ∇²B = -(μσ(-∂B/∂t) + με(-∂²B/∂t²)) = μσ ∂B/∂t + με ∂²B/∂t²
  rw [hlapl, hcurl_split, hfar_j, hcomm_E, hfar_deriv]; ring

/-! ## I. Wave Equation in Vacuum

Setting σ = 0 and using ε₀, μ₀, the general equation becomes:
  ∇²E = μ₀ε₀ ∂²E/∂t²

The speed of light is c = 1/√(μ₀ε₀).
-/

/-- **Wave equation for E in vacuum**: ∇²E = μ₀ε₀ ∂²E/∂t². -/
theorem vacuum_wave_equation_E
    (ε₀ μ₀ : ℝ) (hε₀ : 0 < ε₀) (hμ₀ : 0 < μ₀)
    (sys : SourceFreeMaxwell (vacuum ε₀ μ₀ hε₀ hμ₀))
    (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    vectorLaplacian (sys.E t) x j =
      μ₀ * ε₀ * timeDerivComp2 sys.E j t x := by
  have h := general_wave_equation_E (vacuum ε₀ μ₀ hε₀ hμ₀) sys sm t x j
  simp [vacuum] at h
  linarith

/-- **Wave equation for B in vacuum**: ∇²B = μ₀ε₀ ∂²B/∂t². -/
theorem vacuum_wave_equation_B
    (ε₀ μ₀ : ℝ) (hε₀ : 0 < ε₀) (hμ₀ : 0 < μ₀)
    (sys : SourceFreeMaxwell (vacuum ε₀ μ₀ hε₀ hμ₀))
    (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    vectorLaplacian (sys.B t) x j =
      μ₀ * ε₀ * timeDerivComp2 sys.B j t x := by
  have h := general_wave_equation_B (vacuum ε₀ μ₀ hε₀ hμ₀) sys sm t x j
  simp [vacuum] at h
  linarith

/-- The wave speed in vacuum: c = 1/√(μ₀ε₀). -/
theorem vacuum_wave_speed (ε₀ μ₀ : ℝ) (hε₀ : 0 < ε₀) (hμ₀ : 0 < μ₀) :
    (vacuum ε₀ μ₀ hε₀ hμ₀).waveSpeed = 1 / Real.sqrt (μ₀ * ε₀) := by
  rfl

/-! ## II. Wave Equation in a Lossless Dielectric

Setting σ = 0 with general ε, μ:
  ∇²E = με ∂²E/∂t²

Phase velocity v = 1/√(με) = c/n where n = √(εᵣμᵣ).
-/

/-- **Wave equation for E in a dielectric**: ∇²E = με ∂²E/∂t². -/
theorem dielectric_wave_equation_E
    (ε μ : ℝ) (hε : 0 < ε) (hμ : 0 < μ)
    (sys : SourceFreeMaxwell (dielectric ε μ hε hμ))
    (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    vectorLaplacian (sys.E t) x j =
      μ * ε * timeDerivComp2 sys.E j t x := by
  have h := general_wave_equation_E (dielectric ε μ hε hμ) sys sm t x j
  simp [dielectric] at h
  linarith

/-- **Wave equation for B in a dielectric**: ∇²B = με ∂²B/∂t². -/
theorem dielectric_wave_equation_B
    (ε μ : ℝ) (hε : 0 < ε) (hμ : 0 < μ)
    (sys : SourceFreeMaxwell (dielectric ε μ hε hμ))
    (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    vectorLaplacian (sys.B t) x j =
      μ * ε * timeDerivComp2 sys.B j t x := by
  have h := general_wave_equation_B (dielectric ε μ hε hμ) sys sm t x j
  simp [dielectric] at h
  linarith

/-- Phase velocity squared in a dielectric: v² = 1/(με). -/
theorem dielectric_wave_speed_sq (ε μ : ℝ) (hε : 0 < ε) (hμ : 0 < μ) :
    (dielectric ε μ hε hμ).waveSpeedSq = 1 / (μ * ε) := by
  rfl

/-! ## III. Wave Equation in a Conductor (Telegraph Equation)

With σ > 0:
  ∇²E = με ∂²E/∂t² + μσ ∂E/∂t

The μσ ∂E/∂t term causes exponential attenuation (skin effect).
-/

/-- **Damped wave equation for E in a conductor (telegraph equation):**
    ∇²E = με ∂²E/∂t² + μσ ∂E/∂t -/
theorem conductor_wave_equation_E
    (ε μ σ : ℝ) (hε : 0 < ε) (hμ : 0 < μ) (hσ : 0 < σ)
    (sys : SourceFreeMaxwell (conductor ε μ σ hε hμ hσ))
    (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    vectorLaplacian (sys.E t) x j =
      μ * ε * timeDerivComp2 sys.E j t x +
      μ * σ * timeDerivComp sys.E j t x := by
  exact general_wave_equation_E (conductor ε μ σ hε hμ hσ) sys sm t x j

/-- **Damped wave equation for B in a conductor:**
    ∇²B = με ∂²B/∂t² + μσ ∂B/∂t -/
theorem conductor_wave_equation_B
    (ε μ σ : ℝ) (hε : 0 < ε) (hμ : 0 < μ) (hσ : 0 < σ)
    (sys : SourceFreeMaxwell (conductor ε μ σ hε hμ hσ))
    (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    vectorLaplacian (sys.B t) x j =
      μ * ε * timeDerivComp2 sys.B j t x +
      μ * σ * timeDerivComp sys.B j t x := by
  exact general_wave_equation_B (conductor ε μ σ hε hμ hσ) sys sm t x j

end MaxwellWave
