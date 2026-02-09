/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Detailed Proof Sketches

Provides the step-by-step derivation structure that would fill in the
`sorry`s in `WaveEquation.lean`.
-/
import MaxwellWave.WaveEquation

noncomputable section

namespace MaxwellWave

/-! ## Step-by-Step Derivation for E

### Step 1: Curl of Faraday's law

  ∇×(∇×E) = ∇×(−∂B/∂t) = −∂(∇×B)/∂t

### Step 2: Curl-curl identity

  ∇×(∇×E) = ∇(∇·E) − ∇²E

### Step 3: Source-free simplification (∇·E = 0)

  −∇²E = −∂(∇×B)/∂t

### Step 4: Substitute Ampère-Maxwell law

  ∇×B = μσE + με ∂E/∂t

  −∇²E = −∂/∂t[μσE + με ∂E/∂t]
        = −μσ ∂E/∂t − με ∂²E/∂t²

### Step 5: Rearrange

  ∇²E = με ∂²E/∂t² + μσ ∂E/∂t                                        ∎
-/

/-- Curl of Faraday's law: ∇×(∇×E) = −∂(∇×B)/∂t.
    Proof: Faraday gives curl E = -∂B/∂t, then curl_neg distributes the
    negation, and curl_time_commute_B swaps curl with ∂/∂t. -/
theorem curl_of_faraday
    (m : Medium) (sys : SourceFreeMaxwell m) (sm : SufficientlySmooth sys)
    (t : ℝ) (x : Vec3) (j : Fin 3) :
    curl (curl (sys.E t)) x j =
      -(timeDerivComp (fun t x => curl (sys.B t) x) j t x) := by
  -- Faraday: curl E = -∂B/∂t as function equality
  have hfar : curl (sys.E t) = fun y k => -(timeDerivComp sys.B k t y) :=
    funext fun y => funext fun k => sys.faraday t y k
  -- curl(-∂B/∂t) = -(curl(∂B/∂t)) by curl_neg
  have hcn : curl (curl (sys.E t)) x j =
      -(curl (fun y k => timeDerivComp sys.B k t y) x j) := by
    conv_lhs => rw [hfar]; exact curl_neg _ x j
  -- curl(∂B/∂t) = ∂(curl B)/∂t by time commutativity
  have hcomm : curl (fun y k => timeDerivComp sys.B k t y) x j =
      timeDerivComp (fun s y => curl (sys.B s) y) j t x :=
    (sm.curl_time_commute_B t x j).symm
  rw [hcn, hcomm]

/-! ## Step-by-step Derivation for B

### Step 1: Curl of Ampère-Maxwell law

  ∇×(∇×B) = ∇×(μσE + με ∂E/∂t)
           = μσ(∇×E) + με ∂(∇×E)/∂t

### Step 2: Substitute Faraday (∇×E = −∂B/∂t)

  = μσ(−∂B/∂t) + με ∂/∂t(−∂B/∂t)
  = −μσ ∂B/∂t − με ∂²B/∂t²

### Step 3: Curl-curl identity + ∇·B = 0

  −∇²B = −μσ ∂B/∂t − με ∂²B/∂t²

### Step 4: Rearrange

  ∇²B = με ∂²B/∂t² + μσ ∂B/∂t                                        ∎
-/

/-!
## Remaining `sorry`s (in VectorCalculus.lean)

All wave equation proofs (`general_wave_equation_E/B`, vacuum, dielectric,
conductor variants) and `curl_of_faraday` are now fully proved. The remaining
`sorry`s are purely in the vector calculus layer:

1. **`fderiv_apply_comm`**: Symmetry of mixed partials. Bridge to Mathlib's
   `IsSymmSndFDerivAt` — requires showing that `fderiv ℝ (fun y => fderiv ℝ f y v) x w`
   equals `(fderiv ℝ (fderiv ℝ f) x w) v` via the chain rule for CLM evaluation.

2. **`divergence_curl_eq_zero`**: ∇·(∇×F) = 0. Requires splitting `fderiv` of
   differences via `fderiv_sub` with differentiability threading from C².

3. **`curl_curl_eq_grad_div_sub_laplacian`**: ∇×(∇×F) = ∇(∇·F) − ∇²F. Tedious
   component-by-component expansion using symmetry of mixed partials.

4. **`curl_add`**: Curl distributes over addition. Follows from `fderiv_add`.

5. **`curl_const_mul`**: Curl distributes over scalar multiplication.
   Follows from `fderiv_const_smul`.

All five are mathematically straightforward consequences of `fderiv` linearity
and symmetry. The challenge is purely in threading Lean's differentiability
hypotheses through the component-wise proofs.
-/

end MaxwellWave
