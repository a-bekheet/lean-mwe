/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# MHD Equilibrium

Static MHD equilibrium: the force balance equation ∇p = J×B,
combined with Ampère's law ∇×B = μ₀J and ∇·B = 0.

Key consequences:
  - B · ∇p = 0 (B lies on pressure surfaces)
  - J · ∇p = 0 (J lies on pressure surfaces)
  - ∇p = (1/μ₀)(∇×B)×B (force balance in terms of B alone)
-/
import PlasmaEquations.SingleFluidMHD
import PlasmaEquations.CylindricalCoords

noncomputable section

open scoped BigOperators

namespace PlasmaEquations

open MaxwellWave

/-! ## Equilibrium structure -/

/-- Static MHD equilibrium.

In a time-independent equilibrium, the plasma is in force balance:
  ∇p = J×B
together with the magnetostatic equations ∇×B = μ₀J and ∇·B = 0. -/
structure MHDEquilibrium (c : MHDConstants) where
  /-- Equilibrium pressure p(x). -/
  p : ScalarField
  /-- Equilibrium magnetic field B(x). -/
  B : VectorField
  /-- Equilibrium current density J(x). -/
  J : VectorField
  /-- Force balance: (∇p)_j = (J×B)_j for each component. -/
  force_balance : ∀ x j,
    partialDeriv p j x = fieldCross J B x j
  /-- Ampère's law: (∇×B)_j = μ₀ J_j. -/
  ampere : ∀ x j, curl B x j = c.μ₀ * J x j
  /-- Solenoidal: ∇·B = 0. -/
  solenoidal : ∀ x, divergence B x = 0
  /-- B is C² smooth. -/
  hB_smooth : IsC2Vector B

namespace MHDEquilibrium

variable {c : MHDConstants} (eq : MHDEquilibrium c)

/-- B · ∇p = 0: the magnetic field is tangent to pressure surfaces.

Proof: B · ∇p = B · (J×B) = 0 by the vector identity a·(b×a) = 0. -/
theorem B_dot_grad_p_eq_zero (x : Vec3) :
    vec3Dot (eq.B x) (gradient eq.p x) = 0 := by
  have hgrad : gradient eq.p x = fun j => fieldCross eq.J eq.B x j := by
    funext j; exact eq.force_balance x j
  rw [hgrad]
  simp only [vec3Dot, dotProduct, fieldCross, vec3Cross, crossProduct]
  simp [Fin.sum_univ_three]
  ring

/-- J · ∇p = 0: the current density is tangent to pressure surfaces.

Proof: J · ∇p = J · (J×B) = 0 by the identity a·(a×b) = 0. -/
theorem J_dot_grad_p_eq_zero (x : Vec3) :
    vec3Dot (eq.J x) (gradient eq.p x) = 0 := by
  have hgrad : gradient eq.p x = fun j => fieldCross eq.J eq.B x j := by
    funext j
    exact eq.force_balance x j
  rw [hgrad]
  exact fieldDot_self_cross_eq_zero eq.J eq.B x

/-- Force balance in terms of B alone: ∇p = (1/μ₀)(∇×B)×B.

Substituting J = (1/μ₀)∇×B from Ampère's law into ∇p = J×B. -/
theorem force_balance_cross_form (x : Vec3) (j : Fin 3) :
    partialDeriv eq.p j x =
      fieldCross (fun y => fun i => (1 / c.μ₀) * curl eq.B y i) eq.B x j := by
  rw [eq.force_balance x j]
  simp only [fieldCross, vec3Cross, crossProduct]
  have hJ : ∀ i, eq.J x i = (1 / c.μ₀) * curl eq.B x i := by
    intro i
    have h := eq.ampere x i
    have hμ := c.μ₀_ne_zero
    field_simp; linarith
  fin_cases j <;> simp [Fin.isValue] <;> rw [hJ, hJ] <;> ring

/-- Magnetic pressure form of force balance:
    ∇p = (1/μ₀)((B·∇)B - ∇(B²/2)).
    Uses the vector identity `(∇×B)×B = (B·∇)B - ∇(|B|²/2)`.

    The proof computes `∂(B²/2)/∂x_j = Σ_k B_k ∂B_k/∂x_j` via the product rule,
    then verifies the algebraic identity component-by-component. -/
theorem magnetic_pressure_form (x : Vec3) (j : Fin 3) :
    partialDeriv eq.p j x =
      (1 / c.μ₀) * (advectiveDerivVector eq.B eq.B x j -
        partialDeriv (fun y => (1/2) * vec3Dot (eq.B y) (eq.B y)) j x) := by
  -- Abbreviations for partial derivatives: d i k = ∂B_k/∂x_i
  let d : Fin 3 → Fin 3 → ℝ := fun i k => partialDerivComp eq.B i k x
  -- Differentiability of B components
  have hBdiff : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => eq.B y k) x :=
    fun k => eq.hB_smooth.differentiableAt k x
  -- Step 1: LHS = (1/μ₀) * ((∇×B)×B)_j via force_balance + Ampère
  rw [eq.force_balance_cross_form x j]
  -- Step 2: Compute ∂(B²/2)/∂x_j using product rule
  -- Each term: fderiv((1/2) * B_k²) = B_k * ∂B_k/∂x_j
  have hBdiff : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => eq.B y k) x :=
    fun k => eq.hB_smooth.differentiableAt k x
  have hterm : ∀ k : Fin 3,
      fderiv ℝ (fun y => (1 : ℝ) / 2 * (eq.B y k * eq.B y k)) x (basisVec j) =
      eq.B x k * d j k := by
    intro k
    have hBk := hBdiff k
    -- Combine into one function equality: (1/2) * (B_k * B_k) = (1/2) • (B_k * B_k)
    have hfn : (fun y => (1 : ℝ) / 2 * (eq.B y k * eq.B y k)) =
               (((1 : ℝ) / 2) • ((fun y => eq.B y k) * (fun y => eq.B y k))) := by
      funext y; simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [hfn, congrArg (· (basisVec j)) (fderiv_const_smul (hBk.mul hBk) _),
        ContinuousLinearMap.smul_apply, smul_eq_mul,
        congrArg (· (basisVec j)) (fderiv_mul hBk hBk),
        ContinuousLinearMap.add_apply]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, d, partialDerivComp]
    ring
  have hgrad_Bsq : partialDeriv (fun y => (1/2 : ℝ) * vec3Dot (eq.B y) (eq.B y)) j x =
      ∑ k : Fin 3, eq.B x k * d j k := by
    simp only [partialDeriv, vec3Dot, dotProduct, Fin.sum_univ_three]
    -- Differentiability of each term
    have hterm_diff : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => (1 : ℝ) / 2 * (eq.B y k * eq.B y k)) x :=
      fun k => (differentiableAt_const _).mul ((hBdiff k).mul (hBdiff k))
    -- Split the function into three addends
    have hfn : (fun y => (1 : ℝ) / 2 * (eq.B y 0 * eq.B y 0 + eq.B y 1 * eq.B y 1 + eq.B y 2 * eq.B y 2)) =
               ((fun y => (1 : ℝ) / 2 * (eq.B y 0 * eq.B y 0)) +
                (fun y => (1 : ℝ) / 2 * (eq.B y 1 * eq.B y 1)) +
                (fun y => (1 : ℝ) / 2 * (eq.B y 2 * eq.B y 2))) := by
      funext y; simp [Pi.add_apply]; ring
    rw [hfn, congrArg (· (basisVec j)) (fderiv_add (hterm_diff 0 |>.add (hterm_diff 1)) (hterm_diff 2)),
        ContinuousLinearMap.add_apply,
        congrArg (· (basisVec j)) (fderiv_add (hterm_diff 0) (hterm_diff 1)),
        ContinuousLinearMap.add_apply,
        hterm 0, hterm 1, hterm 2]
  -- Step 3: Now show the algebraic identity
  rw [hgrad_Bsq]
  simp only [fieldCross, vec3Cross, crossProduct, curl, partialDerivComp, Fin.isValue,
             advectiveDerivVector, Fin.sum_univ_three, d]
  have hJ : ∀ i, eq.J x i = (1 / c.μ₀) * curl eq.B x i := by
    intro i; have h := eq.ampere x i; have hμ := c.μ₀_ne_zero
    field_simp; linarith
  fin_cases j <;> simp [Fin.isValue] <;> ring

end MHDEquilibrium

end PlasmaEquations
