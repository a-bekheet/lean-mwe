/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Vorticity and the Vorticity Transport Equation

The vorticity ω = ∇×v satisfies a transport equation obtained by taking
the curl of the Navier-Stokes momentum equation:

  ∂ω/∂t + (v·∇)ω = (ω·∇)v + ν∇²ω + (1/ρ)(∇×f)

Key steps:
  1. curl(∂v/∂t) = ∂ω/∂t (curl-time commutativity)
  2. curl((v·∇)v) = (v·∇)ω − (ω·∇)v (the hard identity)
  3. curl(∇p) = 0 (curl of gradient)
  4. curl(μ∇²v) = μ∇²ω (curl commutes with Laplacian for incompressible flow)
  5. curl(f) stays as is

The term (ω·∇)v is the **vortex stretching** term, unique to 3D.
-/
import NavierStokes.Equations

noncomputable section

open scoped BigOperators

namespace NavierStokes

open MaxwellWave PlasmaEquations

/-! ## Vorticity Definition -/

/-- Vorticity of a time-dependent velocity field: ω(t,x) = (∇×v)(t,x). -/
def vorticity (v : TDVectorField) (t : ℝ) (x : Vec3) : Vec3 :=
  curl (v t) x

/-! ## Basic Vorticity Identities -/

/-- Divergence of vorticity is zero: ∇·ω = 0.
    Follows directly from ∇·(∇×F) = 0. -/
theorem div_vorticity_eq_zero {c : FluidConstants} (sys : IncompressibleNS c)
    (t : ℝ) (x : Vec3) :
    divergence (vorticity sys.v t) x = 0 :=
  divergence_curl_eq_zero (sys.v t) (sys.hv_smooth t) x

/-- Curl of pressure gradient is zero: ∇×(∇p) = 0.
    Follows directly from ∇×(∇f) = 0. -/
theorem curl_pressure_gradient_eq_zero {c : FluidConstants} (sys : IncompressibleNS c)
    (t : ℝ) (x : Vec3) :
    curl (gradient (sys.p t)) x = 0 :=
  curl_gradient_eq_zero (sys.p t) (sys.hp_smooth t) x

/-! ## Smoothness Bundle -/

/-- Sufficient smoothness for the vorticity transport and pressure Poisson derivations.
    Bundles C³ regularity and time-space derivative commutativity. -/
structure NSSmoothness {c : FluidConstants} (sys : IncompressibleNS c) where
  /-- Velocity components are C³ (needed for curl of Laplacian). -/
  hv_C3 : ∀ t j, ContDiff ℝ 3 (fun x => sys.v t x j)
  /-- Curl and time derivative commute. -/
  curl_time_commute : ∀ t x j,
    timeDerivComp (fun s y => curl (sys.v s) y) j t x =
      curl (fun y k => timeDerivComp sys.v k t y) x j
  /-- Divergence and time derivative commute:
      Σ_k ∂/∂x_k(∂v_k/∂t) = 0, which follows from ∂/∂t(∇·v) = 0
      when spatial and temporal derivatives commute. -/
  div_time_commute : ∀ t x,
    ∑ k : Fin 3, fderiv ℝ (fun y => timeDerivComp sys.v k t y) x (basisVec k) = 0

/-! ## Curl of the Advective Term

The identity ∇×((v·∇)v) = (v·∇)ω − (ω·∇)v for divergence-free v
is the cornerstone of the vorticity equation. The proof is fully
component-wise: for each of the 3 vorticity components, we expand
both sides in terms of first and second partial derivatives, apply
Clairaut's theorem (symmetry of mixed partials) and the incompressibility
constraint (∂₀v₀ + ∂₁v₁ + ∂₂v₂ = 0), then close with `ring`. -/

/-- Auxiliary: partial derivatives of a C² vector field are differentiable. -/
lemma partialDerivComp_differentiable {F : VectorField} (hF : IsC2Vector F)
    (i j : Fin 3) (x : Vec3) :
    DifferentiableAt ℝ (fun y => partialDerivComp F i j y) x := by
  dsimp [partialDerivComp]
  have hfderiv_c1 : ContDiff ℝ 1 (fderiv ℝ (fun z => F z j)) :=
    (hF j).fderiv_right (by norm_num)
  have hdf : DifferentiableAt ℝ (fderiv ℝ (fun z => F z j)) x :=
    (hfderiv_c1.differentiable (by simp)).differentiableAt
  exact hdf.clm_apply (differentiableAt_const (basisVec i))

/-- ∇×((v·∇)v) = (v·∇)ω − (ω·∇)v  for divergence-free v.

Each component is proved by:
1. Introducing abbreviations for the 9 first partials d i k = ∂v_k/∂x_i
   and the 27 second partials dd a i k = ∂²v_k/∂x_a∂x_i
2. Using Clairaut: dd a i k = dd i a k
3. Using incompressibility: d 0 0 + d 1 1 + d 2 2 = 0
4. Expanding both sides, substituting, and closing with ring -/
theorem curl_advective_eq (v : VectorField) (hv : IsC2Vector v)
    (hdiv : ∀ x, divergence v x = 0) (x : Vec3) (j : Fin 3) :
    curl (fun y k => advectiveDerivVector v v y k) x j =
      advectiveDerivVector v (curl v) x j -
        advectiveDerivVector (curl v) v x j := by
  -- First partials: d i k = ∂v_k/∂x_i
  let d : Fin 3 → Fin 3 → ℝ := fun i k => partialDerivComp v i k x
  -- Second partials: dd a i k = ∂²v_k/(∂x_a ∂x_i)
  let dd : Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun a i k => fderiv ℝ (fun y => partialDerivComp v i k y) x (basisVec a)
  -- Clairaut: dd a i k = dd i a k
  have hcomm : ∀ a i k, dd a i k = dd i a k := by
    intro a i k
    simp only [dd, partialDerivComp]
    exact fderiv_apply_comm (fun y => v y k) (hv k) x (basisVec i) (basisVec a)
  -- Incompressibility: d 0 0 + d 1 1 + d 2 2 = 0
  have hinc : d 0 0 + d 1 1 + d 2 2 = 0 := by
    have h := hdiv x
    simp only [divergence, partialDerivComp, Fin.sum_univ_three] at h
    exact h
  -- Differentiability
  have hdiff : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => v y k) x :=
    fun k => hv.differentiableAt k x
  have hpd_diff : ∀ i k : Fin 3,
      DifferentiableAt ℝ (fun y => partialDerivComp v i k y) x :=
    fun i k => partialDerivComp_differentiable hv i k x
  -- Product rule: fderiv of (v_i * ∂v_k/∂x_i)
  have hprod_rule : ∀ a i k : Fin 3,
      fderiv ℝ (fun y => v y i * partialDerivComp v i k y) x (basisVec a) =
        d a i * d i k + v x i * dd a i k := by
    intro a i k
    have h := fderiv_mul (hdiff i) (hpd_diff i k)
    have key : (fderiv ℝ (fun y => v y i * partialDerivComp v i k y) x) (basisVec a) =
        v x i * (fderiv ℝ (fun y => partialDerivComp v i k y) x) (basisVec a) +
        partialDerivComp v i k x * (fderiv ℝ (fun y => v y i) x) (basisVec a) := by
      have := ContinuousLinearMap.ext_iff.mp h (basisVec a)
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul] at this
      exact this
    simp only [d, dd, partialDerivComp] at key ⊢; linarith
  -- fderiv of the advective derivative (sum of products)
  have hadv_fderiv : ∀ a k : Fin 3,
      fderiv ℝ (fun y => advectiveDerivVector v v y k) x (basisVec a) =
        (d a 0 * d 0 k + v x 0 * dd a 0 k) +
        (d a 1 * d 1 k + v x 1 * dd a 1 k) +
        (d a 2 * d 2 k + v x 2 * dd a 2 k) := by
    intro a k
    simp only [advectiveDerivVector, Fin.sum_univ_three]
    have hprod_diff : ∀ i : Fin 3,
        DifferentiableAt ℝ (fun y => v y i * partialDerivComp v i k y) x :=
      fun i => (hdiff i).mul (hpd_diff i k)
    -- Use congrArg to bridge fderiv of Pi.add and fderiv of lambda sum
    have hfun_eq : (fun y => v y 0 * partialDerivComp v 0 k y +
        v y 1 * partialDerivComp v 1 k y + v y 2 * partialDerivComp v 2 k y) =
        (((fun y => v y 0 * partialDerivComp v 0 k y) +
          (fun y => v y 1 * partialDerivComp v 1 k y)) +
          (fun y => v y 2 * partialDerivComp v 2 k y)) := by
      ext y; simp [Pi.add_apply]
    rw [hfun_eq]
    have h := fderiv_add ((hprod_diff 0).add (hprod_diff 1)) (hprod_diff 2)
    have h' := fderiv_add (hprod_diff 0) (hprod_diff 1)
    have r1 := ContinuousLinearMap.ext_iff.mp h (basisVec a)
    have r2 := ContinuousLinearMap.ext_iff.mp h' (basisVec a)
    simp only [ContinuousLinearMap.add_apply] at r1 r2
    rw [r1, r2, hprod_rule a 0 k, hprod_rule a 1 k, hprod_rule a 2 k]
  -- Helper: fderiv of curl component (fderiv of difference = difference of fderivs)
  have hcurl_pd : ∀ (a b c : Fin 3) (i : Fin 3),
      fderiv ℝ (fun y => partialDerivComp v b c y - partialDerivComp v a b y) x (basisVec i) =
        dd i b c - dd i a b := by
    intro a b c i
    have h := fderiv_sub (hpd_diff b c) (hpd_diff a b)
    -- h : fderiv (pdcomp_b_c - pdcomp_a_b) = fderiv(pdcomp_b_c) - fderiv(pdcomp_a_b)
    -- This is Pi.sub vs lambda sub; they're defeq. Use congrArg to evaluate at basisVec i.
    have := congrArg (fun L => L (basisVec i)) h
    simp only [ContinuousLinearMap.sub_apply] at this
    -- Now this : fderiv((pdcomp_b_c) - (pdcomp_a_b)) x (basisVec i) =
    --            fderiv(pdcomp_b_c) x (basisVec i) - fderiv(pdcomp_a_b) x (basisVec i)
    -- This should be defeq to the goal
    exact this
  -- Now prove component by component
  fin_cases j
  -- Component 0: (∇×((v·∇)v))_0 = ((v·∇)ω)_0 - ((ω·∇)v)_0
  · -- LHS = hadv_fderiv 1 2 - hadv_fderiv 2 1
    have hlhs : partialDerivComp (fun y k => advectiveDerivVector v v y k) 1 2 x -
        partialDerivComp (fun y k => advectiveDerivVector v v y k) 2 1 x =
        (d 1 0 * d 0 2 + v x 0 * dd 1 0 2 + (d 1 1 * d 1 2 + v x 1 * dd 1 1 2) +
          (d 1 2 * d 2 2 + v x 2 * dd 1 2 2)) -
        (d 2 0 * d 0 1 + v x 0 * dd 2 0 1 + (d 2 1 * d 1 1 + v x 1 * dd 2 1 1) +
          (d 2 2 * d 2 1 + v x 2 * dd 2 2 1)) := by
      have h1 := hadv_fderiv 1 2; have h2 := hadv_fderiv 2 1
      simp only [partialDerivComp] at h1 h2 ⊢; linarith
    -- RHS: advDeriv v (curl v) 0 - advDeriv (curl v) v 0
    -- advDeriv v (curl v) 0 = Σ_i v_i * ∂(curl v)_0/∂x_i
    -- (curl v)_0 = d 1 2 - d 2 1 (= ∂v₂/∂x₁ - ∂v₁/∂x₂)
    -- ∂(curl v)_0/∂x_i = dd(i,1,2) - dd(i,2,1) (using fderiv_sub)
    -- advDeriv (curl v) v 0 = Σ_i (curl v)_i * d(i,0)
    -- (curl v)_0 = d 1 2 - d 2 1
    -- (curl v)_1 = d 2 0 - d 0 2
    -- (curl v)_2 = d 0 1 - d 1 0
    have hrhs : advectiveDerivVector v (curl v) x 0 -
        advectiveDerivVector (curl v) v x 0 =
        (v x 0 * (dd 0 1 2 - dd 0 2 1) + v x 1 * (dd 1 1 2 - dd 1 2 1) +
          v x 2 * (dd 2 1 2 - dd 2 2 1)) -
        ((d 1 2 - d 2 1) * d 0 0 + (d 2 0 - d 0 2) * d 1 0 +
          (d 0 1 - d 1 0) * d 2 0) := by
      simp only [advectiveDerivVector, curl, Fin.sum_univ_three, Fin.isValue, partialDerivComp]
      have hc0 := hcurl_pd 2 1 2 0; have hc1 := hcurl_pd 2 1 2 1; have hc2 := hcurl_pd 2 1 2 2
      simp only [partialDerivComp] at hc0 hc1 hc2
      rw [hc0, hc1, hc2]
      simp only [dd, d, partialDerivComp]
    -- The main goal has curl unexpanded. Use linarith with hlhs and hrhs.
    have c102 := hcomm 1 0 2; have c122 := hcomm 1 2 2
    have c201 := hcomm 2 0 1; have c211 := hcomm 2 1 1
    have c012 := hcomm 0 1 2; have c021 := hcomm 0 2 1
    -- Expand curl to get partialDerivComp form, then convert
    show partialDerivComp _ 1 2 x - partialDerivComp _ 2 1 x =
      advectiveDerivVector v (curl v) x 0 - advectiveDerivVector (curl v) v x 0
    rw [hlhs, hrhs, c102, c122, c201, c211]
    have key : (d 1 2 - d 2 1) * (d 0 0 + d 1 1 + d 2 2) = 0 := by rw [hinc]; ring
    nlinarith [key]
  -- Component 1
  · have hlhs : partialDerivComp (fun y k => advectiveDerivVector v v y k) 2 0 x -
        partialDerivComp (fun y k => advectiveDerivVector v v y k) 0 2 x =
        (d 2 0 * d 0 0 + v x 0 * dd 2 0 0 + (d 2 1 * d 1 0 + v x 1 * dd 2 1 0) +
          (d 2 2 * d 2 0 + v x 2 * dd 2 2 0)) -
        (d 0 0 * d 0 2 + v x 0 * dd 0 0 2 + (d 0 1 * d 1 2 + v x 1 * dd 0 1 2) +
          (d 0 2 * d 2 2 + v x 2 * dd 0 2 2)) := by
      have h1 := hadv_fderiv 2 0; have h2 := hadv_fderiv 0 2
      simp only [partialDerivComp] at h1 h2 ⊢; linarith
    have hrhs : advectiveDerivVector v (curl v) x 1 -
        advectiveDerivVector (curl v) v x 1 =
        (v x 0 * (dd 0 2 0 - dd 0 0 2) + v x 1 * (dd 1 2 0 - dd 1 0 2) +
          v x 2 * (dd 2 2 0 - dd 2 0 2)) -
        ((d 1 2 - d 2 1) * d 0 1 + (d 2 0 - d 0 2) * d 1 1 +
          (d 0 1 - d 1 0) * d 2 1) := by
      simp only [advectiveDerivVector, curl, Fin.sum_univ_three, Fin.isValue, partialDerivComp]
      have hc0 := hcurl_pd 0 2 0 0; have hc1 := hcurl_pd 0 2 0 1; have hc2 := hcurl_pd 0 2 0 2
      simp only [partialDerivComp] at hc0 hc1 hc2
      rw [hc0, hc1, hc2]
      simp only [dd, d, partialDerivComp]
    show partialDerivComp _ 2 0 x - partialDerivComp _ 0 2 x =
      advectiveDerivVector v (curl v) x 1 - advectiveDerivVector (curl v) v x 1
    rw [hlhs, hrhs, hcomm 2 0 0, hcomm 2 1 0, hcomm 0 1 2, hcomm 0 2 2]
    have key : (d 2 0 - d 0 2) * (d 0 0 + d 1 1 + d 2 2) = 0 := by rw [hinc]; ring
    nlinarith [key]
  -- Component 2
  · have hlhs : partialDerivComp (fun y k => advectiveDerivVector v v y k) 0 1 x -
        partialDerivComp (fun y k => advectiveDerivVector v v y k) 1 0 x =
        (d 0 0 * d 0 1 + v x 0 * dd 0 0 1 + (d 0 1 * d 1 1 + v x 1 * dd 0 1 1) +
          (d 0 2 * d 2 1 + v x 2 * dd 0 2 1)) -
        (d 1 0 * d 0 0 + v x 0 * dd 1 0 0 + (d 1 1 * d 1 0 + v x 1 * dd 1 1 0) +
          (d 1 2 * d 2 0 + v x 2 * dd 1 2 0)) := by
      have h1 := hadv_fderiv 0 1; have h2 := hadv_fderiv 1 0
      simp only [partialDerivComp] at h1 h2 ⊢; linarith
    have hrhs : advectiveDerivVector v (curl v) x 2 -
        advectiveDerivVector (curl v) v x 2 =
        (v x 0 * (dd 0 0 1 - dd 0 1 0) + v x 1 * (dd 1 0 1 - dd 1 1 0) +
          v x 2 * (dd 2 0 1 - dd 2 1 0)) -
        ((d 1 2 - d 2 1) * d 0 2 + (d 2 0 - d 0 2) * d 1 2 +
          (d 0 1 - d 1 0) * d 2 2) := by
      simp only [advectiveDerivVector, curl, Fin.sum_univ_three, Fin.isValue, partialDerivComp]
      have hc0 := hcurl_pd 1 0 1 0; have hc1 := hcurl_pd 1 0 1 1; have hc2 := hcurl_pd 1 0 1 2
      simp only [partialDerivComp] at hc0 hc1 hc2
      rw [hc0, hc1, hc2]
      simp only [dd, d, partialDerivComp]
    show partialDerivComp _ 0 1 x - partialDerivComp _ 1 0 x =
      advectiveDerivVector v (curl v) x 2 - advectiveDerivVector (curl v) v x 2
    rw [hlhs, hrhs, hcomm 0 1 1, hcomm 0 2 1, hcomm 1 0 0, hcomm 1 2 0]
    have key : (d 0 1 - d 1 0) * (d 0 0 + d 1 1 + d 2 2) = 0 := by rw [hinc]; ring
    nlinarith [key]

/-! ## Curl Commutes with Laplacian for Incompressible Flow

For divergence-free v with sufficient smoothness, ∇×(∇²v) = ∇²(∇×v).
This uses Clairaut symmetry to interchange differentiation order at the
third-derivative level. -/

/-- ∇×(∇²v) = ∇²(∇×v) for sufficiently smooth incompressible velocity fields. -/
theorem curl_vectorLaplacian_eq {c : FluidConstants} (sys : IncompressibleNS c)
    (sm : NSSmoothness sys) (t : ℝ) (x : Vec3) (j : Fin 3) :
    curl (vectorLaplacian (sys.v t)) x j =
      vectorLaplacian (curl (sys.v t)) x j := by
  -- C² for partials (from C³ for components)
  have hpd_c2 : ∀ a k : Fin 3, ContDiff ℝ 2 (fun y => partialDerivComp (sys.v t) a k y) := by
    intro a k
    simp only [partialDerivComp]
    exact ((sm.hv_C3 t k).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  -- Differentiability of second partials
  have hpd2_diff : ∀ i k : Fin 3,
      DifferentiableAt ℝ (fun y => partialDerivComp2 (sys.v t) i k y) x := by
    intro i k; simp only [partialDerivComp2, partialDerivComp]
    exact ((((sm.hv_C3 t k).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
      |>.fderiv_right (m := 1) (by norm_num)
      |>.differentiable (by simp) |>.differentiableAt).clm_apply
      (differentiableAt_const _))
  -- Differentiability of first partials
  have hpd_diff : ∀ i k : Fin 3,
      DifferentiableAt ℝ (fun y => partialDerivComp (sys.v t) i k y) x :=
    fun i k => partialDerivComp_differentiable (sys.hv_smooth t) i k x
  -- Third-derivative Clairaut:
  -- fderiv(pd2 i k) x (e_a) = fderiv(fun y => fderiv(pdcomp a k) y (e_i)) x (e_i)
  have h3c : ∀ a i k : Fin 3,
      fderiv ℝ (fun y => partialDerivComp2 (sys.v t) i k y) x (basisVec a) =
        fderiv ℝ (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) a k z) y
          (basisVec i)) x (basisVec i) := by
    intro a i k; simp only [partialDerivComp2]
    rw [fderiv_apply_comm (fun y => partialDerivComp (sys.v t) i k y) (hpd_c2 i k) x
      (basisVec i) (basisVec a)]
    have hfn_eq : (fun y => (fderiv ℝ (fun y => partialDerivComp (sys.v t) i k y) y) (basisVec a)) =
        (fun y => (fderiv ℝ (fun z => partialDerivComp (sys.v t) a k z) y) (basisVec i)) := by
      funext y
      exact fderiv_apply_comm (fun z => sys.v t z k) ((sm.hv_C3 t k).of_le (by norm_num)) y
        (basisVec i) (basisVec a)
    rw [hfn_eq]
  -- Helper for fderiv of subtraction
  have hsubApply : ∀ (f g : Vec3 → ℝ) (hf : DifferentiableAt ℝ f x)
      (hg : DifferentiableAt ℝ g x) (w : Vec3),
      fderiv ℝ (fun y => f y - g y) x w = fderiv ℝ f x w - fderiv ℝ g x w :=
    fun f g hf hg w => congrArg (fun L => L w) (fderiv_sub hf hg)
  -- Differentiability of vectorLaplacian components
  have hvl_diff : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun y => vectorLaplacian (sys.v t) y k) x := by
    intro k; simp only [vectorLaplacian, Fin.sum_univ_three]
    exact ((hpd2_diff 0 k).add (hpd2_diff 1 k)).add (hpd2_diff 2 k)
  -- Differentiability of fderiv(pdcomp a k)(·)(e_i) for the RHS
  have hsd : ∀ (a i : Fin 3) (k : Fin 3),
      DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) a k z) y (basisVec i)) x := by
    intro a i k
    exact (((hpd_c2 a k).fderiv_right (m := 1) (by norm_num)).differentiable
      (by simp) |>.differentiableAt).clm_apply (differentiableAt_const _)
  -- Helper for expanding vectorLaplacian fderiv
  have hvl_expand : ∀ a k : Fin 3,
      fderiv ℝ (fun y => vectorLaplacian (sys.v t) y k) x (basisVec a) =
        fderiv ℝ (fun y => partialDerivComp2 (sys.v t) 0 k y) x (basisVec a) +
        fderiv ℝ (fun y => partialDerivComp2 (sys.v t) 1 k y) x (basisVec a) +
        fderiv ℝ (fun y => partialDerivComp2 (sys.v t) 2 k y) x (basisVec a) := by
    intro a k; simp only [vectorLaplacian, Fin.sum_univ_three]
    have hfun_eq : (fun y => partialDerivComp2 (sys.v t) 0 k y +
        partialDerivComp2 (sys.v t) 1 k y + partialDerivComp2 (sys.v t) 2 k y) =
        (((fun y => partialDerivComp2 (sys.v t) 0 k y) +
          (fun y => partialDerivComp2 (sys.v t) 1 k y)) +
          (fun y => partialDerivComp2 (sys.v t) 2 k y)) := by
      ext y; simp [Pi.add_apply]
    rw [hfun_eq]
    have h := fderiv_add ((hpd2_diff 0 k).add (hpd2_diff 1 k)) (hpd2_diff 2 k)
    have h' := fderiv_add (hpd2_diff 0 k) (hpd2_diff 1 k)
    have r1 := ContinuousLinearMap.ext_iff.mp h (basisVec a)
    have r2 := ContinuousLinearMap.ext_iff.mp h' (basisVec a)
    simp only [ContinuousLinearMap.add_apply] at r1 r2
    rw [r1, r2]
  -- Third derivative abbreviation
  let td : Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun a i k => fderiv ℝ (fun y =>
      fderiv ℝ (fun z => partialDerivComp (sys.v t) a k z) y (basisVec i)) x (basisVec i)
  -- LHS helper: curl(∇²v)_j = ∂/∂x_a(∇²v_b) - ∂/∂x_c(∇²v_d)
  -- Each ∂/∂x_a(∇²v_k) = Σ_i h3c(a,i,k)
  have hlhs_term : ∀ a k : Fin 3,
      fderiv ℝ (fun y => vectorLaplacian (sys.v t) y k) x (basisVec a) =
        td a 0 k + td a 1 k + td a 2 k := by
    intro a k; rw [hvl_expand a k, h3c a 0 k, h3c a 1 k, h3c a 2 k]
  -- RHS helper: ∇²(curl v)_j = Σ_i ∂²/∂x_i²(curl(v)_j)
  -- curl(v)_j = pdcomp(a, b) - pdcomp(c, d) for specific (a,b,c,d)
  -- So ∂/∂x_i(curl(v)_j) = fderiv(pdcomp(a,b))(e_i) - fderiv(pdcomp(c,d))(e_i) = td(a,i,b) - td(c,i,d)...
  -- Actually: fderiv(fun y => pdcomp(sys.v t) a b y - pdcomp(sys.v t) c d y) x (e_i)
  --   = fderiv(pdcomp a b) x (e_i) - fderiv(pdcomp c d) x (e_i)  [by hsubApply]
  -- and fderiv of that at second level: similarly splits by hsubApply again
  -- ∂²/∂x_i²(pdcomp a b - pdcomp c d) = td(a,i,b) - td(c,i,d)
  -- Wait, td(a,i,k) = fderiv(fderiv(pdcomp a k)(·)(e_i)) x (e_i)
  -- So ∂²/∂x_i²(curl_j) = td(a,i,b) - td(c,i,d) where curl_j = pdcomp(a,b) - pdcomp(c,d)
  -- But we need to be more careful: the second fderiv applies to
  --   fun y => fderiv(pdcomp a b)(y)(e_i) - fderiv(pdcomp c d)(y)(e_i)
  -- which by fderiv_sub splits
  have hrhs_term : ∀ a b c d i : Fin 3,
      fderiv ℝ (fun y =>
        fderiv ℝ (fun z => partialDerivComp (sys.v t) a b z -
          partialDerivComp (sys.v t) c d z) y (basisVec i)) x (basisVec i) =
        td a i b - td c i d := by
    intro a b c d i
    -- First, fderiv of (f - g) at inner level
    have hinner : ∀ y, fderiv ℝ (fun z => partialDerivComp (sys.v t) a b z -
        partialDerivComp (sys.v t) c d z) y =
        fderiv ℝ (fun z => partialDerivComp (sys.v t) a b z) y -
        fderiv ℝ (fun z => partialDerivComp (sys.v t) c d z) y := by
      intro y; exact fderiv_sub ((hpd_c2 a b).differentiable (by simp) |>.differentiableAt)
        ((hpd_c2 c d).differentiable (by simp) |>.differentiableAt)
    -- So (inner fderiv)(y)(e_i) = fderiv(pdcomp a b)(y)(e_i) - fderiv(pdcomp c d)(y)(e_i)
    have heval : ∀ y, fderiv ℝ (fun z => partialDerivComp (sys.v t) a b z -
        partialDerivComp (sys.v t) c d z) y (basisVec i) =
        fderiv ℝ (fun z => partialDerivComp (sys.v t) a b z) y (basisVec i) -
        fderiv ℝ (fun z => partialDerivComp (sys.v t) c d z) y (basisVec i) := by
      intro y; rw [hinner y]; simp [ContinuousLinearMap.sub_apply]
    simp_rw [heval]
    -- Now fderiv of (f - g) at outer level
    rw [hsubApply _ _ (hsd a i b) (hsd c i d)]
  -- Helper: expand LHS of curl(vectorLaplacian) for component (a1,k1) - (a2,k2)
  -- LHS: partialDerivComp (vectorLaplacian F) a k x = fderiv(fun y => vectorLaplacian F y k) x (e_a)
  --   = td(a,0,k) + td(a,1,k) + td(a,2,k)  (by hlhs_term)
  -- RHS: vectorLaplacian (curl F) x j = Σ_i partialDerivComp2 (curl F) i j x
  --   = Σ_i fderiv(fun y => fderiv(fun z => curl F z j) y (e_i)) x (e_i)
  --   = Σ_i (td(a,i,b) - td(c,i,d))  (by hrhs_term)  where curl_j = pd(a,b) - pd(c,d)

  -- The proof pattern for each component:
  -- 1. Unfold only curl on both sides to get partialDerivComp of vectorLaplacian (LHS)
  --    and vectorLaplacian of (pdcomp - pdcomp) (RHS)
  -- 2. Rewrite LHS with hlhs_term, RHS with hrhs_term
  -- 3. Close with ring
  -- Helper: vectorLaplacian of curl component j equals sum of hrhs_terms
  -- For j=0: curl(F)(y)(0) = pd(F,1,2,y) - pd(F,2,1,y)
  -- So ∇²(curl F)_0 = Σ_i pd2(curl F, i, 0) where each term involves
  --   fderiv(fderiv(curl(·)(0))(·)(e_i))(x)(e_i) = hrhs_term(1,2,2,1,i)
  -- We prove this via a function equality under the fderiv binders.
  have hcurl_comp0 : ∀ y, curl (sys.v t) y 0 =
      partialDerivComp (sys.v t) 1 2 y - partialDerivComp (sys.v t) 2 1 y := by
    intro y; rfl
  have hcurl_comp1 : ∀ y, curl (sys.v t) y 1 =
      partialDerivComp (sys.v t) 2 0 y - partialDerivComp (sys.v t) 0 2 y := by
    intro y; rfl
  have hcurl_comp2 : ∀ y, curl (sys.v t) y 2 =
      partialDerivComp (sys.v t) 0 1 y - partialDerivComp (sys.v t) 1 0 y := by
    intro y; rfl
  -- For the RHS, we need:
  -- partialDerivComp2 (curl F) i j x = fderiv(fderiv(curl(F)(·)(j))(·)(e_i))(x)(e_i)
  -- Since curl(F)(y)(j) = pd(a,b,y) - pd(c,d,y), this equals hrhs_term(a,b,c,d,i)
  have hrhs_vl : ∀ (a b c_1 d_1 : Fin 3) (j : Fin 3),
      (∀ y, curl (sys.v t) y j = partialDerivComp (sys.v t) a b y -
        partialDerivComp (sys.v t) c_1 d_1 y) →
      vectorLaplacian (curl (sys.v t)) x j =
        (td a 0 b - td c_1 0 d_1) + (td a 1 b - td c_1 1 d_1) + (td a 2 b - td c_1 2 d_1) := by
    intro a b c_1 d_1 j hcomp
    simp only [vectorLaplacian, Fin.sum_univ_three, partialDerivComp2]
    -- Now the goal has fderiv(fun y => partialDerivComp (curl F) i j y) terms
    -- partialDerivComp (curl F) i j y = fderiv(fun z => curl F z j) y (basisVec i)
    -- We need to rewrite curl F z j under the binders
    have hfn_eq : (fun y => curl (sys.v t) y j) =
        (fun y => partialDerivComp (sys.v t) a b y - partialDerivComp (sys.v t) c_1 d_1 y) := by
      funext y; exact hcomp y
    simp only [partialDerivComp]
    simp_rw [hfn_eq]
    rw [hrhs_term a b c_1 d_1 0, hrhs_term a b c_1 d_1 1, hrhs_term a b c_1 d_1 2]
  fin_cases j
  -- Component 0: curl(∇²v)_0 = ∇²(curl v)_0
  · show curl (vectorLaplacian (sys.v t)) x 0 = vectorLaplacian (curl (sys.v t)) x 0
    conv_lhs => rw [curl.eq_def]; simp only [Fin.isValue, partialDerivComp]
    rw [hlhs_term 1 2, hlhs_term 2 1, hrhs_vl 1 2 2 1 0 hcurl_comp0]
    ring
  -- Component 1: curl(∇²v)_1 = ∇²(curl v)_1
  · show curl (vectorLaplacian (sys.v t)) x 1 = vectorLaplacian (curl (sys.v t)) x 1
    conv_lhs => rw [curl.eq_def]; simp only [Fin.isValue, partialDerivComp]
    rw [hlhs_term 2 0, hlhs_term 0 2, hrhs_vl 2 0 0 2 1 hcurl_comp1]
    ring
  -- Component 2: curl(∇²v)_2 = ∇²(curl v)_2
  · show curl (vectorLaplacian (sys.v t)) x 2 = vectorLaplacian (curl (sys.v t)) x 2
    conv_lhs => rw [curl.eq_def]; simp only [Fin.isValue, partialDerivComp]
    rw [hlhs_term 0 1, hlhs_term 1 0, hrhs_vl 0 1 1 0 2 hcurl_comp2]
    ring

/-! ## Vorticity Transport Equation -/

/-- **Vorticity transport equation** for incompressible Navier-Stokes:

  ∂ω/∂t + (v·∇)ω = (ω·∇)v + ν∇²ω + (1/ρ)(∇×f)

where ω = ∇×v is the vorticity.

Derivation: take the curl of each term in the momentum equation
  ρ(∂v/∂t + (v·∇)v) = -∇p + μ∇²v + f
and use:
  - curl(∂v/∂t) = ∂ω/∂t
  - curl((v·∇)v) = (v·∇)ω - (ω·∇)v
  - curl(∇p) = 0
  - curl(∇²v) = ∇²ω (for incompressible flow)
  - curl(f) stays as is -/
theorem vorticity_transport {c : FluidConstants} (sys : IncompressibleNS c)
    (sm : NSSmoothness sys) (t : ℝ) (x : Vec3) (j : Fin 3) :
    timeDerivComp (fun s y => curl (sys.v s) y) j t x +
      advectiveDerivVector (sys.v t) (curl (sys.v t)) x j =
    advectiveDerivVector (curl (sys.v t)) (sys.v t) x j +
      c.ν * vectorLaplacian (curl (sys.v t)) x j +
      (1 / c.ρ) * curl (sys.f t) x j := by
  -- Step 1: Key intermediate results
  have hcurl_dt : curl (fun y k => timeDerivComp sys.v k t y) x j =
      timeDerivComp (fun s y => curl (sys.v s) y) j t x :=
    (sm.curl_time_commute t x j).symm
  have hcurl_adv : curl (fun y k => advectiveDerivVector (sys.v t) (sys.v t) y k) x j =
      advectiveDerivVector (sys.v t) (curl (sys.v t)) x j -
        advectiveDerivVector (curl (sys.v t)) (sys.v t) x j :=
    curl_advective_eq (sys.v t) (sys.hv_smooth t) (sys.incompressibility t) x j
  have hcurl_grad_p : curl (gradient (sys.p t)) x j = 0 :=
    congr_fun (curl_gradient_eq_zero (sys.p t) (sys.hp_smooth t) x) j
  have hcurl_lapl : curl (vectorLaplacian (sys.v t)) x j =
      vectorLaplacian (curl (sys.v t)) x j :=
    curl_vectorLaplacian_eq sys sm t x j

  -- Step 2: The momentum equation (per unit mass) as function equality
  have hmom_fn : ∀ k : Fin 3,
      (fun y => timeDerivComp sys.v k t y + advectiveDerivVector (sys.v t) (sys.v t) y k) =
      (fun y => -(1 / c.ρ) * partialDeriv (sys.p t) k y +
        c.ν * vectorLaplacian (sys.v t) y k + (1 / c.ρ) * sys.f t y k) := by
    intro k; funext y
    have := sys.momentum_per_unit_mass t y k
    simp only [materialDerivVector] at this; linarith

  -- Step 3: Differentiability for curl linearity
  have hv := sys.hv_smooth t
  have hdiff_v : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => sys.v t y k) x :=
    fun k => hv.differentiableAt k x
  have hdiff_td : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => timeDerivComp sys.v k t y) x := by
    intro k
    -- From momentum: td_k(y) = -(1/ρ)*∂p/∂x_k(y) + ν*(∇²v)_k(y) + (1/ρ)*f_k(y) - adv_k(y)
    -- All spatially differentiable. Use momentum fn equality.
    have hpd_diff : ∀ i j' : Fin 3,
        DifferentiableAt ℝ (fun y => partialDerivComp (sys.v t) i j' y) x :=
      fun i j' => partialDerivComp_differentiable (sys.hv_smooth t) i j' x
    have hadv_diff : DifferentiableAt ℝ (fun y => advectiveDerivVector (sys.v t) (sys.v t) y k) x := by
      simp only [advectiveDerivVector, Fin.sum_univ_three]
      exact (((hdiff_v 0).mul (hpd_diff 0 k)).add ((hdiff_v 1).mul (hpd_diff 1 k))).add
        ((hdiff_v 2).mul (hpd_diff 2 k))
    have hp_diff : DifferentiableAt ℝ (fun y => partialDeriv (sys.p t) k y) x := by
      simp only [partialDeriv]
      exact ((sys.hp_smooth t).fderiv_right (m := 1) (by norm_num) |>.differentiable (by simp)
        |>.differentiableAt).clm_apply (differentiableAt_const _)
    have hvl_diff : DifferentiableAt ℝ (fun y => vectorLaplacian (sys.v t) y k) x := by
      simp only [vectorLaplacian, Fin.sum_univ_three]
      have hpd2 : ∀ i : Fin 3,
          DifferentiableAt ℝ (fun y => partialDerivComp2 (sys.v t) i k y) x := by
        intro i; simp only [partialDerivComp2, partialDerivComp]
        -- Need: DiffAt (fun y => fderiv(fun z => fderiv(v_k)(z)(e_i)) y (e_i)) x
        -- From C³(v_k): fderiv(v_k) is C², so (fun y => fderiv(v_k)(y)(e_i)) is C²
        -- Then fderiv of that is C¹, hence differentiable, and clm_apply gives scalar
        exact ((((sm.hv_C3 t k).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
          |>.fderiv_right (m := 1) (by norm_num)
          |>.differentiable (by simp) |>.differentiableAt).clm_apply
          (differentiableAt_const _))
      exact ((hpd2 0).add (hpd2 1)).add (hpd2 2)
    have hf_diff := (sys.hf_smooth t).differentiableAt k x
    -- td_k + adv_k = RHS, td_k = RHS - adv_k
    have h_eq : (fun y => timeDerivComp sys.v k t y) =
        (fun y => (-(1 / c.ρ) * partialDeriv (sys.p t) k y +
          c.ν * vectorLaplacian (sys.v t) y k + (1 / c.ρ) * sys.f t y k) -
          advectiveDerivVector (sys.v t) (sys.v t) y k) := by
      funext y; have := congr_fun (hmom_fn k) y; linarith
    rw [h_eq]
    exact (((hp_diff.const_mul _).add (hvl_diff.const_mul _)).add (hf_diff.const_mul _)).sub hadv_diff

  have hdiff_adv : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun y => advectiveDerivVector (sys.v t) (sys.v t) y k) x := by
    intro k; simp only [advectiveDerivVector, Fin.sum_univ_three]
    have hpd_diff : ∀ i : Fin 3,
        DifferentiableAt ℝ (fun y => partialDerivComp (sys.v t) i k y) x :=
      fun i => partialDerivComp_differentiable (sys.hv_smooth t) i k x
    exact (((hdiff_v 0).mul (hpd_diff 0)).add ((hdiff_v 1).mul (hpd_diff 1))).add
      ((hdiff_v 2).mul (hpd_diff 2))
  have hdiff_grad : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => partialDeriv (sys.p t) k y) x := by
    intro k; simp only [partialDeriv]
    exact ((sys.hp_smooth t).fderiv_right (m := 1) (by norm_num) |>.differentiable (by simp)
      |>.differentiableAt).clm_apply (differentiableAt_const _)
  have hdiff_vl : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => vectorLaplacian (sys.v t) y k) x := by
    intro k; simp only [vectorLaplacian, Fin.sum_univ_three]
    have hpd2 : ∀ i : Fin 3,
        DifferentiableAt ℝ (fun y => partialDerivComp2 (sys.v t) i k y) x := by
      intro i; simp only [partialDerivComp2, partialDerivComp]
      exact ((((sm.hv_C3 t k).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
        |>.fderiv_right (m := 1) (by norm_num)
        |>.differentiable (by simp) |>.differentiableAt).clm_apply
        (differentiableAt_const _))
    exact ((hpd2 0).add (hpd2 1)).add (hpd2 2)
  have hdiff_f : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => sys.f t y k) x :=
    fun k => (sys.hf_smooth t).differentiableAt k x

  -- Step 4: curl of LHS = curl(timeDerivComp) + curl(advective)
  have hlhs_curl : curl (fun y k => timeDerivComp sys.v k t y +
      advectiveDerivVector (sys.v t) (sys.v t) y k) x j =
    curl (fun y k => timeDerivComp sys.v k t y) x j +
      curl (fun y k => advectiveDerivVector (sys.v t) (sys.v t) y k) x j :=
    curl_add _ _ x hdiff_td hdiff_adv j

  -- Step 5: curl of RHS using curl linearity
  -- The RHS function is: y k ↦ -(1/ρ)*∂p/∂x_k(y) + ν*(∇²v)_k(y) + (1/ρ)*f_k(y)
  -- We note that ∂p/∂x_k = gradient(p)(k), so the first term involves gradient
  -- curl(-(1/ρ)*∇p + ν*∇²v + (1/ρ)*f) = -(1/ρ)*curl(∇p) + ν*curl(∇²v) + (1/ρ)*curl(f)
  -- by curl linearity.
  -- The key issue is matching `partialDeriv` with `gradient` — they're definitionally equal.

  have hrhs_curl : curl (fun y k => -(1 / c.ρ) * partialDeriv (sys.p t) k y +
      c.ν * vectorLaplacian (sys.v t) y k + (1 / c.ρ) * sys.f t y k) x j =
    -(1 / c.ρ) * curl (gradient (sys.p t)) x j +
      c.ν * curl (vectorLaplacian (sys.v t)) x j +
      (1 / c.ρ) * curl (sys.f t) x j := by
    -- Split into three terms using curl_add twice and curl_const_mul
    have h1 : ∀ k : Fin 3, DifferentiableAt ℝ
        (fun y => -(1 / c.ρ) * partialDeriv (sys.p t) k y + c.ν * vectorLaplacian (sys.v t) y k) x :=
      fun k => ((hdiff_grad k).const_mul _).add ((hdiff_vl k).const_mul _)
    have h2 : ∀ k : Fin 3, DifferentiableAt ℝ
        (fun y => (1 / c.ρ) * sys.f t y k) x :=
      fun k => (hdiff_f k).const_mul _
    -- First split: (first two terms) + (1/ρ)*f
    have step1 := curl_add
      (fun y k => -(1 / c.ρ) * partialDeriv (sys.p t) k y + c.ν * vectorLaplacian (sys.v t) y k)
      (fun y k => (1 / c.ρ) * sys.f t y k) x h1 h2 j
    -- Second split: -(1/ρ)*∇p + ν*∇²v
    have h3 : ∀ k : Fin 3, DifferentiableAt ℝ
        (fun y => -(1 / c.ρ) * partialDeriv (sys.p t) k y) x :=
      fun k => (hdiff_grad k).const_mul _
    have h4 : ∀ k : Fin 3, DifferentiableAt ℝ
        (fun y => c.ν * vectorLaplacian (sys.v t) y k) x :=
      fun k => (hdiff_vl k).const_mul _
    have step2 := curl_add
      (fun y k => -(1 / c.ρ) * partialDeriv (sys.p t) k y)
      (fun y k => c.ν * vectorLaplacian (sys.v t) y k) x h3 h4 j
    -- Factor out constants
    -- Note: gradient p y k = partialDeriv (p) k y by definition
    have hgrad_eq : ∀ k : Fin 3,
        (fun y => -(1 / c.ρ) * partialDeriv (sys.p t) k y) =
        (fun y => -(1 / c.ρ) * gradient (sys.p t) y k) := by
      intro k; rfl
    -- step3: curl(c * gradient(p)) = c * curl(gradient(p))
    -- Note: gradient p y k = partialDeriv p k y, so the functions are defeq
    have step3 : curl (fun y k => -(1 / c.ρ) * partialDeriv (sys.p t) k y) x j =
        -(1 / c.ρ) * curl (gradient (sys.p t)) x j :=
      curl_const_mul (-(1 / c.ρ)) (gradient (sys.p t)) x (fun k => hdiff_grad k) j
    have step4 := curl_const_mul c.ν (vectorLaplacian (sys.v t)) x
      (fun k => hdiff_vl k) j
    have step5 := curl_const_mul (1 / c.ρ) (sys.f t) x hdiff_f j
    calc curl (fun y k => -(1 / c.ρ) * partialDeriv (sys.p t) k y +
              c.ν * vectorLaplacian (sys.v t) y k + (1 / c.ρ) * sys.f t y k) x j
        = curl (fun y k => -(1 / c.ρ) * partialDeriv (sys.p t) k y +
            c.ν * vectorLaplacian (sys.v t) y k) x j +
          curl (fun y k => (1 / c.ρ) * sys.f t y k) x j := step1
      _ = (curl (fun y k => -(1 / c.ρ) * partialDeriv (sys.p t) k y) x j +
          curl (fun y k => c.ν * vectorLaplacian (sys.v t) y k) x j) +
          curl (fun y k => (1 / c.ρ) * sys.f t y k) x j := by rw [step2]
      _ = (-(1 / c.ρ) * curl (gradient (sys.p t)) x j +
          c.ν * curl (vectorLaplacian (sys.v t)) x j) +
          (1 / c.ρ) * curl (sys.f t) x j := by rw [step3, step4, step5]
      _ = _ := by ring

  -- Step 6: Functions are equal (momentum), so their curls are equal
  have hcurl_eq : curl (fun y k => timeDerivComp sys.v k t y +
      advectiveDerivVector (sys.v t) (sys.v t) y k) x j =
    curl (fun y k => -(1 / c.ρ) * partialDeriv (sys.p t) k y +
      c.ν * vectorLaplacian (sys.v t) y k + (1 / c.ρ) * sys.f t y k) x j := by
    congr 2; funext y k; exact congr_fun (hmom_fn k) y

  -- Step 7: Combine and simplify
  -- From hcurl_eq + hlhs_curl + hrhs_curl:
  -- curl(td) + curl(adv) = -(1/ρ)*curl(∇p) + ν*curl(∇²v) + (1/ρ)*curl(f)
  -- Substitute: curl(∇p) = 0, curl(∇²v) = ∇²ω
  -- curl(td) = ∂ω/∂t (from hcurl_dt)
  -- curl(adv) = (v·∇)ω - (ω·∇)v (from hcurl_adv)
  -- So: ∂ω/∂t + (v·∇)ω - (ω·∇)v = 0 + ν*∇²ω + (1/ρ)*curl(f)
  -- Rearrange: ∂ω/∂t + (v·∇)ω = (ω·∇)v + ν*∇²ω + (1/ρ)*curl(f)
  have key := hcurl_eq
  rw [hlhs_curl] at key
  rw [hrhs_curl] at key
  rw [hcurl_grad_p, hcurl_lapl] at key
  -- key: curl(td)_j + curl(adv)_j = -(1/ρ)*0 + ν*∇²ω_j + (1/ρ)*curl(f)_j
  -- Substitute hcurl_dt and hcurl_adv
  rw [hcurl_dt, hcurl_adv] at key
  -- key: ∂ω/∂t_j + ((v·∇)ω_j - (ω·∇)v_j) = 0 + ν*∇²ω_j + (1/ρ)*curl(f)_j
  linarith

end NavierStokes
