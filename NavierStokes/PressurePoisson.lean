/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Pressure Poisson Equation

For incompressible Navier-Stokes, taking the divergence of the momentum
equation and using ∇·v = 0 yields an elliptic equation for the pressure:

  ∇²p = -ρ Σ_{i,j} (∂v_j/∂x_i)(∂v_i/∂x_j) + ∇·f

This determines the pressure field as a constraint enforcing incompressibility.
The viscous and temporal terms vanish because ∇·v = 0.
-/
import NavierStokes.Vorticity

noncomputable section

open scoped BigOperators

namespace NavierStokes

open MaxwellWave PlasmaEquations

/-! ## Pressure Poisson Equation -/

/-- **Pressure Poisson equation** for incompressible Navier-Stokes:

  ∇²p = -ρ Σ_{i,k} (∂v_k/∂x_i)(∂v_i/∂x_k) + ∇·f

Derivation: take ∂/∂x_k of momentum component k and sum over k.
The time derivative term vanishes (∂/∂t(∇·v) = 0 by div_time_commute),
the viscous term vanishes (∇²(∇·v) = 0 by Clairaut + incompressibility),
the pressure term gives -∇²p, the advective term gives the double sum
(by product rule, Clairaut, and incompressibility), and the force term
gives ∇·f. -/
theorem pressure_poisson {c : FluidConstants} (sys : IncompressibleNS c)
    (sm : NSSmoothness sys) (t : ℝ) (x : Vec3) :
    scalarLaplacian (sys.p t) x =
      -c.ρ * ∑ i : Fin 3, ∑ k : Fin 3,
        partialDerivComp (sys.v t) i k x * partialDerivComp (sys.v t) k i x
      + divergence (sys.f t) x := by
  -- Abbreviations for partial derivatives
  let d : Fin 3 → Fin 3 → ℝ := fun i k => partialDerivComp (sys.v t) i k x
  let dd : Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun a i k => fderiv ℝ (fun y => partialDerivComp (sys.v t) i k y) x (basisVec a)
  -- Clairaut symmetry: dd a i k = dd i a k
  have hcomm : ∀ a i k, dd a i k = dd i a k := by
    intro a i k
    simp only [dd, partialDerivComp]
    exact fderiv_apply_comm (fun y => sys.v t y k) ((sys.hv_smooth t) k) x
      (basisVec i) (basisVec a)
  -- Incompressibility at x: d 0 0 + d 1 1 + d 2 2 = 0
  have hinc : d 0 0 + d 1 1 + d 2 2 = 0 := by
    have h := sys.incompressibility t x
    simp only [divergence, partialDerivComp, Fin.sum_univ_three] at h
    exact h
  -- Differentiated incompressibility: ∀ a, dd a 0 0 + dd a 1 1 + dd a 2 2 = 0
  have hinc_d : ∀ a : Fin 3, dd a 0 0 + dd a 1 1 + dd a 2 2 = 0 := by
    intro a
    have hfn : (fun y => partialDerivComp (sys.v t) 0 0 y +
                         partialDerivComp (sys.v t) 1 1 y +
                         partialDerivComp (sys.v t) 2 2 y) = fun _ => (0 : ℝ) := by
      funext y
      have := sys.incompressibility t y
      simp only [divergence, Fin.sum_univ_three] at this
      linarith
    have hpd_diff : ∀ i : Fin 3,
        DifferentiableAt ℝ (fun y => partialDerivComp (sys.v t) i i y) x :=
      fun i => partialDerivComp_differentiable (sys.hv_smooth t) i i x
    -- fderiv of the sum = sum of fderivs
    have hfun_eq : (fun y => partialDerivComp (sys.v t) 0 0 y +
        partialDerivComp (sys.v t) 1 1 y + partialDerivComp (sys.v t) 2 2 y) =
        (((fun y => partialDerivComp (sys.v t) 0 0 y) +
          (fun y => partialDerivComp (sys.v t) 1 1 y)) +
          (fun y => partialDerivComp (sys.v t) 2 2 y)) := by
      ext y; simp [Pi.add_apply]
    have hzero : fderiv ℝ (fun y => partialDerivComp (sys.v t) 0 0 y +
        partialDerivComp (sys.v t) 1 1 y + partialDerivComp (sys.v t) 2 2 y) x = 0 := by
      rw [congrArg (fun f => fderiv ℝ f x) hfn]; simp
    rw [hfun_eq] at hzero
    have h := fderiv_add ((hpd_diff 0).add (hpd_diff 1)) (hpd_diff 2)
    have h' := fderiv_add (hpd_diff 0) (hpd_diff 1)
    have r1 := ContinuousLinearMap.ext_iff.mp h (basisVec a)
    have r2 := ContinuousLinearMap.ext_iff.mp h' (basisVec a)
    simp only [ContinuousLinearMap.add_apply] at r1 r2
    have hzero_a := ContinuousLinearMap.ext_iff.mp hzero (basisVec a)
    simp only [ContinuousLinearMap.zero_apply] at hzero_a
    rw [r1, r2] at hzero_a
    -- hzero_a: fderiv(pdcomp 0 0) + fderiv(pdcomp 1 1) + fderiv(pdcomp 2 2) = 0
    -- Goal: dd a 0 0 + dd a 1 1 + dd a 2 2 = 0 where dd unfolds to fderiv(pdcomp)
    -- These are defeq. Use `change` to align.
    change (fderiv ℝ (fun y => partialDerivComp (sys.v t) 0 0 y) x) (basisVec a) +
      (fderiv ℝ (fun y => partialDerivComp (sys.v t) 1 1 y) x) (basisVec a) +
      (fderiv ℝ (fun y => partialDerivComp (sys.v t) 2 2 y) x) (basisVec a) = 0
    linarith
  -- Differentiability
  have hdiff : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => sys.v t y k) x :=
    fun k => (sys.hv_smooth t).differentiableAt k x
  have hpd_diff : ∀ i k : Fin 3,
      DifferentiableAt ℝ (fun y => partialDerivComp (sys.v t) i k y) x :=
    fun i k => partialDerivComp_differentiable (sys.hv_smooth t) i k x
  -- Product rule: ∂/∂x_a(v_i * ∂v_k/∂x_i) = (∂v_i/∂x_a)(∂v_k/∂x_i) + v_i * ∂²v_k/∂x_a∂x_i
  have hprod_rule : ∀ a i k : Fin 3,
      fderiv ℝ (fun y => sys.v t y i * partialDerivComp (sys.v t) i k y) x (basisVec a) =
        d a i * d i k + sys.v t x i * dd a i k := by
    intro a i k
    have h := fderiv_mul (hdiff i) (hpd_diff i k)
    have key := ContinuousLinearMap.ext_iff.mp h (basisVec a)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] at key
    -- Bridge: (fun y => f y * g y) is defeq to (f * g) via Pi.mul
    show (fderiv ℝ ((fun y => sys.v t y i) * (fun y => partialDerivComp (sys.v t) i k y)) x)
        (basisVec a) = d a i * d i k + sys.v t x i * dd a i k
    rw [key]; simp only [d, dd, partialDerivComp]; ring

  -- === STRATEGY ===
  -- The momentum equation gives (as function equality):
  --   ∂p/∂x_k(y) = -ρ*matDeriv_k(y) + μ*(∇²v)_k(y) + f_k(y)
  -- Differentiating and summing:
  --   ∇²p = -ρ*(Σ_k fderiv(matDeriv_k) · e_k) + μ*(visc_div) + ∇·f
  -- We split matDeriv = timeDerivComp + advective and show:
  --   (a) advective divergence = Σ_k Σ_i d k i * d i k
  --   (b) time-derivative divergence = 0 (from NSSmoothness.div_time_commute)
  --   (c) viscous divergence = 0 (from Clairaut + incompressibility)
  -- Therefore: ∇²p = -ρ*(Σ d k i * d i k) + ∇·f

  -- Momentum as function equality:
  have hmom_fn : ∀ k : Fin 3, (fun y => partialDeriv (sys.p t) k y) =
      (fun y => -(c.ρ * materialDerivVector sys.v sys.v t y k) +
        c.μ * vectorLaplacian (sys.v t) y k + sys.f t y k) := by
    intro k; funext y; have := sys.momentum t y k; linarith

  -- Differentiability of advective terms
  have hdiff_adv : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun y => advectiveDerivVector (sys.v t) (sys.v t) y k) x := by
    intro k
    simp only [advectiveDerivVector, Fin.sum_univ_three]
    exact (((hdiff 0).mul (hpd_diff 0 k)).add ((hdiff 1).mul (hpd_diff 1 k))).add
      ((hdiff 2).mul (hpd_diff 2 k))

  -- Differentiability of timeDerivComp (derived from momentum eq.)
  have hdiff_td : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun y => timeDerivComp sys.v k t y) x := by
    intro k
    have hp_diff : DifferentiableAt ℝ (fun y => partialDeriv (sys.p t) k y) x := by
      simp only [partialDeriv]
      exact ((sys.hp_smooth t).fderiv_right (m := 1) (by norm_num) |>.differentiable (by simp)
        |>.differentiableAt).clm_apply (differentiableAt_const _)
    have hvl_diff : DifferentiableAt ℝ (fun y => vectorLaplacian (sys.v t) y k) x := by
      simp only [vectorLaplacian, Fin.sum_univ_three]
      have hpd2 : ∀ i : Fin 3,
          DifferentiableAt ℝ (fun y => partialDerivComp2 (sys.v t) i k y) x := by
        intro i
        simp only [partialDerivComp2, partialDerivComp]
        exact ((((sm.hv_C3 t k).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
          |>.fderiv_right (m := 1) (by norm_num)
          |>.differentiable (by simp) |>.differentiableAt).clm_apply
          (differentiableAt_const _))
      exact ((hpd2 0).add (hpd2 1)).add (hpd2 2)
    have hf_diff := (sys.hf_smooth t).differentiableAt k x
    have h_eq : (fun y => c.ρ * timeDerivComp sys.v k t y) =
        (fun y => -(partialDeriv (sys.p t) k y) + c.μ * vectorLaplacian (sys.v t) y k +
          sys.f t y k - c.ρ * advectiveDerivVector (sys.v t) (sys.v t) y k) := by
      funext y; have := sys.momentum t y k
      simp only [materialDerivVector] at this; linarith
    have hd : DifferentiableAt ℝ (fun y => c.ρ * timeDerivComp sys.v k t y) x := by
      rw [h_eq]
      exact ((hp_diff.neg.add (hvl_diff.const_mul _)).add hf_diff).sub (hdiff_adv k |>.const_mul _)
    have h_eq2 : (fun y => timeDerivComp sys.v k t y) =
        (fun y => (1 / c.ρ) * (c.ρ * timeDerivComp sys.v k t y)) := by
      ext y; field_simp [c.ρ_ne_zero]
    rw [h_eq2]; exact hd.const_mul _

  -- Differentiability of matDeriv components
  have hmd_diff : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun y => materialDerivVector sys.v sys.v t y k) x :=
    fun k => (hdiff_td k).add (hdiff_adv k)
  have hvl_diff : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun y => vectorLaplacian (sys.v t) y k) x := by
    intro k
    simp only [vectorLaplacian, Fin.sum_univ_three]
    have hpd2 : ∀ i : Fin 3,
        DifferentiableAt ℝ (fun y => partialDerivComp2 (sys.v t) i k y) x := by
      intro i; simp only [partialDerivComp2, partialDerivComp]
      exact ((((sm.hv_C3 t k).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
        |>.fderiv_right (m := 1) (by norm_num)
        |>.differentiable (by simp) |>.differentiableAt).clm_apply
        (differentiableAt_const _))
    exact ((hpd2 0).add (hpd2 1)).add (hpd2 2)
  have hf_diff : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => sys.f t y k) x :=
    fun k => (sys.hf_smooth t).differentiableAt k x

  -- (A) ∂²p/∂x_k² via momentum equation
  have hpd2_eq : ∀ k : Fin 3, partialDeriv2 (sys.p t) k x =
      -(c.ρ * fderiv ℝ (fun y => materialDerivVector sys.v sys.v t y k) x (basisVec k)) +
        c.μ * fderiv ℝ (fun y => vectorLaplacian (sys.v t) y k) x (basisVec k) +
        fderiv ℝ (fun y => sys.f t y k) x (basisVec k) := by
    intro k
    simp only [partialDeriv2, partialDeriv]
    have hmom_k := hmom_fn k; simp only [partialDeriv] at hmom_k
    rw [hmom_k]
    have h1 := hmd_diff k; have h2 := hvl_diff k; have h3 := hf_diff k
    -- Rewrite the function to smul form for fderiv_const_smul
    have hfn_eq1 : (fun y => -(c.ρ * materialDerivVector sys.v sys.v t y k)) =
        ((-c.ρ) • (fun y => materialDerivVector sys.v sys.v t y k)) := by
      funext y; simp [smul_eq_mul]
    have hfn_eq2 : (fun y => c.μ * vectorLaplacian (sys.v t) y k) =
        (c.μ • (fun y => vectorLaplacian (sys.v t) y k)) := by
      funext y; simp [smul_eq_mul]
    -- The function is ((-ρ) • md + μ • vl) + f
    -- which = ((fun y => -ρ * md y + μ * vl y) + f)
    have hfun_eq : (fun y => -(c.ρ * materialDerivVector sys.v sys.v t y k) +
        c.μ * vectorLaplacian (sys.v t) y k + sys.f t y k) =
        (((((-c.ρ) • (fun y => materialDerivVector sys.v sys.v t y k)) +
          (c.μ • (fun y => vectorLaplacian (sys.v t) y k))) +
          (fun y => sys.f t y k))) := by
      ext y; simp [Pi.add_apply, smul_eq_mul]
    rw [hfun_eq]
    have h_inner := fderiv_add ((h1.const_smul (-c.ρ)).add (h2.const_smul c.μ)) h3
    have h_inner' := fderiv_add (h1.const_smul (-c.ρ)) (h2.const_smul c.μ)
    have r := ContinuousLinearMap.ext_iff.mp h_inner (basisVec k)
    have r' := ContinuousLinearMap.ext_iff.mp h_inner' (basisVec k)
    simp only [ContinuousLinearMap.add_apply] at r r'
    rw [r, r']
    simp only [fderiv_const_smul h1, fderiv_const_smul h2,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

  -- (B) Sum to get ∇²p
  have hlapl_eq : scalarLaplacian (sys.p t) x =
      -(c.ρ * ∑ k : Fin 3, fderiv ℝ (fun y => materialDerivVector sys.v sys.v t y k) x (basisVec k)) +
        c.μ * ∑ k : Fin 3, fderiv ℝ (fun y => vectorLaplacian (sys.v t) y k) x (basisVec k) +
        ∑ k : Fin 3, fderiv ℝ (fun y => sys.f t y k) x (basisVec k) := by
    simp only [scalarLaplacian, Fin.sum_univ_three]
    rw [hpd2_eq 0, hpd2_eq 1, hpd2_eq 2]; ring

  -- (C) Split matDeriv = timeDerivComp + advective
  have hmd_split_sum :
      ∑ k : Fin 3, fderiv ℝ (fun y => materialDerivVector sys.v sys.v t y k) x (basisVec k) =
        ∑ k : Fin 3, fderiv ℝ (fun y => timeDerivComp sys.v k t y) x (basisVec k) +
        ∑ k : Fin 3, fderiv ℝ (fun y => advectiveDerivVector (sys.v t) (sys.v t) y k) x (basisVec k) := by
    simp only [Fin.sum_univ_three]
    have hsplit : ∀ k : Fin 3,
        fderiv ℝ (fun y => materialDerivVector sys.v sys.v t y k) x (basisVec k) =
          fderiv ℝ (fun y => timeDerivComp sys.v k t y) x (basisVec k) +
          fderiv ℝ (fun y => advectiveDerivVector (sys.v t) (sys.v t) y k) x (basisVec k) := by
      intro k
      have hfn : (fun y => materialDerivVector sys.v sys.v t y k) =
          ((fun y => timeDerivComp sys.v k t y) + (fun y => advectiveDerivVector (sys.v t) (sys.v t) y k)) := by
        ext y; simp [materialDerivVector, Pi.add_apply]
      rw [hfn]
      have h := ContinuousLinearMap.ext_iff.mp (fderiv_add (hdiff_td k) (hdiff_adv k)) (basisVec k)
      simp only [ContinuousLinearMap.add_apply] at h; exact h
    rw [hsplit 0, hsplit 1, hsplit 2]; ring

  -- (D) Time-derivative divergence = 0 (from NSSmoothness)
  have htd_div : ∑ k : Fin 3, fderiv ℝ (fun y => timeDerivComp sys.v k t y) x (basisVec k) = 0 :=
    sm.div_time_commute t x

  -- (E) Advective divergence = Σ_k Σ_i d k i * d i k
  have hadv_sum :
      ∑ k : Fin 3, fderiv ℝ (fun y => advectiveDerivVector (sys.v t) (sys.v t) y k) x (basisVec k) =
        ∑ k : Fin 3, ∑ i : Fin 3, d k i * d i k := by
    simp only [Fin.sum_univ_three]
    have hadv_fderiv : ∀ k : Fin 3,
        fderiv ℝ (fun y => advectiveDerivVector (sys.v t) (sys.v t) y k) x (basisVec k) =
          ∑ i : Fin 3, (d k i * d i k + sys.v t x i * dd k i k) := by
      intro k
      simp only [advectiveDerivVector, Fin.sum_univ_three]
      have hprod_diff : ∀ i : Fin 3,
          DifferentiableAt ℝ (fun y => sys.v t y i * partialDerivComp (sys.v t) i k y) x :=
        fun i => (hdiff i).mul (hpd_diff i k)
      have hfun_eq : (fun y => sys.v t y 0 * partialDerivComp (sys.v t) 0 k y +
          sys.v t y 1 * partialDerivComp (sys.v t) 1 k y +
          sys.v t y 2 * partialDerivComp (sys.v t) 2 k y) =
          (((fun y => sys.v t y 0 * partialDerivComp (sys.v t) 0 k y) +
            (fun y => sys.v t y 1 * partialDerivComp (sys.v t) 1 k y)) +
            (fun y => sys.v t y 2 * partialDerivComp (sys.v t) 2 k y)) := by
        ext y; simp [Pi.add_apply]
      rw [hfun_eq]
      have h := fderiv_add ((hprod_diff 0).add (hprod_diff 1)) (hprod_diff 2)
      have h' := fderiv_add (hprod_diff 0) (hprod_diff 1)
      have r1 := ContinuousLinearMap.ext_iff.mp h (basisVec k)
      have r2 := ContinuousLinearMap.ext_iff.mp h' (basisVec k)
      simp only [ContinuousLinearMap.add_apply] at r1 r2
      rw [r1, r2, hprod_rule k 0 k, hprod_rule k 1 k, hprod_rule k 2 k]
    rw [hadv_fderiv 0, hadv_fderiv 1, hadv_fderiv 2]
    simp only [Fin.sum_univ_three]
    -- Apply Clairaut to move second-derivative terms
    rw [hcomm 0 0 0, hcomm 0 1 0, hcomm 0 2 0,
        hcomm 1 0 1, hcomm 1 1 1, hcomm 1 2 1,
        hcomm 2 0 2, hcomm 2 1 2, hcomm 2 2 2]
    -- After Clairaut, second-derivative groups vanish by incompressibility:
    -- v_i * (dd i 0 0 + dd i 1 1 + dd i 2 2) = v_i * 0
    have h0 := hinc_d 0; have h1 := hinc_d 1; have h2 := hinc_d 2
    have w0 : sys.v t x 0 * (dd 0 0 0 + dd 0 1 1 + dd 0 2 2) = 0 := by rw [h0]; ring
    have w1 : sys.v t x 1 * (dd 1 0 0 + dd 1 1 1 + dd 1 2 2) = 0 := by rw [h1]; ring
    have w2 : sys.v t x 2 * (dd 2 0 0 + dd 2 1 1 + dd 2 2 2) = 0 := by rw [h2]; ring
    nlinarith [w0, w1, w2]

  -- (F) Viscous divergence = 0
  have hpd_c2 : ∀ a k : Fin 3,
      ContDiff ℝ 2 (fun y => partialDerivComp (sys.v t) a k y) := by
    intro a k
    simp only [partialDerivComp]
    exact ((sm.hv_C3 t k).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

  have hpd2_diff : ∀ i k : Fin 3,
      DifferentiableAt ℝ (fun y => partialDerivComp2 (sys.v t) i k y) x := by
    intro i k; simp only [partialDerivComp2, partialDerivComp]
    exact ((((sm.hv_C3 t k).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
      |>.fderiv_right (m := 1) (by norm_num)
      |>.differentiable (by simp) |>.differentiableAt).clm_apply
      (differentiableAt_const _))

  have h3clairaut : ∀ a i k : Fin 3,
      fderiv ℝ (fun y => partialDerivComp2 (sys.v t) i k y) x (basisVec a) =
        fderiv ℝ (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) a k z) y
          (basisVec i)) x (basisVec i) := by
    intro a i k
    simp only [partialDerivComp2]
    rw [fderiv_apply_comm (fun y => partialDerivComp (sys.v t) i k y) (hpd_c2 i k) x
      (basisVec i) (basisVec a)]
    have hfn_eq : (fun y => (fderiv ℝ (fun y => partialDerivComp (sys.v t) i k y) y) (basisVec a)) =
        (fun y => (fderiv ℝ (fun z => partialDerivComp (sys.v t) a k z) y) (basisVec i)) := by
      funext y
      exact fderiv_apply_comm (fun z => sys.v t z k) ((sm.hv_C3 t k).of_le (by norm_num)) y
        (basisVec i) (basisVec a)
    rw [hfn_eq]

  have hvisc_div :
      ∑ k : Fin 3, fderiv ℝ (fun y => vectorLaplacian (sys.v t) y k) x (basisVec k) = 0 := by
    simp only [Fin.sum_univ_three]
    have hvl_fderiv : ∀ a k : Fin 3,
        fderiv ℝ (fun y => vectorLaplacian (sys.v t) y k) x (basisVec a) =
          fderiv ℝ (fun y => partialDerivComp2 (sys.v t) 0 k y) x (basisVec a) +
          fderiv ℝ (fun y => partialDerivComp2 (sys.v t) 1 k y) x (basisVec a) +
          fderiv ℝ (fun y => partialDerivComp2 (sys.v t) 2 k y) x (basisVec a) := by
      intro a k
      simp only [vectorLaplacian, Fin.sum_univ_three]
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
    rw [hvl_fderiv 0 0, hvl_fderiv 1 1, hvl_fderiv 2 2]
    rw [h3clairaut 0 0 0, h3clairaut 0 1 0, h3clairaut 0 2 0,
        h3clairaut 1 0 1, h3clairaut 1 1 1, h3clairaut 1 2 1,
        h3clairaut 2 0 2, h3clairaut 2 1 2, h3clairaut 2 2 2]
    -- Group by i: for each i, Σ_k fderiv(pdcomp k k)(e_i)(x)(e_i) = 0
    have hdiv_zero_fn : ∀ i : Fin 3,
        (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) 0 0 z) y (basisVec i) +
                  fderiv ℝ (fun z => partialDerivComp (sys.v t) 1 1 z) y (basisVec i) +
                  fderiv ℝ (fun z => partialDerivComp (sys.v t) 2 2 z) y (basisVec i)) =
        fun _ => (0 : ℝ) := by
      intro i; funext y
      have hfn_zero : (fun z => partialDerivComp (sys.v t) 0 0 z +
                                partialDerivComp (sys.v t) 1 1 z +
                                partialDerivComp (sys.v t) 2 2 z) = fun _ => (0 : ℝ) := by
        funext z; have := sys.incompressibility t z
        simp only [divergence, Fin.sum_univ_three] at this; linarith
      have hpd_diff_y : ∀ j : Fin 3,
          DifferentiableAt ℝ (fun z => partialDerivComp (sys.v t) j j z) y :=
        fun j => (hpd_c2 j j).differentiable (by simp) |>.differentiableAt
      have hfun_eq_y : (fun z => partialDerivComp (sys.v t) 0 0 z +
          partialDerivComp (sys.v t) 1 1 z + partialDerivComp (sys.v t) 2 2 z) =
          (((fun z => partialDerivComp (sys.v t) 0 0 z) +
            (fun z => partialDerivComp (sys.v t) 1 1 z)) +
            (fun z => partialDerivComp (sys.v t) 2 2 z)) := by
        ext z; simp [Pi.add_apply]
      have hzero_y : fderiv ℝ (fun z => partialDerivComp (sys.v t) 0 0 z +
          partialDerivComp (sys.v t) 1 1 z + partialDerivComp (sys.v t) 2 2 z) y = 0 := by
        rw [congrArg (fun f => fderiv ℝ f y) hfn_zero]; simp
      rw [hfun_eq_y] at hzero_y
      have h1 := fderiv_add ((hpd_diff_y 0).add (hpd_diff_y 1)) (hpd_diff_y 2)
      have h2 := fderiv_add (hpd_diff_y 0) (hpd_diff_y 1)
      have r1 := ContinuousLinearMap.ext_iff.mp h1 (basisVec i)
      have r2 := ContinuousLinearMap.ext_iff.mp h2 (basisVec i)
      simp only [ContinuousLinearMap.add_apply] at r1 r2
      have hzero_a := ContinuousLinearMap.ext_iff.mp hzero_y (basisVec i)
      simp only [ContinuousLinearMap.zero_apply] at hzero_a
      rw [r1, r2] at hzero_a; linarith
    have hsd_diff : ∀ (a i : Fin 3),
        DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) a a z) y (basisVec i)) x := by
      intro a i
      exact (((hpd_c2 a a).fderiv_right (m := 1) (by norm_num)).differentiable
        (by simp) |>.differentiableAt).clm_apply (differentiableAt_const _)
    have hgroup : ∀ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) 0 0 z) y (basisVec i)) x (basisVec i) +
        fderiv ℝ (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) 1 1 z) y (basisVec i)) x (basisVec i) +
        fderiv ℝ (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) 2 2 z) y (basisVec i)) x (basisVec i) = 0 := by
      intro i
      have hfun_eq_i : (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) 0 0 z) y (basisVec i) +
          fderiv ℝ (fun z => partialDerivComp (sys.v t) 1 1 z) y (basisVec i) +
          fderiv ℝ (fun z => partialDerivComp (sys.v t) 2 2 z) y (basisVec i)) =
          (((fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) 0 0 z) y (basisVec i)) +
            (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) 1 1 z) y (basisVec i))) +
            (fun y => fderiv ℝ (fun z => partialDerivComp (sys.v t) 2 2 z) y (basisVec i))) := by
        ext y; simp [Pi.add_apply]
      have hzero := congrArg (fun f => fderiv ℝ f x) (hdiv_zero_fn i); simp at hzero
      rw [hfun_eq_i] at hzero
      have hsum := fderiv_add ((hsd_diff 0 i).add (hsd_diff 1 i)) (hsd_diff 2 i)
      have hsum' := fderiv_add (hsd_diff 0 i) (hsd_diff 1 i)
      have r1 := ContinuousLinearMap.ext_iff.mp hsum (basisVec i)
      have r2 := ContinuousLinearMap.ext_iff.mp hsum' (basisVec i)
      simp only [ContinuousLinearMap.add_apply] at r1 r2
      have hzero_a := ContinuousLinearMap.ext_iff.mp hzero (basisVec i)
      simp only [ContinuousLinearMap.zero_apply] at hzero_a
      rw [r1, r2] at hzero_a; linarith
    have h0 := hgroup 0; have h1 := hgroup 1; have h2 := hgroup 2
    linarith

  -- (G) Combine: ∇²p = -ρ*(td_div + adv_div) + μ*visc_div + ∇·f
  --            = -ρ*(0 + Σ d k i * d i k) + μ*0 + ∇·f
  --            = -ρ*Σ d k i * d i k + ∇·f
  rw [hlapl_eq, hmd_split_sum, htd_div, hadv_sum, hvisc_div]
  simp only [d, divergence, partialDerivComp, Fin.sum_univ_three]
  ring

end NavierStokes
