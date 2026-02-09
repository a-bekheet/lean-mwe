/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Vector Calculus Operators

Definitions of gradient, divergence, curl, and Laplacian for scalar and vector
fields on ℝ³, built atop Mathlib's `fderiv` (Fréchet derivative).
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped BigOperators

namespace MaxwellWave

abbrev Vec3 := Fin 3 → ℝ
abbrev ScalarField := Vec3 → ℝ
abbrev VectorField := Vec3 → Vec3
abbrev TDScalarField := ℝ → Vec3 → ℝ
abbrev TDVectorField := ℝ → Vec3 → Vec3

/-! ## Partial Derivatives -/

def basisVec (i : Fin 3) : Vec3 := Pi.single i 1

def partialDeriv (f : ScalarField) (i : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ f x (basisVec i)

def partialDerivComp (F : VectorField) (i j : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ (fun y => F y j) x (basisVec i)

def partialDeriv2 (f : ScalarField) (i : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ (fun y => partialDeriv f i y) x (basisVec i)

def partialDerivComp2 (F : VectorField) (i j : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ (fun y => partialDerivComp F i j y) x (basisVec i)

def timeDeriv (f : TDScalarField) (t : ℝ) (x : Vec3) : ℝ :=
  deriv (fun s => f s x) t

def timeDerivComp (F : TDVectorField) (j : Fin 3) (t : ℝ) (x : Vec3) : ℝ :=
  deriv (fun s => F s x j) t

def timeDeriv2 (f : TDScalarField) (t : ℝ) (x : Vec3) : ℝ :=
  deriv (fun s => timeDeriv f s x) t

def timeDerivComp2 (F : TDVectorField) (j : Fin 3) (t : ℝ) (x : Vec3) : ℝ :=
  deriv (fun s => timeDerivComp F j s x) t

/-! ## Vector Calculus Operators -/

def gradient (f : ScalarField) (x : Vec3) : Vec3 :=
  fun i => partialDeriv f i x

def divergence (F : VectorField) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, partialDerivComp F i i x

def curl (F : VectorField) (x : Vec3) : Vec3 := fun k =>
  match k with
  | ⟨0, _⟩ => partialDerivComp F 1 2 x - partialDerivComp F 2 1 x
  | ⟨1, _⟩ => partialDerivComp F 2 0 x - partialDerivComp F 0 2 x
  | ⟨2, _⟩ => partialDerivComp F 0 1 x - partialDerivComp F 1 0 x

def scalarLaplacian (f : ScalarField) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, partialDeriv2 f i x

def vectorLaplacian (F : VectorField) (x : Vec3) : Vec3 := fun j =>
  ∑ i : Fin 3, partialDerivComp2 F i j x

scoped notation "∇" => gradient
scoped notation "∇⬝" => divergence
scoped notation "∇×" => curl
scoped notation "∇²ₛ" => scalarLaplacian
scoped notation "∇²" => vectorLaplacian

/-! ## Smoothness Definitions -/

def IsC2Scalar (f : ScalarField) : Prop := ContDiff ℝ 2 f

def IsC2Vector (F : VectorField) : Prop :=
  ∀ j : Fin 3, ContDiff ℝ 2 (fun x => F x j)

/-! ## Fundamental Lemma: Symmetry of Mixed Partials

This is the bridge to Mathlib's `IsSymmSndFDerivAt`. The connection requires
showing that `fderiv ℝ (fun y => fderiv ℝ f y v) x w` equals
`(fderiv ℝ (fderiv ℝ f) x w) v`, which follows from the chain rule for
evaluation at a fixed vector (a continuous linear map). -/

/-- Symmetry of mixed second partial derivatives (Clairaut/Schwarz theorem).
    For C² functions: ∂²f/∂v∂w = ∂²f/∂w∂v.

    This connects our `fderiv`-based partial derivatives to Mathlib's
    `IsSymmSndFDerivAt` via the chain rule for CLM evaluation. -/
lemma fderiv_apply_comm (f : ScalarField) (hf : ContDiff ℝ 2 f) (x v w : Vec3) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
    fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  -- The key Mathlib result: C² implies symmetric second derivative
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp)
  -- fderiv ℝ f is differentiable (C² ⟹ fderiv is C¹ ⟹ differentiable)
  have hfderiv_c1 : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfderiv_c1.differentiable (by simp)).differentiableAt
  -- CLM apply-const: fderiv ℝ (fun y => c y v) x w = (fderiv ℝ c x w) v
  -- when c is differentiable and v is constant.
  -- Use fderiv_clm_apply with constant u:
  have hv_const : DifferentiableAt ℝ (fun _ : Vec3 => v) x := differentiableAt_const v
  have key_v := fderiv_clm_apply hdf hv_const
  have key_w := fderiv_clm_apply hdf (differentiableAt_const w)
  -- key_v: fderiv (fun y => fderiv f y v) x = (fderiv f x).comp (fderiv const_v x) + (fderiv (fderiv f) x).flip v
  -- Since fderiv of constant = 0: first term vanishes
  simp at key_v key_w
  -- Now key_v says: fderiv (fun y => fderiv f y v) x = (fderiv (fderiv f) x).flip v
  -- Applied to w: fderiv (fun y => fderiv f y v) x w = (fderiv (fderiv f) x).flip v w
  --            = fderiv (fderiv f) x w v
  -- Similarly for key_w with roles swapped.
  -- The symmetry hsymm gives: fderiv (fderiv f) x v w = fderiv (fderiv f) x w v
  rw [show (fun y => fderiv ℝ f y v) = fun y => (fderiv ℝ f y) v from rfl] at key_v
  rw [show (fun y => fderiv ℝ f y w) = fun y => (fderiv ℝ f y) w from rfl] at key_w
  -- Use the simplified key_v and key_w as CLM equalities, then apply to get ℝ values
  have := ContinuousLinearMap.ext_iff.mp key_v w
  have := ContinuousLinearMap.ext_iff.mp key_w v
  simp [ContinuousLinearMap.flip_apply] at *
  rw [‹fderiv ℝ (fun y => (fderiv ℝ f y) v) x w = _›,
      ‹fderiv ℝ (fun y => (fderiv ℝ f y) w) x v = _›]
  exact (hsymm v w).symm

/-! ## Vector Calculus Identities -/

/-- **Curl of gradient is zero**: ∇×(∇f) = 0.
    Each component is ∂ᵢ∂ⱼf − ∂ⱼ∂ᵢf = 0 by symmetry of mixed partials. -/
theorem curl_gradient_eq_zero (f : ScalarField) (hf : IsC2Scalar f) (x : Vec3) :
    curl (gradient f) x = 0 := by
  funext k
  simp only [Pi.zero_apply]
  fin_cases k <;> simp only [curl, partialDerivComp, gradient, partialDeriv]
  · linarith [fderiv_apply_comm f hf x (basisVec 1) (basisVec 2)]
  · linarith [fderiv_apply_comm f hf x (basisVec 2) (basisVec 0)]
  · linarith [fderiv_apply_comm f hf x (basisVec 0) (basisVec 1)]

/-- **Divergence of curl is zero**: ∇·(∇×F) = 0.
    Expands to a sum of mixed partials that cancel pairwise. -/
theorem divergence_curl_eq_zero (F : VectorField) (hF : IsC2Vector F) (x : Vec3) :
    divergence (curl F) x = 0 := by
  let d : Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun i k j => fderiv ℝ (fun y => partialDerivComp F i j y) x (basisVec k)
  have hpdiff (i j : Fin 3) : DifferentiableAt ℝ (fun y => partialDerivComp F i j y) x := by
    dsimp [partialDerivComp]
    have hfderiv_c1 : ContDiff ℝ 1 (fderiv ℝ (fun z => F z j)) :=
      (hF j).fderiv_right (by norm_num)
    have hdf : DifferentiableAt ℝ (fderiv ℝ (fun z => F z j)) x :=
      (hfderiv_c1.differentiable (by simp)).differentiableAt
    simpa using hdf.clm_apply (differentiableAt_const (basisVec i))
  have hcomm (i k j : Fin 3) : d i k j = d k i j := by
    simpa [d, partialDerivComp] using
      (fderiv_apply_comm (fun y => F y j) (hF j) x (basisVec i) (basisVec k))
  have hsubApply (f g : Vec3 → ℝ) (hf : DifferentiableAt ℝ f x)
      (hg : DifferentiableAt ℝ g x) (v : Vec3) :
      fderiv ℝ (fun y => f y - g y) x v = fderiv ℝ f x v - fderiv ℝ g x v :=
    congrArg (fun L => L v) (fderiv_sub hf hg)
  have h0 : partialDerivComp (curl F) 0 0 x = d 1 0 2 - d 2 0 1 := by
    simpa [d, curl, partialDerivComp, Fin.isValue] using
      hsubApply (fun y => partialDerivComp F 1 2 y) (fun y => partialDerivComp F 2 1 y)
        (hpdiff 1 2) (hpdiff 2 1) (basisVec 0)
  have h1 : partialDerivComp (curl F) 1 1 x = d 2 1 0 - d 0 1 2 := by
    simpa [d, curl, partialDerivComp, Fin.isValue] using
      hsubApply (fun y => partialDerivComp F 2 0 y) (fun y => partialDerivComp F 0 2 y)
        (hpdiff 2 0) (hpdiff 0 2) (basisVec 1)
  have h2 : partialDerivComp (curl F) 2 2 x = d 0 2 1 - d 1 2 0 := by
    simpa [d, curl, partialDerivComp, Fin.isValue] using
      hsubApply (fun y => partialDerivComp F 0 1 y) (fun y => partialDerivComp F 1 0 y)
        (hpdiff 0 1) (hpdiff 1 0) (basisVec 2)
  calc
    divergence (curl F) x
        = partialDerivComp (curl F) 0 0 x + partialDerivComp (curl F) 1 1 x +
            partialDerivComp (curl F) 2 2 x := by
              simp [divergence, Fin.sum_univ_three]
    _ = (d 1 0 2 - d 2 0 1) + (d 2 1 0 - d 0 1 2) + (d 0 2 1 - d 1 2 0) := by
          rw [h0, h1, h2]
    _ = 0 := by
          rw [hcomm 1 0 2, hcomm 2 1 0, hcomm 0 2 1]
          ring

/-- **Vector identity**: ∇×(∇×F) = ∇(∇·F) − ∇²F.
    This is the critical identity for deriving wave equations.

    The proof requires expanding both sides into sums of second partial
    derivatives and using the symmetry of mixed partials. Each component
    involves 6+ terms that must be matched algebraically. -/
theorem curl_curl_eq_grad_div_sub_laplacian
    (F : VectorField) (hF : IsC2Vector F) (x : Vec3) :
    curl (curl F) x = fun j =>
      partialDeriv (divergence F) j x - vectorLaplacian F x j := by
  let d : Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun i k j => fderiv ℝ (fun y => partialDerivComp F i j y) x (basisVec k)
  have hpdiff (i j : Fin 3) : DifferentiableAt ℝ (fun y => partialDerivComp F i j y) x := by
    dsimp [partialDerivComp]
    have hfderiv_c1 : ContDiff ℝ 1 (fderiv ℝ (fun z => F z j)) :=
      (hF j).fderiv_right (by norm_num)
    have hdf : DifferentiableAt ℝ (fderiv ℝ (fun z => F z j)) x :=
      (hfderiv_c1.differentiable (by simp)).differentiableAt
    simpa using hdf.clm_apply (differentiableAt_const (basisVec i))
  have hcomm (i k j : Fin 3) : d i k j = d k i j := by
    simpa [d, partialDerivComp] using
      (fderiv_apply_comm (fun y => F y j) (hF j) x (basisVec i) (basisVec k))
  have hsubApply (f g : Vec3 → ℝ) (hf : DifferentiableAt ℝ f x)
      (hg : DifferentiableAt ℝ g x) (v : Vec3) :
      fderiv ℝ (fun y => f y - g y) x v = fderiv ℝ f x v - fderiv ℝ g x v :=
    congrArg (fun L => L v) (fderiv_sub hf hg)
  have hgraddiv (j : Fin 3) :
      partialDeriv (divergence F) j x =
        ∑ i : Fin 3, d i j i := by
    have hsum :
        fderiv ℝ (∑ i : Fin 3, partialDerivComp F i i) x =
          ∑ i : Fin 3, fderiv ℝ (partialDerivComp F i i) x := by
      simpa using
        (fderiv_sum (u := (Finset.univ : Finset (Fin 3)))
          (A := fun i => partialDerivComp F i i) (x := x) (h := fun i _ => hpdiff i i))
    calc
      partialDeriv (divergence F) j x
          = fderiv ℝ (∑ i : Fin 3, partialDerivComp F i i) x (basisVec j) := by
              rfl
      _ = (∑ i : Fin 3, fderiv ℝ (partialDerivComp F i i) x) (basisVec j) := by
            rw [hsum]
      _ = ∑ i : Fin 3, d i j i := by
            simp [d]
  funext j
  fin_cases j
  · have hA : partialDerivComp (curl F) 1 2 x = d 0 1 1 - d 1 1 0 := by
      simpa [d, curl, partialDerivComp, Fin.isValue] using
        hsubApply (fun y => partialDerivComp F 0 1 y) (fun y => partialDerivComp F 1 0 y)
          (hpdiff 0 1) (hpdiff 1 0) (basisVec 1)
    have hB : partialDerivComp (curl F) 2 1 x = d 2 2 0 - d 0 2 2 := by
      simpa [d, curl, partialDerivComp, Fin.isValue] using
        hsubApply (fun y => partialDerivComp F 2 0 y) (fun y => partialDerivComp F 0 2 y)
          (hpdiff 2 0) (hpdiff 0 2) (basisVec 2)
    have hL :
        curl (curl F) x 0 =
          (d 0 1 1 - d 1 1 0) - (d 2 2 0 - d 0 2 2) := by
      simp [curl, Fin.isValue, hA, hB]
    have hR :
        partialDeriv (divergence F) 0 x - vectorLaplacian F x 0 =
          (d 0 0 0 + d 1 0 1 + d 2 0 2) - (d 0 0 0 + d 1 1 0 + d 2 2 0) := by
      rw [hgraddiv 0]
      simp [vectorLaplacian, partialDerivComp2, Fin.sum_univ_three, d]
    have hGoal : curl (curl F) x 0 = partialDeriv (divergence F) 0 x - vectorLaplacian F x 0 := by
      rw [hL, hR, hcomm 0 1 1, hcomm 0 2 2]
      ring
    simpa using hGoal
  · have hA : partialDerivComp (curl F) 2 0 x = d 1 2 2 - d 2 2 1 := by
      simpa [d, curl, partialDerivComp, Fin.isValue] using
        hsubApply (fun y => partialDerivComp F 1 2 y) (fun y => partialDerivComp F 2 1 y)
          (hpdiff 1 2) (hpdiff 2 1) (basisVec 2)
    have hB : partialDerivComp (curl F) 0 2 x = d 0 0 1 - d 1 0 0 := by
      simpa [d, curl, partialDerivComp, Fin.isValue] using
        hsubApply (fun y => partialDerivComp F 0 1 y) (fun y => partialDerivComp F 1 0 y)
          (hpdiff 0 1) (hpdiff 1 0) (basisVec 0)
    have hL :
        curl (curl F) x 1 =
          (d 1 2 2 - d 2 2 1) - (d 0 0 1 - d 1 0 0) := by
      simp [curl, Fin.isValue, hA, hB]
    have hR :
        partialDeriv (divergence F) 1 x - vectorLaplacian F x 1 =
          (d 0 1 0 + d 1 1 1 + d 2 1 2) - (d 0 0 1 + d 1 1 1 + d 2 2 1) := by
      rw [hgraddiv 1]
      simp [vectorLaplacian, partialDerivComp2, Fin.sum_univ_three, d]
    have hGoal : curl (curl F) x 1 = partialDeriv (divergence F) 1 x - vectorLaplacian F x 1 := by
      rw [hL, hR, hcomm 1 2 2, hcomm 1 0 0]
      ring
    simpa using hGoal
  · have hA : partialDerivComp (curl F) 0 1 x = d 2 0 0 - d 0 0 2 := by
      simpa [d, curl, partialDerivComp, Fin.isValue] using
        hsubApply (fun y => partialDerivComp F 2 0 y) (fun y => partialDerivComp F 0 2 y)
          (hpdiff 2 0) (hpdiff 0 2) (basisVec 0)
    have hB : partialDerivComp (curl F) 1 0 x = d 1 1 2 - d 2 1 1 := by
      simpa [d, curl, partialDerivComp, Fin.isValue] using
        hsubApply (fun y => partialDerivComp F 1 2 y) (fun y => partialDerivComp F 2 1 y)
          (hpdiff 1 2) (hpdiff 2 1) (basisVec 1)
    have hL :
        curl (curl F) x 2 =
          (d 2 0 0 - d 0 0 2) - (d 1 1 2 - d 2 1 1) := by
      simp [curl, Fin.isValue, hA, hB]
    have hR :
        partialDeriv (divergence F) 2 x - vectorLaplacian F x 2 =
          (d 0 2 0 + d 1 2 1 + d 2 2 2) - (d 0 0 2 + d 1 1 2 + d 2 2 2) := by
      rw [hgraddiv 2]
      simp [vectorLaplacian, partialDerivComp2, Fin.sum_univ_three, d]
    have hGoal : curl (curl F) x 2 = partialDeriv (divergence F) 2 x - vectorLaplacian F x 2 := by
      rw [hL, hR, hcomm 2 0 0, hcomm 2 1 1]
      ring
    simpa using hGoal

/-! ## Curl Linearity Helpers -/

/-- C² vector field components are differentiable. -/
lemma IsC2Vector.differentiableAt {F : VectorField} (hF : IsC2Vector F)
    (j : Fin 3) (x : Vec3) : DifferentiableAt ℝ (fun y => F y j) x :=
  ((hF j).differentiable (by simp)).differentiableAt

/-- Curl distributes over negation: ∇×(−F) = −(∇×F). -/
theorem curl_neg (F : VectorField) (x : Vec3) (j : Fin 3) :
    curl (fun y k => -(F y k)) x j = -(curl F x j) := by
  fin_cases j <;>
    simp only [curl, partialDerivComp, Fin.isValue] <;>
    simp only [show (fun y => -(F y _)) = (-(fun y => F y _)) from rfl,
               fderiv_neg, ContinuousLinearMap.neg_apply] <;>
    ring

/-- Curl distributes over addition (from fderiv linearity). -/
theorem curl_add (F G : VectorField) (x : Vec3)
    (hF : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => F y j) x)
    (hG : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => G y j) x)
    (j : Fin 3) :
    curl (fun y k => F y k + G y k) x j = curl F x j + curl G x j := by
  fin_cases j <;>
    simp only [curl, partialDerivComp, Fin.isValue] <;>
    simp only [show ∀ i : Fin 3, (fun y => F y i + G y i) =
      ((fun y => F y i) + (fun y => G y i)) from fun i => rfl,
      fderiv_add (hF _) (hG _), ContinuousLinearMap.add_apply] <;>
    ring

/-- Curl distributes over scalar multiplication (from fderiv linearity). -/
theorem curl_const_mul (c : ℝ) (F : VectorField) (x : Vec3)
    (hF : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => F y j) x)
    (j : Fin 3) :
    curl (fun y k => c * F y k) x j = c * curl F x j := by
  fin_cases j <;>
    simp only [curl, partialDerivComp, Fin.isValue] <;>
    simp only [show ∀ i : Fin 3, (fun y => c * F y i) = (c • (fun y => F y i)) from
      fun i => rfl, fderiv_const_smul (hF _),
      ContinuousLinearMap.smul_apply, smul_eq_mul] <;>
    ring

end MaxwellWave
