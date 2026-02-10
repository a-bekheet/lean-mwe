/-
Copyright (c) 2025 Mohamed Bekheet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohamed Bekheet
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Curl

This module defines the curl of a vector field `Fin 3 → ℝ` using the Fréchet derivative.

## Main definitions

* `curl F x` is the curl of the vector field `F` at the point `x`.

## Main results

* `curl_apply`: the components of `curl F x` as explicit partial-derivative differences.
* `curl_zero`: `curl 0 x = 0`.
* `curl_neg`: `curl (-F) x = -curl F x`.
* `curl_add`: `curl (F + G) x = curl F x + curl G x`, given differentiability of components.
* `curl_sub`: `curl (F - G) x = curl F x - curl G x`, given differentiability of components.
* `curl_const_smul`: `curl (c • F) x = c • curl F x`, given differentiability of components.

## Notation

The scope `Curl` gives the notation `∇×` for `curl`.

## Tags

curl, vector calculus, cross product, Fréchet derivative
-/

noncomputable section

open Matrix

variable (F G : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) (c : ℝ)

/-- The curl of a vector field `F : (Fin 3 → ℝ) → (Fin 3 → ℝ)` at a point `x`,
defined as the vector of partial-derivative differences:

`curl F x = ![∂₁F₂ − ∂₂F₁, ∂₂F₀ − ∂₀F₂, ∂₀F₁ − ∂₁F₀]`

where `∂ᵢFⱼ` denotes `fderiv ℝ (fun y => F y j) x (Pi.single i 1)`. -/
def curl (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![fderiv ℝ (fun y => F y 2) x (Pi.single 1 1) -
      fderiv ℝ (fun y => F y 1) x (Pi.single 2 1),
    fderiv ℝ (fun y => F y 0) x (Pi.single 2 1) -
      fderiv ℝ (fun y => F y 2) x (Pi.single 0 1),
    fderiv ℝ (fun y => F y 1) x (Pi.single 0 1) -
      fderiv ℝ (fun y => F y 0) x (Pi.single 1 1)]

@[inherit_doc] scoped[Curl] notation "∇×" => curl

theorem curl_apply (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) :
    curl F x =
      ![fderiv ℝ (fun y => F y 2) x (Pi.single 1 1) -
          fderiv ℝ (fun y => F y 1) x (Pi.single 2 1),
        fderiv ℝ (fun y => F y 0) x (Pi.single 2 1) -
          fderiv ℝ (fun y => F y 2) x (Pi.single 0 1),
        fderiv ℝ (fun y => F y 1) x (Pi.single 0 1) -
          fderiv ℝ (fun y => F y 0) x (Pi.single 1 1)] :=
  rfl

@[simp]
theorem curl_zero (x : Fin 3 → ℝ) : curl 0 x = 0 := by
  simp [curl]

theorem curl_neg (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) :
    curl (-F) x = -curl F x := by
  have h : ∀ j : Fin 3, (fun y => (-F) y j) = -(fun y => F y j) := fun j => rfl
  simp only [curl, h, fderiv_neg, ContinuousLinearMap.neg_apply]
  ext i; fin_cases i <;> simp <;> ring

theorem curl_add (F G : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ)
    (hF : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => F y j) x)
    (hG : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => G y j) x) :
    curl (F + G) x = curl F x + curl G x := by
  have h : ∀ j : Fin 3, (fun y => (F + G) y j) =
      ((fun y => F y j) + (fun y => G y j)) := fun j => rfl
  simp only [curl, h, fderiv_add (hF _) (hG _), ContinuousLinearMap.add_apply]
  ext i; fin_cases i <;> simp <;> ring

theorem curl_sub (F G : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ)
    (hF : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => F y j) x)
    (hG : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => G y j) x) :
    curl (F - G) x = curl F x - curl G x := by
  have h : ∀ j : Fin 3, (fun y => (F - G) y j) =
      ((fun y => F y j) - (fun y => G y j)) := fun j => rfl
  simp only [curl, h, fderiv_sub (hF _) (hG _), ContinuousLinearMap.sub_apply]
  ext i; fin_cases i <;> simp <;> ring

theorem curl_const_smul (c : ℝ) (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ)
    (hF : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => F y j) x) :
    curl (c • F) x = c • curl F x := by
  have h : ∀ j : Fin 3, (fun y => (c • F) y j) = (c • (fun y => F y j)) := fun j => rfl
  simp only [curl, h, fderiv_const_smul (hF _), ContinuousLinearMap.smul_apply]
  ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

end
