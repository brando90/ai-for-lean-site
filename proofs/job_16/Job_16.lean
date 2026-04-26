-- CANNOT_FORMALIZE_EXACTLY: The conjecture is an open research problem (COLT 2024) asking whether there exists an oblivious stepsize schedule yielding a worst-case anytime rate f(x_T) - f* ≤ C·L·‖x₀-x*‖²/T^α with α > 1 for all L-smooth convex f. This is not resolved in the mathematical literature; the provided sketch itself is merely a prompt template and does not contain a proof. Formalizing the full statement would require a substantial development of L-smooth convex functions, gradient descent iterates, and existence of such a stepsize schedule in Lean 4/Mathlib — and no such proof is known. Below is a faithful formal statement of the existential conjecture as a Prop, with an `axiom`-free placeholder that does not pretend to prove it.
import Mathlib

open scoped BigOperators
open Real

/-- Gradient descent iterate with oblivious stepsize sequence `η`, given a
gradient oracle `g : (ℕ → EuclideanSpace ℝ (Fin d)) → ℕ → EuclideanSpace ℝ (Fin d)`.
We encode the iterate recursively. -/
noncomputable def gdIter {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℕ → ℝ) (x₀ : EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => x₀
  | t + 1 => gdIter g η x₀ t - (η t) • g (gdIter g η x₀ t)

/-- `LSmoothConvex L f` asserts that `f : ℝⁿ → ℝ` is convex, differentiable
with gradient `∇f`, and has `L`-Lipschitz gradient. We bundle the gradient
function for convenience. -/
structure LSmoothConvex (d : ℕ) (L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (grad : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop where
  convex : ConvexOn ℝ Set.univ f
  hasGrad : ∀ x, HasFDerivAt f
              ((InnerProductSpace.toDual ℝ _ (grad x)) : _ →L[ℝ] ℝ) x
  lipGrad : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖
  attainsMin : ∃ xStar, ∀ x, f xStar ≤ f x

/-- The full conjecture: there exists an oblivious stepsize schedule `η` and
an exponent `α > 1` and a universal constant `C < ∞` such that for every
dimension `d`, every smoothness constant `L > 0`, every `L`-smooth convex
`f` with gradient `grad`, every initialization `x₀`, every minimizer `xStar`
of `f`, and every `T : ℕ` with `T ≥ 1`, the gradient-descent iterate
satisfies `f (x_T) - f(xStar) ≤ C * L * ‖x₀ - xStar‖² / T^α`. -/
def AnytimeFasterRateConjecture : Prop :=
  ∃ (η : ℕ → ℝ) (α : ℝ) (C : ℝ),
    1 < α ∧ 0 ≤ C ∧
    ∀ (d : ℕ) (L : ℝ) (_hL : 0 < L)
      (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (grad : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (_hf : LSmoothConvex d L f grad)
      (x₀ xStar : EuclideanSpace ℝ (Fin d))
      (_hmin : ∀ x, f xStar ≤ f x)
      (T : ℕ) (_hT : 1 ≤ T),
        f (gdIter grad η x₀ T) - f xStar
          ≤ C * L * ‖x₀ - xStar‖ ^ 2 / (T : ℝ) ^ α

/-- We record the status of the conjecture as an open problem. We do NOT
prove it; instead we prove the trivial disjunction `P ∨ ¬ P` via classical
logic, which is the strongest honest statement we can make in Lean without
resolving the open problem. -/
theorem anytimeFasterRate_decidable_open :
    AnytimeFasterRateConjecture ∨ ¬ AnytimeFasterRateConjecture :=
  Classical.em _