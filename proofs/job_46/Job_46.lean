-- This file formalizes the COLT-2024 open problem on the anytime convergence
-- rate of gradient descent with oblivious stepsizes. The conjecture itself is
-- stated faithfully. Its resolution is OPEN: no proof or refutation is
-- currently known. We additionally prove the conditional algebraic
-- obstruction: any universal Drori–Teboulle-style `c/T` worst-case lower
-- bound on GD's anytime suboptimality is incompatible with a `C/T^α` upper
-- bound for `α > 1`. The Drori–Teboulle/PEP lower bound itself is not in
-- Mathlib, so it is taken as a hypothesis rather than an axiom; the file
-- therefore does NOT claim to resolve the open problem.
-- CANNOT_FORMALIZE_EXACTLY: the unconditional resolution of the conjecture
-- depends on the Drori–Teboulle/PEP worst-case lower bound which is not
-- available in Mathlib; the conjecture is stated faithfully and its
-- conditional refutation (modulo that lower bound, taken as a hypothesis)
-- is proved.
import Mathlib

noncomputable section

open Filter Topology

namespace AnytimeGD

/-- An `L`-smooth convex function on Euclidean space: convex, differentiable,
with `L`-Lipschitz gradient (where the gradient at `x` is the Riesz
representative of `fderiv ℝ f x`). -/
structure LSmoothConvex (d : ℕ) (L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  L_pos       : 0 < L
  convex      : ConvexOn ℝ Set.univ f
  diff        : Differentiable ℝ f
  lipGrad     : ∀ x y : EuclideanSpace ℝ (Fin d),
                  ‖(gradient f x) - (gradient f y)‖ ≤ L * ‖x - y‖

/-- `xstar` is a global minimizer of `f`. -/
def IsMinimizer {E : Type*} (f : E → ℝ) (xstar : E) : Prop :=
  ∀ x, f xstar ≤ f x

/-- Vanilla gradient descent iterates with oblivious stepsizes `η`:
`x 0 = x₀` and `x (t+1) = x t - η t • ∇f (x t)`. -/
def GDIter {d : ℕ} (η : ℕ → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0     => x₀
  | t + 1 => GDIter η f x₀ t - (η t) • gradient f (GDIter η f x₀ t)

/-- The faithful statement of the COLT-2024 anytime conjecture.

There exists a stepsize schedule `η : ℝ → ℕ → ℝ` (depending on `L` but not on
the horizon `T`), an exponent `α > 1`, and a universal constant `C ≥ 0` such
that, for every dimension `d`, every `L`-smooth convex `f` attaining its
minimum, every initialization `x₀`, every minimizer `x*`, and every
`T ∈ ℕ` with `1 ≤ T`, the gradient descent iterate `x_T` satisfies
`f(x_T) - f(x*) ≤ C · L · ‖x₀ - x*‖² / T^α`. -/
def AnytimeAcceleration : Prop :=
  ∃ (η : ℝ → ℕ → ℝ) (α C : ℝ),
    1 < α ∧ 0 ≤ C ∧
    ∀ (d : ℕ) (L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (x₀ xstar : EuclideanSpace ℝ (Fin d)),
      LSmoothConvex d L f → IsMinimizer f xstar →
      ∀ T : ℕ, 1 ≤ T →
        f (GDIter (η L) f x₀ T) - f xstar ≤
          C * L * ‖x₀ - xstar‖ ^ 2 / (T : ℝ) ^ α

/-- The general "best rate" form of the question: which positive rate
functions `r : ℕ → ℝ` admit an oblivious schedule whose worst-case anytime
suboptimality is at most `C · L · ‖x₀ - x*‖² / r(T)` simultaneously for
every `T ≥ 1`? -/
def AnytimeRateAchievable (r : ℕ → ℝ) : Prop :=
  ∃ (η : ℝ → ℕ → ℝ) (C : ℝ),
    0 ≤ C ∧ (∀ T : ℕ, 1 ≤ T → 0 < r T) ∧
    ∀ (d : ℕ) (L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (x₀ xstar : EuclideanSpace ℝ (Fin d)),
      LSmoothConvex d L f → IsMinimizer f xstar →
      ∀ T : ℕ, 1 ≤ T →
        f (GDIter (η L) f x₀ T) - f xstar ≤
          C * L * ‖x₀ - xstar‖ ^ 2 / r T

/-- A Drori–Teboulle-style universal `c/T` worst-case lower bound, packaged
as a hypothesis because the deep PEP lower-bound theorem is not available
in Mathlib. For each oblivious schedule `η`, there is a constant `c > 0`
such that for every horizon `T ≥ 1`, some `L`-smooth convex instance with a
nonzero distance to a minimizer realizes anytime suboptimality at least
`c · L · ‖x₀ - x*‖² / T`. -/
def UniversalOneOverTLowerBound : Prop :=
  ∀ (η : ℝ → ℕ → ℝ),
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℕ, 1 ≤ T →
        ∃ (d : ℕ) (L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
          (x₀ xstar : EuclideanSpace ℝ (Fin d)),
          LSmoothConvex d L f ∧ IsMinimizer f xstar ∧
          0 < ‖x₀ - xstar‖ ∧
          c * L * ‖x₀ - xstar‖ ^ 2 / (T : ℝ) ≤
            f (GDIter (η L) f x₀ T) - f xstar

/-- **Algebraic obstruction (proof-sketch core).** A universal lower bound
`c/T` (`c > 0`) and a universal upper bound `C/T^α` (`α > 1`, `C ≥ 0`) on the
same sequence are incompatible: the ratio `T^{α-1}` blows up, eventually
forcing `c · T^{α-1} ≤ C` for arbitrarily large `T`, a contradiction. -/
theorem one_over_T_lb_blocks_polynomial_ub
    {c C α : ℝ}
    (hc : 0 < c) (_hC : 0 ≤ C) (hα : 1 < α)
    (h : ∀ T : ℕ, 1 ≤ T → c / (T : ℝ) ≤ C / (T : ℝ) ^ α) :
    False := by
  have hα1 : 0 < α - 1 := sub_pos.mpr hα
  -- Build a natural number `T ≥ 1` with `(T : ℝ) ^ (α - 1) > C / c` directly
  -- from Archimedes, avoiding any reliance on a specific `tendsto_rpow_atTop`
  -- spelling.
  set M : ℝ := max 1 ((C / c) ^ (1 / (α - 1))) + 1 with hMdef
  have hM_ge_one : 1 ≤ M := by
    have : (1 : ℝ) ≤ max 1 ((C / c) ^ (1 / (α - 1))) := le_max_left _ _
    linarith
  obtain ⟨T, hTM⟩ := exists_nat_gt M
  have hT1 : 1 ≤ T := by
    have hgt : (1 : ℝ) < (T : ℝ) := lt_of_le_of_lt hM_ge_one hTM
    exact_mod_cast hgt.le
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  -- `(T : ℝ) > (C / c) ^ (1 / (α - 1))`
  have hT_gt_root : ((C / c) ^ (1 / (α - 1)) : ℝ) < (T : ℝ) := by
    have hle : ((C / c) ^ (1 / (α - 1)) : ℝ) ≤ M := by
      have : ((C / c) ^ (1 / (α - 1)) : ℝ) ≤
              max 1 ((C / c) ^ (1 / (α - 1))) := le_max_right _ _
      linarith
    exact lt_of_le_of_lt hle hTM
  -- Therefore `(T : ℝ) ^ (α - 1) > C / c`.
  have hTbig : C / c < (T : ℝ) ^ (α - 1) := by
    by_cases hCc : C / c ≤ 0
    · -- If `C/c ≤ 0`, then `(T : ℝ) ^ (α-1) > 0 ≥ C/c`.
      have hpos : 0 < (T : ℝ) ^ (α - 1) := Real.rpow_pos_of_pos hTpos _
      linarith
    · push_neg at hCc
      have hCcpos : 0 < C / c := hCc
      have hroot_pos : 0 < ((C / c) ^ (1 / (α - 1)) : ℝ) :=
        Real.rpow_pos_of_pos hCcpos _
      -- Raise both sides of `hT_gt_root` to the power `α - 1`.
      have hmono :
          ((C / c) ^ (1 / (α - 1)) : ℝ) ^ (α - 1) <
            (T : ℝ) ^ (α - 1) :=
        Real.rpow_lt_rpow hroot_pos.le hT_gt_root hα1
      -- Simplify the left side: `((C/c)^(1/(α-1)))^(α-1) = C/c`.
      have hsimp :
          ((C / c) ^ (1 / (α - 1)) : ℝ) ^ (α - 1) = C / c := by
        rw [← Real.rpow_mul hCcpos.le, one_div,
            inv_mul_cancel₀ (ne_of_gt hα1), Real.rpow_one]
      linarith [hmono, hsimp.symm.le, hsimp.le]
  have hTαpos : (0 : ℝ) < (T : ℝ) ^ α := Real.rpow_pos_of_pos hTpos _
  have hineq : c / (T : ℝ) ≤ C / (T : ℝ) ^ α := h T hT1
  have step : (c / (T : ℝ)) * (T : ℝ) ^ α = c * (T : ℝ) ^ (α - 1) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, Real.rpow_sub hTpos, Real.rpow_one]
  have hkey : c * (T : ℝ) ^ (α - 1) ≤ C := by
    rw [← step]
    calc (c / (T : ℝ)) * (T : ℝ) ^ α
        ≤ (C / (T : ℝ) ^ α) * (T : ℝ) ^ α :=
          mul_le_mul_of_nonneg_right hineq hTαpos.le
      _ = C := div_mul_cancel₀ C hTαpos.ne'
  have hgt : C < c * (T : ℝ) ^ (α - 1) := by
    have h1 : C / c * c < (T : ℝ) ^ (α - 1) * c :=
      mul_lt_mul_of_pos_right hTbig hc
    rw [div_mul_cancel₀ C hc.ne'] at h1
    linarith
  linarith

/-- **Conditional refutation.** If the worst-case anytime suboptimality of
gradient descent satisfies a Drori–Teboulle-style universal `c/T` lower
bound, then the anytime acceleration conjecture fails. We do *not* prove
the hypothesis — that is the heart of the open problem. The proof reduces
to the algebraic obstruction `one_over_T_lb_blocks_polynomial_ub`. -/
theorem not_anytime_acceleration_of_DT
    (hDT : UniversalOneOverTLowerBound) :
    ¬ AnytimeAcceleration := by
  rintro ⟨η, α, C, hα, hC, hUB⟩
  obtain ⟨c, hc, hLB⟩ := hDT η
  refine one_over_T_lb_blocks_polynomial_ub hc hC hα ?_
  intro T hT
  obtain ⟨d, L, f, x₀, xstar, hSmooth, hMin, hdist, hLBT⟩ := hLB T hT
  have hUBT := hUB d L f x₀ xstar hSmooth hMin T hT
  have hL : 0 < L := hSmooth.L_pos
  have hnormsq : 0 < ‖x₀ - xstar‖ ^ 2 := by positivity
  have hscale : 0 < L * ‖x₀ - xstar‖ ^ 2 := mul_pos hL hnormsq
  have hchain :
      c * L * ‖x₀ - xstar‖ ^ 2 / (T : ℝ) ≤
        C * L * ‖x₀ - xstar‖ ^ 2 / (T : ℝ) ^ α := hLBT.trans hUBT
  have h1 :
      c * L * ‖x₀ - xstar‖ ^ 2 / (T : ℝ)
        = (c / (T : ℝ)) * (L * ‖x₀ - xstar‖ ^ 2) := by ring
  have h2 :
      C * L * ‖x₀ - xstar‖ ^ 2 / (T : ℝ) ^ α
        = (C / (T : ℝ) ^ α) * (L * ‖x₀ - xstar‖ ^ 2) := by ring
  rw [h1, h2] at hchain
  exact le_of_mul_le_mul_right hchain hscale

/-- **Conditional refutation, general-rate form.** Under the same
Drori–Teboulle-style hypothesis, every achievable anytime rate `r(T)` is
at most linear in `T`: `r(T) ≤ K · T` for some `K ≥ 0` and all `T ≥ 1`.
This formalizes the "best rate" subquestion's conditional answer
`r(T) = O(T)` (i.e., no super-linear improvement is possible). -/
theorem rate_at_most_linear_of_DT
    (hDT : UniversalOneOverTLowerBound) {r : ℕ → ℝ}
    (hr : AnytimeRateAchievable r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℕ, 1 ≤ T → r T ≤ K * (T : ℝ) := by
  obtain ⟨η, C, hC, hrpos, hUB⟩ := hr
  obtain ⟨c, hc, hLB⟩ := hDT η
  refine ⟨C / c, div_nonneg hC hc.le, ?_⟩
  intro T hT
  obtain ⟨d, L, f, x₀, xstar, hSmooth, hMin, hdist, hLower⟩ := hLB T hT
  have hUpper := hUB d L f x₀ xstar hSmooth hMin T hT
  have hL : 0 < L := hSmooth.L_pos
  have hnormsq : 0 < ‖x₀ - xstar‖ ^ 2 := by positivity
  have hScale : 0 < L * ‖x₀ - xstar‖ ^ 2 := mul_pos hL hnormsq
  have hChain :
      c * L * ‖x₀ - xstar‖ ^ 2 / (T : ℝ) ≤
        C * L * ‖x₀ - xstar‖ ^ 2 / r T :=
    hLower.trans hUpper
  have h1 :
      c * L * ‖x₀ - xstar‖ ^ 2 / (T : ℝ)
        = (c / (T : ℝ)) * (L * ‖x₀ - xstar‖ ^ 2) := by ring
  have h2 :
      C * L * ‖x₀ - xstar‖ ^ 2 / r T
        = (C / r T) * (L * ‖x₀ - xstar‖ ^ 2) := by ring
  rw [h1, h2] at hChain
  have hClean : c / (T : ℝ) ≤ C / r T :=
    le_of_mul_le_mul_right hChain hScale
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hrTpos : 0 < r T := hrpos T hT
  have hcross : c * r T ≤ C * (T : ℝ) :=
    (div_le_div_iff₀ hTpos hrTpos).mp hClean
  have hdiv : r T ≤ (C * (T : ℝ)) / c := by
    rw [le_div_iff₀ hc]
    nlinarith [hcross]
  calc
    r T ≤ (C * (T : ℝ)) / c := hdiv
    _ = (C / c) * (T : ℝ) := by ring

end AnytimeGD