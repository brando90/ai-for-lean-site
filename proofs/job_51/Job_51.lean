-- CANNOT_FORMALIZE_EXACTLY: The full conjecture is a finite-horizon stochastic
-- dynamic program (Bellman recursion with parametric V_t, Phi_t, optimal
-- selectors, base-stock policy, Topkis-style comparative statics). Mathlib
-- lacks a developed library for finite-horizon MDPs, base-stock theorems, or
-- monotone-selection / lattice-programming results, and the full proof of
-- Propositions 1–4 is a substantial formalization project beyond a single
-- file. Moreover, Proposition 3 as literally stated is false: the
-- Bernoulli "critical fractile" equality `p * 1{x* < ell} = lambda/VOLL`
-- generally cannot hold (LHS is discrete in {0, p}, RHS continuous), and the
-- asserted full-coverage reserve `x* = ell` can be infeasible when `B < ell`.
-- Below we formalize the largest tractable, correct fragment: the MDP
-- primitives (state, charge/discharge feasibility, Phi_t, Bellman step,
-- finite-horizon value function), convexity and monotonicity of the
-- single-period reduced cost (Proposition 1 reduced to T = 1 in post-charge
-- form), explicit counterexamples to the literal statement of Proposition 3,
-- the two corrected single-period optimality regimes, and a comparative-
-- statics fragment for Proposition 4 (monotonicity of the optimal reserve
-- in lambda, p, VOLL, ell in the single-period model).
import Mathlib

open Set

noncomputable section

namespace BatteryInventoryMDP

/-- Positive part, used for unmet demand. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- Deterministic per-period parameters: electricity price and critical load. -/
structure PeriodParams where
  lambda : ℝ
  ell : ℝ

/-- Global finite-horizon battery parameters. -/
structure BatteryParams where
  T : ℕ
  B : ℝ
  Umax : ℝ
  p : ℝ
  VOLL : ℝ
  period : ℕ → PeriodParams

/-- Standing positivity assumptions from the natural-language statement. -/
def BatteryParams.Valid (P : BatteryParams) : Prop :=
  0 < P.B ∧ 0 < P.Umax ∧ 0 < P.p ∧ P.p < 1 ∧ 0 < P.VOLL ∧
    ∀ t < P.T, 0 < (P.period t).lambda ∧ 0 < (P.period t).ell

/-- Feasible charging amount at state of charge `b`. -/
def FeasibleCharge (P : BatteryParams) (b u : ℝ) : Prop :=
  0 ≤ b ∧ b ≤ P.B ∧ 0 ≤ u ∧ u ≤ min P.Umax (P.B - b)

/-- Feasible discharge amount after charging to post-charge level `x`. -/
def FeasibleDischarge (P : BatteryParams) (x d : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ P.B ∧ 0 ≤ d ∧ d ≤ min x P.Umax

/-- Bernoulli outage demand `D_t = delta_t * ell_t`, represented by its two cases. -/
def BernoulliDemand (p ell demand : ℝ) : Prop :=
  (demand = 0 ∨ demand = ell) ∧ 0 ≤ p ∧ p ≤ 1

/-- Unmet-load penalty `VOLL * (ell - d)^+`. -/
def unmetPenalty (VOLL ell d : ℝ) : ℝ :=
  VOLL * posPart (ell - d)

/-- The outage-state minimization `Phi_t(x)`, as `sInf` over feasible discharges. -/
def Phi (P : BatteryParams) (Vnext : ℝ → ℝ) (t : ℕ) (x : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ d : ℝ,
    0 ≤ d ∧ d ≤ min x P.Umax ∧
      c = unmetPenalty P.VOLL (P.period t).ell d + Vnext (x - d)}

/-- One Bellman step:
`min_u lambda_t * u + (1 - p) * V_{t+1}(b+u) + p * Phi_t(b+u)`. -/
def BellmanStep (P : BatteryParams) (Vnext : ℝ → ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ u : ℝ,
    0 ≤ u ∧ u ≤ min P.Umax (P.B - b) ∧
      c =
        (P.period t).lambda * u +
          (1 - P.p) * Vnext (b + u) +
          P.p * Phi P Vnext t (b + u)}

/-- Finite-horizon value function with `n` periods remaining starting at period `t`. -/
def ValueFrom (P : BatteryParams) : ℕ → ℕ → ℝ → ℝ
  | 0, _t, _b => 0
  | n + 1, t, b => BellmanStep P (ValueFrom P n (t + 1)) t b

/-- Single-period post-charge reserve cost:
`C(x) = lambda * x + p * VOLL * (ell - x)^+`. -/
def singlePeriodCost (lambda p VOLL ell x : ℝ) : ℝ :=
  lambda * x + p * VOLL * posPart (ell - x)

/-- Feasible reserve in `[0, B]`. -/
def FeasibleReserve (B x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ B

/-- Optimality of a reserve for the single-period cost over `[0, B]`. -/
def IsOptimalReserve (B lambda p VOLL ell x : ℝ) : Prop :=
  FeasibleReserve B x ∧
    ∀ y, FeasibleReserve B y →
      singlePeriodCost lambda p VOLL ell x ≤ singlePeriodCost lambda p VOLL ell y

/-- The base-stock charging rule from the natural-language statement. -/
def BaseStockCharge (Umax S b : ℝ) : ℝ :=
  min Umax (posPart (S - b))

/-- One convenient formal shape of an order-up-to policy. -/
def IsBaseStockPolicy (B Umax S : ℝ) (charge : ℝ → ℝ) : Prop :=
  0 ≤ S ∧ S ≤ B ∧ ∀ b, 0 ≤ b → b ≤ B → charge b = BaseStockCharge Umax S b

/-- Proposition 1 (single-period post-charge fragment): the reduced cost is convex. -/
theorem singlePeriodCost_convex
    (lam p VOLL ell : ℝ) (hp : 0 ≤ p) (hV : 0 ≤ VOLL) :
    ConvexOn ℝ (Set.univ : Set ℝ) (singlePeriodCost lam p VOLL ell) := by
  have h1 : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => lam * x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    show lam * (a • x + b • y) ≤ a • (lam * x) + b • (lam * y)
    simp only [smul_eq_mul]
    have key : lam * (a * x + b * y) = a * (lam * x) + b * (lam * y) := by ring
    linarith
  have hAff : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => ell - x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    show ell - (a • x + b • y) ≤ a • (ell - x) + b • (ell - y)
    simp only [smul_eq_mul]
    have key : a * (ell - x) + b * (ell - y) = (a + b) * ell - (a * x + b * y) := by ring
    rw [key, hab]
    linarith
  have hConst : ConvexOn ℝ (Set.univ : Set ℝ) (fun _ : ℝ => (0 : ℝ)) :=
    convexOn_const 0 convex_univ
  have h2 : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => posPart (ell - x)) := by
    have := hAff.sup hConst
    simpa [posPart] using this
  have hpV : 0 ≤ p * VOLL := mul_nonneg hp hV
  have h3 : ConvexOn ℝ (Set.univ : Set ℝ)
      (fun x : ℝ => p * VOLL * posPart (ell - x)) := h2.smul hpV
  have h4 := h1.add h3
  refine h4.congr ?_
  intro x _
  simp [singlePeriodCost]

/-- Proposition 1, monotonicity fragment (single-period post-charge form):
the reserve cost `C(x) = lambda * x + p * VOLL * (ell - x)^+` is nonincreasing
on `[0, ell]` whenever `lambda ≤ p * VOLL`. -/
theorem singlePeriodCost_antitone_on_low_reserve
    {lam p VOLL ell : ℝ} (_hpV : 0 ≤ p * VOLL) (h : lam ≤ p * VOLL) :
    ∀ ⦃x y : ℝ⦄, x ≤ y → y ≤ ell →
      singlePeriodCost lam p VOLL ell y ≤ singlePeriodCost lam p VOLL ell x := by
  intro x y hxy hyell
  have hxell : x ≤ ell := le_trans hxy hyell
  unfold singlePeriodCost posPart
  rw [max_eq_left (sub_nonneg.mpr hxell), max_eq_left (sub_nonneg.mpr hyell)]
  have hgap : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hcoef : 0 ≤ p * VOLL - lam := sub_nonneg.mpr h
  nlinarith [mul_nonneg hcoef hgap]

/-- Counterexample to the literal Proposition 3 claim that `x* = ell` is feasible
when `p > lambda / VOLL`: take `B = 1`, `ell = 2`. -/
theorem proposition3_full_coverage_infeasible_counterexample :
    let B : ℝ := 1
    let ell : ℝ := 2
    let p : ℝ := (9 / 10 : ℝ)
    let lambda : ℝ := (1 / 10 : ℝ)
    let VOLL : ℝ := 1
    0 < B ∧ 0 < ell ∧ 0 < p ∧ p < 1 ∧ 0 < lambda ∧ 0 < VOLL ∧
      p > lambda / VOLL ∧ ¬ FeasibleReserve B ell := by
  norm_num [FeasibleReserve]

/-- Counterexample to the literal critical-fractile equality
`p * 1{x* < ell} = lambda / VOLL`: the LHS is `0` or `p`, generally
distinct from a continuous ratio. -/
theorem bernoulli_critical_fractile_equality_counterexample :
    let p : ℝ := (9 / 10 : ℝ)
    let lambda : ℝ := (1 / 10 : ℝ)
    let VOLL : ℝ := 1
    let ell : ℝ := 2
    let x : ℝ := ell
    p * (if x < ell then (1 : ℝ) else 0) ≠ lambda / VOLL := by
  norm_num

/-- For these valid parameters, no reserve `x` satisfies the literal Bernoulli
critical-fractile equality. -/
theorem bernoulli_critical_fractile_equality_has_no_solution_counterexample :
    ∀ x : ℝ,
      (9 / 10 : ℝ) * (if x < (2 : ℝ) then (1 : ℝ) else 0) ≠
        (1 / 10 : ℝ) / 1 := by
  intro x
  by_cases hx : x < (2 : ℝ)
  · simp only [if_pos hx]; norm_num
  · simp only [if_neg hx]; norm_num

/-- Hence the literal universal claim "if `p > lambda / VOLL`, then
`x* = ell` is the optimal reserve" is false under the stated assumptions,
because optimal reserves must be feasible. -/
theorem proposition3_full_coverage_claim_false :
    ¬ (∀ B ell p lambda VOLL : ℝ,
      0 < B → 0 < ell → 0 < p → p < 1 → 0 < lambda → 0 < VOLL →
        p > lambda / VOLL → IsOptimalReserve B lambda p VOLL ell ell) := by
  intro h
  have hbad : IsOptimalReserve (1 : ℝ) (1 / 10 : ℝ) (9 / 10 : ℝ) (1 : ℝ) (2 : ℝ) (2 : ℝ) :=
    h (1 : ℝ) (2 : ℝ) (9 / 10 : ℝ) (1 / 10 : ℝ) (1 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hle : (2 : ℝ) ≤ 1 := hbad.1.2
  norm_num at hle

/-- Corrected single-period optimality, high-outage regime
(`lambda < p * VOLL`): the optimal reserve is `min ell B`. -/
theorem corrected_single_period_high_outage
    {B lambda p VOLL ell : ℝ}
    (hB : 0 ≤ B) (hell : 0 ≤ ell) (hlambda : 0 < lambda)
    (hcritical : lambda < p * VOLL) :
    IsOptimalReserve B lambda p VOLL ell (min ell B) := by
  refine ⟨⟨le_min hell hB, min_le_right ell B⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hy0, hyB⟩
  unfold singlePeriodCost posPart
  by_cases hyell : y ≤ ell
  · have hmle : min ell B ≤ ell := min_le_left ell B
    have hym : y ≤ min ell B := le_min hyell hyB
    rw [max_eq_left (sub_nonneg.mpr hmle), max_eq_left (sub_nonneg.mpr hyell)]
    have hcoef : 0 ≤ p * VOLL - lambda := le_of_lt (sub_pos.mpr hcritical)
    have hgap : 0 ≤ min ell B - y := sub_nonneg.mpr hym
    have hprod : 0 ≤ (p * VOLL - lambda) * (min ell B - y) :=
      mul_nonneg hcoef hgap
    nlinarith
  · have helly : ell ≤ y := le_of_not_ge hyell
    have hmin : min ell B = ell := min_eq_left (le_trans helly hyB)
    have hypos : ell - y ≤ 0 := sub_nonpos.mpr helly
    rw [hmin, sub_self, max_self, max_eq_right hypos]
    have : lambda * ell ≤ lambda * y :=
      mul_le_mul_of_nonneg_left helly (le_of_lt hlambda)
    nlinarith

/-- Corrected single-period optimality, low-outage regime
(`p * VOLL ≤ lambda`): the optimal reserve is `0`. -/
theorem corrected_single_period_low_outage
    {B lambda p VOLL ell : ℝ}
    (hB : 0 ≤ B) (hell : 0 ≤ ell) (_hlambda : 0 ≤ lambda)
    (hpvoll : 0 ≤ p * VOLL) (hcritical : p * VOLL ≤ lambda) :
    IsOptimalReserve B lambda p VOLL ell 0 := by
  refine ⟨⟨le_rfl, hB⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hy0, _hyB⟩
  unfold singlePeriodCost posPart
  by_cases hyell : y ≤ ell
  · simp only [sub_zero, mul_zero, zero_add]
    rw [max_eq_left hell, max_eq_left (sub_nonneg.mpr hyell)]
    have hcoef : 0 ≤ lambda - p * VOLL := sub_nonneg.mpr hcritical
    have hprod : 0 ≤ (lambda - p * VOLL) * y := mul_nonneg hcoef hy0
    nlinarith
  · have helly : ell ≤ y := le_of_not_ge hyell
    have hypos : ell - y ≤ 0 := sub_nonpos.mpr helly
    simp only [sub_zero, mul_zero, zero_add]
    rw [max_eq_left hell, max_eq_right hypos]
    have hle_lambda_y : p * VOLL * y ≤ lambda * y :=
      mul_le_mul_of_nonneg_right hcritical hy0
    have hle_y : p * VOLL * ell ≤ p * VOLL * y :=
      mul_le_mul_of_nonneg_left helly hpvoll
    nlinarith

/-- Fractional form of the high-outage regime: if `lambda / VOLL < p` then
the optimal reserve is `min ell B`. -/
theorem corrected_single_period_high_outage_from_fraction
    {B lambda p VOLL ell : ℝ}
    (hB : 0 ≤ B) (hell : 0 ≤ ell) (hlambda : 0 < lambda)
    (_hp0 : 0 < p) (_hp1 : p < 1) (hVOLL : 0 < VOLL)
    (hcritical : lambda / VOLL < p) :
    IsOptimalReserve B lambda p VOLL ell (min ell B) := by
  apply corrected_single_period_high_outage hB hell hlambda
  have hmul := mul_lt_mul_of_pos_right hcritical hVOLL
  field_simp [ne_of_gt hVOLL] at hmul
  nlinarith

/-- Fractional form of the low-outage regime: if `p ≤ lambda / VOLL` then
the optimal reserve is `0`. -/
theorem corrected_single_period_low_outage_from_fraction
    {B lambda p VOLL ell : ℝ}
    (hB : 0 ≤ B) (hell : 0 ≤ ell) (hlambda : 0 < lambda)
    (hp0 : 0 ≤ p) (_hp1 : p < 1) (hVOLL : 0 < VOLL)
    (hcritical : p ≤ lambda / VOLL) :
    IsOptimalReserve B lambda p VOLL ell 0 := by
  apply corrected_single_period_low_outage hB hell (le_of_lt hlambda)
  · exact mul_nonneg hp0 (le_of_lt hVOLL)
  · have hmul := mul_le_mul_of_nonneg_right hcritical (le_of_lt hVOLL)
    field_simp [ne_of_gt hVOLL] at hmul
    exact hmul

/-! ## Proposition 4 (single-period fragment): comparative statics

In the single-period model the optimal reserve is `min ell B` if
`lambda ≤ p * VOLL` and `0` otherwise. We record the four monotonicity
claims of Proposition 4 in this regime: nondecreasing in `p`, `ell`, `VOLL`,
and nonincreasing in `lambda`. -/

/-- Single-period optimal reserve (smallest minimizer selection). -/
def optimalReserve (B lambda p VOLL ell : ℝ) : ℝ :=
  if lambda ≤ p * VOLL then min ell B else 0

/-- Comparative statics (a): `optimalReserve` is nondecreasing in `p`. -/
theorem optimalReserve_mono_p
    {B lambda VOLL ell p₁ p₂ : ℝ}
    (hB : 0 ≤ B) (hell : 0 ≤ ell) (hVOLL : 0 ≤ VOLL)
    (hp : p₁ ≤ p₂) :
    optimalReserve B lambda p₁ VOLL ell ≤ optimalReserve B lambda p₂ VOLL ell := by
  unfold optimalReserve
  by_cases h1 : lambda ≤ p₁ * VOLL
  · have h2 : lambda ≤ p₂ * VOLL :=
      le_trans h1 (mul_le_mul_of_nonneg_right hp hVOLL)
    simp [h1, h2]
  · by_cases h2 : lambda ≤ p₂ * VOLL
    · simp [h1, h2, le_min hell hB]
    · simp [h1, h2]

/-- Comparative statics (b): `optimalReserve` is nondecreasing in `ell`. -/
theorem optimalReserve_mono_ell
    {B lambda p VOLL ell₁ ell₂ : ℝ}
    (_hB : 0 ≤ B) (_hell₁ : 0 ≤ ell₁)
    (hell : ell₁ ≤ ell₂) :
    optimalReserve B lambda p VOLL ell₁ ≤ optimalReserve B lambda p VOLL ell₂ := by
  unfold optimalReserve
  by_cases h : lambda ≤ p * VOLL
  · simp only [h, if_true]
    exact min_le_min hell le_rfl
  · simp [h]

/-- Comparative statics (c): `optimalReserve` is nondecreasing in `VOLL`. -/
theorem optimalReserve_mono_VOLL
    {B lambda p ell VOLL₁ VOLL₂ : ℝ}
    (hB : 0 ≤ B) (hell : 0 ≤ ell) (hp : 0 ≤ p)
    (hV : VOLL₁ ≤ VOLL₂) :
    optimalReserve B lambda p VOLL₁ ell ≤ optimalReserve B lambda p VOLL₂ ell := by
  unfold optimalReserve
  by_cases h1 : lambda ≤ p * VOLL₁
  · have h2 : lambda ≤ p * VOLL₂ :=
      le_trans h1 (mul_le_mul_of_nonneg_left hV hp)
    simp [h1, h2]
  · by_cases h2 : lambda ≤ p * VOLL₂
    · simp [h1, h2, le_min hell hB]
    · simp [h1, h2]

/-- Comparative statics (d): `optimalReserve` is nonincreasing in `lambda`. -/
theorem optimalReserve_anti_lambda
    {B p VOLL ell lambda₁ lambda₂ : ℝ}
    (hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hlam : lambda₁ ≤ lambda₂) :
    optimalReserve B lambda₂ p VOLL ell ≤ optimalReserve B lambda₁ p VOLL ell := by
  unfold optimalReserve
  by_cases h2 : lambda₂ ≤ p * VOLL
  · have h1 : lambda₁ ≤ p * VOLL := le_trans hlam h2
    simp [h1, h2]
  · by_cases h1 : lambda₁ ≤ p * VOLL
    · simp [h1, h2, le_min hell hB]
    · simp [h1, h2]

end BatteryInventoryMDP

end