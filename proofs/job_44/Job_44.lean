-- CANNOT_FORMALIZE_EXACTLY: The exact conjecture quantifies over the sparse
-- Erdős--Rényi law `G(n, c/n)`, convergence in probability of random core sizes,
-- spectral radii of induced adjacency matrices, and a square-root critical
-- asymptotic for an order parameter `φ*(u) - φ_c ~ C √(u_c - u)`. These notions
-- are not presently available in Mathlib in a form that would let us formalize
-- the statement as written (no random-graph law `G(n, c/n)`, no `⟶_P`, no
-- critical asymptotics). The submitted NL "proof" is in fact a DISPROOF whose
-- engine is a deterministic isolated-star obstruction showing that the very
-- object `S*(u)` (defined as the *largest* subset / *maximal* fixed point of
-- `T_u`) is ill-posed in the critical star regime. The strongest exact theorem
-- we can prove in Lean 4 + Mathlib is precisely that deterministic obstruction:
-- on the star `K_{1,d+1}` with `β² d < 1 ≤ β² (d+1)` and `1 < u < 1/(1-β)`, the
-- substars obtained by deleting one leaf are Bonacich `u`-fixed points, but
-- their union is the inadmissible full star — hence no greatest Bonacich
-- `u`-core (and no greatest fixed point of `T_u`) exists. Such isolated stars
-- appear in `G(n, c/n)` with high probability, so this deterministic obstruction
-- is the load-bearing combinatorial step of the disproof.

import Mathlib

namespace BonacichSquareRootSingularity

open scoped BigOperators

noncomputable section

/-- Vertices of the star with `d + 1` leaves: `none` is the center, `some j` is leaf `j`. -/
abbrev StarVertex (d : ℕ) := Option (Fin (d + 1))

/-- A subset of vertices of the star with `d + 1` leaves. -/
abbrev StarSubset (d : ℕ) := Finset (StarVertex d)

/-- Number of leaves contained in a subset. -/
def leafCount {d : ℕ} (S : StarSubset d) : ℕ :=
  (S.erase (none : StarVertex d)).card

/-- Bonacich centrality of the center in an admissible `m`-leaf star. -/
def centerValue (β : ℝ) (m : ℕ) : ℝ :=
  (1 + β * (m : ℝ)) / (1 - β ^ 2 * (m : ℝ))

/-- Bonacich centrality of a leaf in an admissible `m`-leaf star. -/
def leafValue (β : ℝ) (m : ℕ) : ℝ :=
  (1 + β) / (1 - β ^ 2 * (m : ℝ))

/--
Explicit Bonacich centrality on induced subgraphs of a star.

If the subset contains the center and `m ≥ 1` leaves, the admissible regime is
`β^2 m < 1`; in that regime the center and leaf values are given by the standard
closed formulas. If `β^2 m ≥ 1`, the centrality is undefined (`none`). For edgeless
subgraphs, the value is `1` on every present vertex.
-/
noncomputable def bonacichCentrality {d : ℕ} (β : ℝ) (S : StarSubset d) :
    StarVertex d → Option ℝ
  | none =>
      if _hcenter : (none : StarVertex d) ∈ S then
        let m := leafCount S
        if _hm0 : m = 0 then
          some 1
        else if _hadm : β ^ 2 * (m : ℝ) < 1 then
          some (centerValue β m)
        else
          none
      else
        none
  | some j =>
      if _hj : (some j : StarVertex d) ∈ S then
        if _hcenter : (none : StarVertex d) ∈ S then
          let m := leafCount S
          if _hm0 : m = 0 then
            some 1
          else if _hadm : β ^ 2 * (m : ℝ) < 1 then
            some (leafValue β m)
          else
            none
        else
          some 1
      else
        none

/-- Bonacich-threshold feasibility for a subset. -/
def IsBonacichCandidate {d : ℕ} (β u : ℝ) (S : StarSubset d) : Prop :=
  ∀ v ∈ S, ∃ b : ℝ, bonacichCentrality β S v = some b ∧ u ≤ b

/-- The Bonacich operator `T_u(S) = {i ∈ S : b_i(β,S) ≥ u}`. -/
noncomputable def Tu {d : ℕ} (β u : ℝ) (S : StarSubset d) : StarSubset d :=
  S.filter (fun v => ∃ b : ℝ, bonacichCentrality β S v = some b ∧ u ≤ b)

/-- Fixed points of the Bonacich operator. -/
def IsFixedPoint {d : ℕ} (β u : ℝ) (S : StarSubset d) : Prop :=
  Tu β u S = S

/-- "Largest subset" version of the Bonacich `u`-core. -/
def IsGreatestBonacichUCore {d : ℕ} (β u : ℝ) (S : StarSubset d) : Prop :=
  IsBonacichCandidate β u S ∧
    ∀ T : StarSubset d, IsBonacichCandidate β u T → T ⊆ S

/-- "Greatest fixed point" version of the Bonacich `u`-core. -/
def IsGreatestFixedPoint {d : ℕ} (β u : ℝ) (S : StarSubset d) : Prop :=
  IsFixedPoint β u S ∧
    ∀ T : StarSubset d, IsFixedPoint β u T → T ⊆ S

theorem tu_eq_self_iff {d : ℕ} {β u : ℝ} {S : StarSubset d} :
    IsFixedPoint β u S ↔ IsBonacichCandidate β u S := by
  constructor
  · intro h v hv
    have hv' : v ∈ Tu β u S := by
      rw [h]
      exact hv
    exact (Finset.mem_filter.mp hv').2
  · intro h
    ext v
    constructor
    · intro hv
      exact (Finset.mem_filter.mp hv).1
    · intro hv
      exact Finset.mem_filter.mpr ⟨hv, h v hv⟩

theorem greatestCore_iff_greatestFixedPoint {d : ℕ} {β u : ℝ} {S : StarSubset d} :
    IsGreatestBonacichUCore β u S ↔ IsGreatestFixedPoint β u S := by
  constructor
  · rintro ⟨hS, hmax⟩
    refine ⟨(tu_eq_self_iff.2 hS), ?_⟩
    intro T hT
    exact hmax T (tu_eq_self_iff.1 hT)
  · rintro ⟨hS, hmax⟩
    refine ⟨(tu_eq_self_iff.1 hS), ?_⟩
    intro T hT
    exact hmax T (tu_eq_self_iff.2 hT)

/-- Remove one leaf from the full star. -/
def removeLeaf {d : ℕ} (j : Fin (d + 1)) : StarSubset d :=
  (Finset.univ : StarSubset d).erase (some j)

@[simp] theorem leafCount_univ {d : ℕ} :
    leafCount (Finset.univ : StarSubset d) = d + 1 := by
  simp [leafCount]

@[simp] theorem leafCount_removeLeaf {d : ℕ} (j : Fin (d + 1)) :
    leafCount (removeLeaf j : StarSubset d) = d := by
  simp [removeLeaf, leafCount]

@[simp] theorem center_mem_removeLeaf {d : ℕ} (j : Fin (d + 1)) :
    (none : StarVertex d) ∈ removeLeaf j := by
  simp [removeLeaf]

@[simp] theorem leaf_mem_removeLeaf {d : ℕ} {j k : Fin (d + 1)} :
    (some k : StarVertex d) ∈ removeLeaf j ↔ k ≠ j := by
  simp [removeLeaf]

theorem centerValue_ge_one_div {β : ℝ} {d : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hd : 1 ≤ d)
    (hadm : β ^ 2 * (d : ℝ) < 1) :
    1 / (1 - β) ≤ centerValue β d := by
  have hden1' : 1 - β ≠ 0 := by linarith
  have hden2' : 1 - β ^ 2 * (d : ℝ) ≠ 0 := by linarith
  have hdR : (1 : ℝ) ≤ d := by
    exact_mod_cast hd
  have hdm1 : 0 ≤ (d : ℝ) - 1 := by
    linarith
  have hden : 0 < (1 - β ^ 2 * (d : ℝ)) * (1 - β) := by
    have h1 : 0 < 1 - β ^ 2 * (d : ℝ) := by linarith
    have h2 : 0 < 1 - β := by linarith
    positivity
  have hnum : 0 ≤ β * ((d : ℝ) - 1) := by
    nlinarith [hβ0, hdm1]
  have haux : 0 ≤ β * ((d : ℝ) - 1) / ((1 - β ^ 2 * (d : ℝ)) * (1 - β)) := by
    exact div_nonneg hnum hden.le
  have hformula :
      (1 + β * (d : ℝ)) / (1 - β ^ 2 * (d : ℝ)) - 1 / (1 - β) =
        β * ((d : ℝ) - 1) / ((1 - β ^ 2 * (d : ℝ)) * (1 - β)) := by
    field_simp
    ring
  have hdiff : 0 ≤ centerValue β d - 1 / (1 - β) := by
    rw [centerValue]
    rw [hformula]
    exact haux
  linarith

theorem leafValue_ge_one_div {β : ℝ} {d : ℕ}
    (_hβ0 : 0 < β) (hβ1 : β < 1) (hd : 1 ≤ d)
    (hadm : β ^ 2 * (d : ℝ) < 1) :
    1 / (1 - β) ≤ leafValue β d := by
  have hden1' : 1 - β ≠ 0 := by linarith
  have hden2' : 1 - β ^ 2 * (d : ℝ) ≠ 0 := by linarith
  have hdR : (1 : ℝ) ≤ d := by
    exact_mod_cast hd
  have hdm1 : 0 ≤ (d : ℝ) - 1 := by
    linarith
  have hden : 0 < (1 - β ^ 2 * (d : ℝ)) * (1 - β) := by
    have h1 : 0 < 1 - β ^ 2 * (d : ℝ) := by linarith
    have h2 : 0 < 1 - β := by linarith
    positivity
  have hnum : 0 ≤ β ^ 2 * ((d : ℝ) - 1) := by
    nlinarith [hdm1]
  have haux : 0 ≤ β ^ 2 * ((d : ℝ) - 1) / ((1 - β ^ 2 * (d : ℝ)) * (1 - β)) := by
    exact div_nonneg hnum hden.le
  have hformula :
      (1 + β) / (1 - β ^ 2 * (d : ℝ)) - 1 / (1 - β) =
        β ^ 2 * ((d : ℝ) - 1) / ((1 - β ^ 2 * (d : ℝ)) * (1 - β)) := by
    field_simp
    ring
  have hdiff : 0 ≤ leafValue β d - 1 / (1 - β) := by
    rw [leafValue]
    rw [hformula]
    exact haux
  linarith

@[simp] theorem bonacichCentrality_center_removeLeaf {d : ℕ} {β : ℝ}
    (j : Fin (d + 1)) (hd : 1 ≤ d) (hadm : β ^ 2 * (d : ℝ) < 1) :
    bonacichCentrality β (removeLeaf j : StarSubset d) none = some (centerValue β d) := by
  have hd0 : d ≠ 0 := by omega
  simp [bonacichCentrality, removeLeaf, leafCount, hd0, hadm, centerValue]

@[simp] theorem bonacichCentrality_leaf_removeLeaf {d : ℕ} {β : ℝ}
    (j k : Fin (d + 1)) (hkj : k ≠ j) (hd : 1 ≤ d)
    (hadm : β ^ 2 * (d : ℝ) < 1) :
    bonacichCentrality β (removeLeaf j : StarSubset d) (some k) = some (leafValue β d) := by
  have hd0 : d ≠ 0 := by omega
  simp [bonacichCentrality, removeLeaf, leafCount, hkj, hd0, hadm, leafValue]

theorem removeLeaf_isCandidate {d : ℕ} {β u : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hd : 1 ≤ d)
    (hadm : β ^ 2 * (d : ℝ) < 1) (hu : u < 1 / (1 - β))
    (j : Fin (d + 1)) :
    IsBonacichCandidate β u (removeLeaf j : StarSubset d) := by
  intro v hv
  rcases v with _ | k
  · refine ⟨centerValue β d, ?_, ?_⟩
    · simpa using bonacichCentrality_center_removeLeaf (β := β) j hd hadm
    · have hbound : 1 / (1 - β) ≤ centerValue β d :=
        centerValue_ge_one_div hβ0 hβ1 hd hadm
      linarith
  · have hkj : k ≠ j := by
      simpa [removeLeaf] using hv
    refine ⟨leafValue β d, ?_, ?_⟩
    · simpa using bonacichCentrality_leaf_removeLeaf (β := β) j k hkj hd hadm
    · have hbound : 1 / (1 - β) ≤ leafValue β d :=
        leafValue_ge_one_div hβ0 hβ1 hd hadm
      linarith

theorem removeLeaf_isFixedPoint {d : ℕ} {β u : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hd : 1 ≤ d)
    (hadm : β ^ 2 * (d : ℝ) < 1) (hu : u < 1 / (1 - β))
    (j : Fin (d + 1)) :
    IsFixedPoint β u (removeLeaf j : StarSubset d) :=
  tu_eq_self_iff.2 (removeLeaf_isCandidate hβ0 hβ1 hd hadm hu j)

@[simp] theorem bonacichCentrality_center_univ {d : ℕ} {β : ℝ}
    (hfull : 1 ≤ β ^ 2 * ((d + 1 : ℕ) : ℝ)) :
    bonacichCentrality β (Finset.univ : StarSubset d) none = none := by
  have hfull' : 1 ≤ β ^ 2 * ((d : ℝ) + 1) := by
    simpa [Nat.cast_add, Nat.cast_one] using hfull
  have hnotlt : ¬ β ^ 2 * ((d : ℝ) + 1) < 1 := by
    linarith [hfull']
  simp [bonacichCentrality, leafCount, hnotlt]

theorem univ_not_candidate {d : ℕ} {β u : ℝ}
    (hfull : 1 ≤ β ^ 2 * ((d + 1 : ℕ) : ℝ)) :
    ¬ IsBonacichCandidate β u (Finset.univ : StarSubset d) := by
  intro h
  rcases h none (by simp) with ⟨b, hb, _⟩
  simp [bonacichCentrality_center_univ (β := β) hfull] at hb

theorem univ_not_fixedPoint {d : ℕ} {β u : ℝ}
    (hfull : 1 ≤ β ^ 2 * ((d + 1 : ℕ) : ℝ)) :
    ¬ IsFixedPoint β u (Finset.univ : StarSubset d) := by
  intro hfix
  exact univ_not_candidate (β := β) (u := u) hfull (tu_eq_self_iff.1 hfix)

theorem removeLeaf_union_removeLeaf {d : ℕ}
    (j₀ j₁ : Fin (d + 1)) (hneq : j₀ ≠ j₁) :
    removeLeaf j₀ ∪ removeLeaf j₁ = (Finset.univ : StarSubset d) := by
  ext v
  rcases v with _ | k
  · simp [removeLeaf]
  · constructor
    · intro _
      simp
    · intro _
      by_cases hk0 : k = j₀
      · have hk1 : k ≠ j₁ := by
          intro hk1eq
          exact hneq (hk0.symm.trans hk1eq)
        exact Finset.mem_union.mpr <| Or.inr (by simp [removeLeaf, hk1])
      · exact Finset.mem_union.mpr <| Or.inl (by simp [removeLeaf, hk0])

/--
Deterministic star-graph obstruction from the submitted disproof:
if `u` satisfies `1 < u < 1 / (1 - β)`, the substars obtained by deleting one leaf
are Bonacich fixed points, but their union is the inadmissible full star. Therefore
there is no largest Bonacich `u`-core.
-/
theorem no_greatest_bonacich_u_core_on_star {d : ℕ} {β u : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hd : 1 ≤ d)
    (hadm : β ^ 2 * (d : ℝ) < 1)
    (hfull : 1 ≤ β ^ 2 * ((d + 1 : ℕ) : ℝ))
    (_hu1 : 1 < u) (hu : u < 1 / (1 - β)) :
    ¬ ∃ S : StarSubset d, IsGreatestBonacichUCore β u S := by
  let j₀ : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
  have hj₁ : 1 < d + 1 := by omega
  let j₁ : Fin (d + 1) := ⟨1, hj₁⟩
  have hneq : j₀ ≠ j₁ := by
    intro h
    have hvals : (0 : ℕ) = 1 := by
      simpa [j₀, j₁] using congrArg Fin.val h
    omega
  have hcan₀ : IsBonacichCandidate β u (removeLeaf j₀ : StarSubset d) :=
    removeLeaf_isCandidate hβ0 hβ1 hd hadm hu j₀
  have hcan₁ : IsBonacichCandidate β u (removeLeaf j₁ : StarSubset d) :=
    removeLeaf_isCandidate hβ0 hβ1 hd hadm hu j₁
  rintro ⟨S, hS, hmax⟩
  have hsub₀ : removeLeaf j₀ ⊆ S := hmax _ hcan₀
  have hsub₁ : removeLeaf j₁ ⊆ S := hmax _ hcan₁
  have huniv_sub : (Finset.univ : StarSubset d) ⊆ S := by
    rw [← removeLeaf_union_removeLeaf j₀ j₁ hneq]
    exact Finset.union_subset hsub₀ hsub₁
  have hS_sub : S ⊆ (Finset.univ : StarSubset d) := by
    intro v hv
    simp
  have hSeq : S = (Finset.univ : StarSubset d) :=
    Finset.Subset.antisymm hS_sub huniv_sub
  exact univ_not_candidate (β := β) (u := u) hfull (hSeq ▸ hS)

/--
Equivalent fixed-point formulation of the same obstruction: there is no greatest fixed
point of `T_u` on the critical star.
-/
theorem no_greatest_fixedPoint_on_star {d : ℕ} {β u : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hd : 1 ≤ d)
    (hadm : β ^ 2 * (d : ℝ) < 1)
    (hfull : 1 ≤ β ^ 2 * ((d + 1 : ℕ) : ℝ))
    (hu1 : 1 < u) (hu : u < 1 / (1 - β)) :
    ¬ ∃ S : StarSubset d, IsGreatestFixedPoint β u S := by
  intro h
  apply no_greatest_bonacich_u_core_on_star hβ0 hβ1 hd hadm hfull hu1 hu
  rcases h with ⟨S, hS⟩
  exact ⟨S, (greatestCore_iff_greatestFixedPoint).2 hS⟩

/-- The canonical leaf parameter from the disproof: `d = ⌈(β²)⁻¹⌉₊ - 1`. -/
def criticalD (β : ℝ) : ℕ :=
  ⌈(β ^ 2)⁻¹⌉₊ - 1

theorem criticalD_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 ≤ criticalD β ∧
      β ^ 2 * (criticalD β : ℝ) < 1 ∧
      1 ≤ β ^ 2 * ((criticalD β + 1 : ℕ) : ℝ) := by
  let q : ℕ := ⌈(β ^ 2)⁻¹⌉₊
  have hβ2_pos : 0 < β ^ 2 := by positivity
  have hβ2_nonneg : 0 ≤ β ^ 2 := le_of_lt hβ2_pos
  have hβ2_lt_one : β ^ 2 < 1 := by nlinarith
  have hinv_pos : 0 < (β ^ 2)⁻¹ := inv_pos.mpr hβ2_pos
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Nat.ceil_pos.mpr hinv_pos
  have hq_ne_zero : q ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hq_pos
  have hq_spec : (((q - 1 : ℕ) : ℝ) < (β ^ 2)⁻¹) ∧ ((β ^ 2)⁻¹ ≤ (q : ℝ)) := by
    exact (Nat.ceil_eq_iff hq_ne_zero).1 rfl
  have hq_gt_one : 1 < q := by
    have hone_lt_inv : 1 < (β ^ 2)⁻¹ := by
      exact (one_lt_inv₀ hβ2_pos).2 hβ2_lt_one
    dsimp [q]
    exact (Nat.lt_ceil).2 (by simpa using hone_lt_inv)
  have hd : 1 ≤ criticalD β := by
    dsimp [criticalD, q]
    omega
  have hcancel : β ^ 2 * (β ^ 2)⁻¹ = 1 := by
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hβ0.ne')]
  have hadm : β ^ 2 * (criticalD β : ℝ) < 1 := by
    have hmul :
        β ^ 2 * ((criticalD β : ℕ) : ℝ) < β ^ 2 * (β ^ 2)⁻¹ := by
      simpa [criticalD, q] using mul_lt_mul_of_pos_left hq_spec.1 hβ2_pos
    simpa [hcancel] using hmul
  have hsucc_eq : criticalD β + 1 = q := by
    dsimp [criticalD, q]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hq_pos)
  have hfull : 1 ≤ β ^ 2 * ((criticalD β + 1 : ℕ) : ℝ) := by
    have hmul :
        β ^ 2 * (β ^ 2)⁻¹ ≤ β ^ 2 * ((criticalD β + 1 : ℕ) : ℝ) := by
      simpa [hsucc_eq, q] using mul_le_mul_of_nonneg_left hq_spec.2 hβ2_nonneg
    simpa [hcancel] using hmul
  exact ⟨hd, hadm, hfull⟩

/--
Specialization of the deterministic obstruction using the proof sketch's canonical choice
`d = ⌈(β²)⁻¹⌉₊ - 1`.
-/
theorem no_greatest_bonacich_u_core_on_critical_star {β u : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hu1 : 1 < u) (hu : u < 1 / (1 - β)) :
    ¬ ∃ S : StarSubset (criticalD β), IsGreatestBonacichUCore β u S := by
  obtain ⟨hd, hadm, hfull⟩ := criticalD_spec hβ0 hβ1
  exact no_greatest_bonacich_u_core_on_star hβ0 hβ1 hd hadm hfull hu1 hu

/--
The same obstruction in the parameter regime appearing in the original conjecture:
if `c > 1` and `0 < β < 1 / c`, then the critical star already prevents the existence
of any largest Bonacich `u`-core.
-/
theorem no_greatest_bonacich_u_core_from_original_parameters {c β u : ℝ}
    (hc : 1 < c) (hβ0 : 0 < β) (hβc : β < 1 / c)
    (hu1 : 1 < u) (hu : u < 1 / (1 - β)) :
    ¬ ∃ S : StarSubset (criticalD β), IsGreatestBonacichUCore β u S := by
  have hβ1 : β < 1 := by
    have hcinv : 1 / c < 1 := by
      simpa using one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hc
    exact lt_trans hβc hcinv
  exact no_greatest_bonacich_u_core_on_critical_star hβ0 hβ1 hu1 hu

/--
Fixed-point reformulation of `no_greatest_bonacich_u_core_on_critical_star`.
-/
theorem no_greatest_fixedPoint_on_critical_star {β u : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hu1 : 1 < u) (hu : u < 1 / (1 - β)) :
    ¬ ∃ S : StarSubset (criticalD β), IsGreatestFixedPoint β u S := by
  obtain ⟨hd, hadm, hfull⟩ := criticalD_spec hβ0 hβ1
  exact no_greatest_fixedPoint_on_star hβ0 hβ1 hd hadm hfull hu1 hu

/--
Fixed-point reformulation in the original conjectural parameter regime `c > 1`, `β < 1 / c`.
-/
theorem no_greatest_fixedPoint_from_original_parameters {c β u : ℝ}
    (hc : 1 < c) (hβ0 : 0 < β) (hβc : β < 1 / c)
    (hu1 : 1 < u) (hu : u < 1 / (1 - β)) :
    ¬ ∃ S : StarSubset (criticalD β), IsGreatestFixedPoint β u S := by
  have hβ1 : β < 1 := by
    have hcinv : 1 / c < 1 := by
      simpa using one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hc
    exact lt_trans hβc hcinv
  exact no_greatest_fixedPoint_on_critical_star hβ0 hβ1 hu1 hu

/--
In the original conjectural regime `c > 1`, `0 < β < 1 / c`, there exists a
threshold `u > 1` for which the Bonacich `u`-core is not well-defined as a
greatest admissible subset.
-/
theorem exists_bad_bonacich_threshold_from_original_parameters {c β : ℝ}
    (hc : 1 < c) (hβ0 : 0 < β) (hβc : β < 1 / c) :
    ∃ u : ℝ, 1 < u ∧
      ¬ ∃ S : StarSubset (criticalD β), IsGreatestBonacichUCore β u S := by
  have hβ1 : β < 1 := by
    have hcinv : 1 / c < 1 := by
      simpa using one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hc
    exact lt_trans hβc hcinv
  have hupper : 1 < 1 / (1 - β) := by
    have hpos : 0 < 1 - β := by linarith
    have hlt : 1 - β < 1 := by linarith
    simpa [one_div] using (one_lt_inv₀ hpos).2 hlt
  refine ⟨(1 + 1 / (1 - β)) / 2, ?_, ?_⟩
  · nlinarith
  · exact no_greatest_bonacich_u_core_from_original_parameters hc hβ0 hβc (by nlinarith)
      (by nlinarith)

/--
The same existential obstruction for the fixed-point formulation of the Bonacich
`u`-core operator.
-/
theorem exists_bad_fixedPoint_threshold_from_original_parameters {c β : ℝ}
    (hc : 1 < c) (hβ0 : 0 < β) (hβc : β < 1 / c) :
    ∃ u : ℝ, 1 < u ∧
      ¬ ∃ S : StarSubset (criticalD β), IsGreatestFixedPoint β u S := by
  have hβ1 : β < 1 := by
    have hcinv : 1 / c < 1 := by
      simpa using one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hc
    exact lt_trans hβc hcinv
  have hupper : 1 < 1 / (1 - β) := by
    have hpos : 0 < 1 - β := by linarith
    have hlt : 1 - β < 1 := by linarith
    simpa [one_div] using (one_lt_inv₀ hpos).2 hlt
  refine ⟨(1 + 1 / (1 - β)) / 2, ?_, ?_⟩
  · nlinarith
  · exact no_greatest_fixedPoint_from_original_parameters hc hβ0 hβc (by nlinarith)
      (by nlinarith)

end

end BonacichSquareRootSingularity