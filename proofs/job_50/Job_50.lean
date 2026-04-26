import Mathlib

noncomputable section

open scoped BigOperators

namespace AdaBoostGlobalDynamics

/-- A weight vector on `m` training examples. -/
abbrev Weight (m : Nat) := Fin m → ℝ

/-- The (closed) probability simplex `Δ_{m-1}`. -/
def IsSimplex {m : Nat} (w : Weight m) : Prop :=
  (∀ i : Fin m, 0 ≤ w i) ∧ Finset.univ.sum (fun i : Fin m => w i) = 1

/-- The open probability simplex, where every coordinate is strictly positive.
This is the regime where the standard multiplicative AdaBoost update is
well-defined for every column. -/
def IsOpenSimplex {m : Nat} (w : Weight m) : Prop :=
  (∀ i : Fin m, 0 < w i) ∧ Finset.univ.sum (fun i : Fin m => w i) = 1

theorem IsOpenSimplex.isSimplex {m : Nat} {w : Weight m}
    (hw : IsOpenSimplex w) : IsSimplex w := by
  refine ⟨?_, hw.2⟩
  intro i
  exact le_of_lt (hw.1 i)

/-- A finite signed prediction matrix `M i j = y_i * h_j(x_i)` with entries in
`{-1, +1}`. -/
def IsSignMatrix {m N : Nat} (M : Fin m → Fin N → ℝ) : Prop :=
  ∀ i : Fin m, ∀ j : Fin N, M i j = -1 ∨ M i j = 1

/-- Binary labels `y_i ∈ {-1, +1}`. -/
def BinaryLabels {m : Nat} (y : Fin m → ℤ) : Prop :=
  ∀ i : Fin m, y i = -1 ∨ y i = 1

/-- Binary-valued weak hypotheses on the observed sample points. -/
def BinaryHypothesesOnData {m N : Nat} {X : Type}
    (x : Fin m → X) (hyp : Fin N → X → ℤ) : Prop :=
  ∀ j : Fin N, ∀ i : Fin m, hyp j (x i) = -1 ∨ hyp j (x i) = 1

/-- The matrix form of a finite binary-labeled dataset and finite hypothesis
class: `M i j = y_i * h_j(x_i)`. -/
def predictionMatrix {m N : Nat} {X : Type}
    (x : Fin m → X) (y : Fin m → ℤ) (hyp : Fin N → X → ℤ) :
    Fin m → Fin N → ℝ :=
  fun i j => ((y i * hyp j (x i) : ℤ) : ℝ)

theorem predictionMatrix_isSign {m N : Nat} {X : Type}
    {x : Fin m → X} {y : Fin m → ℤ} {hyp : Fin N → X → ℤ}
    (hy : BinaryLabels y) (hh : BinaryHypothesesOnData x hyp) :
    IsSignMatrix (predictionMatrix x y hyp) := by
  intro i j
  rcases hy i with hyneg | hypos <;> rcases hh j i with hhneg | hhpos
  · right
    simp [predictionMatrix, hyneg, hhneg]
  · left
    simp [predictionMatrix, hyneg, hhpos]
  · left
    simp [predictionMatrix, hypos, hhneg]
  · right
    simp [predictionMatrix, hypos, hhpos]

/-- The edge of hypothesis column `j` at weights `w`, i.e. `(wᵀ M)_j`. -/
def edge {m N : Nat} (M : Fin m → Fin N → ℝ) (w : Weight m)
    (j : Fin N) : ℝ :=
  Finset.univ.sum (fun i : Fin m => w i * M i j)

/-- The weighted classification error of column `j`: probability mass on
examples with `M i j = -1`, equivalently `h_j(x_i) ≠ y_i`. -/
def weightedError {m N : Nat} (M : Fin m → Fin N → ℝ) (w : Weight m)
    (j : Fin N) : ℝ :=
  Finset.univ.sum (fun i : Fin m => if M i j = -1 then w i else 0)

/-- The Freund--Schapire AdaBoost coefficient
`α_t = (1/2) log((1 - ε_t) / ε_t)`. -/
def alpha {m N : Nat} (M : Fin m → Fin N → ℝ) (w : Weight m)
    (j : Fin N) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 - weightedError M w j) / weightedError M w j)

/-- The exponential normalizer
`Z_t = ∑_i w_t(i) exp(-α_t M_{i,j_t})`. -/
def normalizer {m N : Nat} (M : Fin m → Fin N → ℝ) (w : Weight m)
    (j : Fin N) : ℝ :=
  Finset.univ.sum
    (fun i : Fin m => w i * Real.exp (-(alpha M w j) * M i j))

/-- The Freund--Schapire AdaBoost update for the selected column `j`:
`w_{t+1}(i) = w_t(i) exp(-α_t M_{i,j_t}) / Z_t`. -/
def updatedWeight {m N : Nat} (M : Fin m → Fin N → ℝ) (w : Weight m)
    (j : Fin N) : Weight m :=
  fun i => w i * Real.exp (-(alpha M w j) * M i j) / normalizer M w j

/-- Deterministic exhaustive weak-learner selection: choose an edge maximizer,
breaking ties by the smallest finite index (Rudin--Daubechies--Schapire 2012). -/
def IsArgMaxSmallest {m N : Nat} (M : Fin m → Fin N → ℝ) (w : Weight m)
    (j : Fin N) : Prop :=
  (∀ k : Fin N, edge M w k ≤ edge M w j) ∧
    ∀ k : Fin N, edge M w k = edge M w j → (j : Nat) ≤ (k : Nat)

/-- One step of exhaustive AdaBoost with deterministic tie-breaking. The
inequalities `0 < ε < 1` and `Z ≠ 0` record the nondegeneracy required for
the displayed logarithmic normalized update to be well-defined. -/
def AdaBoostStep {m N : Nat} (M : Fin m → Fin N → ℝ)
    (w w' : Weight m) : Prop :=
  ∃ j : Fin N,
    IsArgMaxSmallest M w j ∧
      0 < weightedError M w j ∧
        weightedError M w j < 1 ∧
          normalizer M w j ≠ 0 ∧
            w' = updatedWeight M w j

/-- The generic no-tie condition at a weight vector: pairwise distinct edges,
i.e. `(wᵀ M)_j ≠ (wᵀ M)_{j'}` for all `j ≠ j'`, so that `w` is not on a
tie boundary between weak-hypothesis regions of the simplex. -/
def NoTieAt {m N : Nat} (M : Fin m → Fin N → ℝ) (w : Weight m) : Prop :=
  ∀ j k : Fin N, j ≠ k → edge M w j ≠ edge M w k

/-- An AdaBoost orbit `w_0, w_1, …`: every iterate lies in the probability
simplex `Δ_{m-1}` and consecutive iterates are related by the exhaustive
deterministic AdaBoost update. -/
def IsAdaBoostOrbit {m N : Nat} (M : Fin m → Fin N → ℝ)
    (w : Nat → Weight m) : Prop :=
  (∀ t : Nat, IsSimplex (w t)) ∧
    ∀ t : Nat, AdaBoostStep M (w t) (w (t + 1))

/-- An AdaBoost orbit whose weights remain strictly positive at every step. -/
def IsOpenAdaBoostOrbit {m N : Nat} (M : Fin m → Fin N → ℝ)
    (w : Nat → Weight m) : Prop :=
  (∀ t : Nat, IsOpenSimplex (w t)) ∧
    ∀ t : Nat, AdaBoostStep M (w t) (w (t + 1))

theorem IsOpenAdaBoostOrbit.isAdaBoostOrbit {m N : Nat}
    {M : Fin m → Fin N → ℝ} {w : Nat → Weight m}
    (h : IsOpenAdaBoostOrbit M w) : IsAdaBoostOrbit M w := by
  refine ⟨?_, h.2⟩
  intro t
  exact (h.1 t).isSimplex

/-- Eventual periodicity of a weight-vector orbit: there exist a preperiod `T`
and a period `p ≥ 1` such that `w_{t+p} = w_t` for all `t ≥ T`. -/
def EventuallyPeriodicSeq {m : Nat} (w : Nat → Weight m) : Prop :=
  ∃ T : Nat, ∃ p : Nat, 0 < p ∧ ∀ t : Nat, T ≤ t → w (t + p) = w t

/-- Matrix-form version of the AdaBoost Always Cycles? global dynamics
conjecture: for every finite signed prediction matrix and every exhaustive
AdaBoost orbit avoiding tie boundaries, the orbit is eventually periodic. -/
def MatrixGlobalConjecture : Prop :=
  ∀ (m N : Nat), 0 < m → 0 < N →
    ∀ (M : Fin m → Fin N → ℝ) (w : Nat → Weight m),
      IsSignMatrix M →
        IsAdaBoostOrbit M w →
          (∀ t : Nat, NoTieAt M (w t)) →
            EventuallyPeriodicSeq w

/-- Dataset/hypothesis-class version of the AdaBoost Always Cycles? global
dynamics conjecture, with `M i j = y_i * h_j(x_i)` and deterministic
smallest-index tie-breaking inside `IsAdaBoostOrbit`. -/
def AdaBoostAlwaysCyclesGlobalConjecture : Prop :=
  ∀ (m N : Nat), 0 < m → 0 < N →
    ∀ (X : Type) (x : Fin m → X) (y : Fin m → ℤ)
      (hyp : Fin N → X → ℤ) (w : Nat → Weight m),
        BinaryLabels y →
          BinaryHypothesesOnData x hyp →
            IsAdaBoostOrbit (predictionMatrix x y hyp) w →
              (∀ t : Nat, NoTieAt (predictionMatrix x y hyp) (w t)) →
                EventuallyPeriodicSeq w

/-- The deterministic smallest-index argmax is unique whenever it exists. -/
theorem argMaxSmallest_unique {m N : Nat}
    {M : Fin m → Fin N → ℝ} {w : Weight m} {j k : Fin N}
    (hj : IsArgMaxSmallest M w j) (hk : IsArgMaxSmallest M w k) :
    j = k := by
  have hkj : edge M w k = edge M w j := le_antisymm (hj.1 k) (hk.1 j)
  have hj_le_k : (j : Nat) ≤ (k : Nat) := hj.2 k hkj
  have hk_le_j : (k : Nat) ≤ (j : Nat) := hk.2 j hkj.symm
  exact Fin.ext (Nat.le_antisymm hj_le_k hk_le_j)

/-- The single-step AdaBoost relation is deterministic whenever it is defined. -/
theorem AdaBoostStep_unique {m N : Nat}
    {M : Fin m → Fin N → ℝ} {w w₁ w₂ : Weight m}
    (h₁ : AdaBoostStep M w w₁) (h₂ : AdaBoostStep M w w₂) :
    w₁ = w₂ := by
  rcases h₁ with ⟨j, hj, _, _, _, hw₁⟩
  rcases h₂ with ⟨k, hk, _, _, _, hw₂⟩
  have hidx : j = k := argMaxSmallest_unique hj hk
  subst hidx
  rw [hw₁, hw₂]

/-- The dataset and matrix formulations of the conjecture are equivalent. -/
theorem dataset_conjecture_iff_matrix_conjecture :
    AdaBoostAlwaysCyclesGlobalConjecture ↔ MatrixGlobalConjecture := by
  constructor
  · intro hdataset m N hm hN M w hM horbit hnotie
    let X : Type := Fin m
    let x : Fin m → X := fun i => i
    let y : Fin m → ℤ := fun _ => 1
    let hyp : Fin N → X → ℤ := fun j i => if M i j = 1 then 1 else -1
    have hy : BinaryLabels y := by
      intro i
      right
      rfl
    have hh : BinaryHypothesesOnData x hyp := by
      intro j i
      dsimp [x, hyp]
      by_cases h1 : M i j = 1
      · right
        simp [h1]
      · left
        simp [h1]
    have hpred : predictionMatrix x y hyp = M := by
      funext i j
      dsimp [predictionMatrix, x, y, hyp]
      rcases hM i j with hneg | hpos
      · have hneOne : ¬ ((-1 : ℝ) = 1) := by norm_num
        simp [hneg, hneOne]
      · simp [hpos]
    exact hdataset m N hm hN X x y hyp w hy hh
      (by simpa [hpred] using horbit)
      (by simpa [hpred] using hnotie)
  · intro hmatrix m N hm hN X x y hyp w hy hh horbit hnotie
    exact hmatrix m N hm hN (predictionMatrix x y hyp) w
      (predictionMatrix_isSign hy hh) horbit hnotie

/-- Data for a fully certified finite exhaustive-AdaBoost counterexample in the
finite matrix formulation. -/
structure ExhaustiveAdaBoostMatrixCounterexample : Type where
  m : Nat
  N : Nat
  hm : 0 < m
  hN : 0 < N
  M : Fin m → Fin N → ℝ
  w : Nat → Weight m
  hsign : IsSignMatrix M
  horbit : IsAdaBoostOrbit M w
  hnotie : ∀ t : Nat, NoTieAt M (w t)
  hnonperiodic : ¬ EventuallyPeriodicSeq w

/-- Data for a fully certified finite exhaustive-AdaBoost counterexample in the
dataset/hypothesis-class formulation. -/
structure ExhaustiveAdaBoostDatasetCounterexample : Type 1 where
  m : Nat
  N : Nat
  hm : 0 < m
  hN : 0 < N
  X : Type
  x : Fin m → X
  y : Fin m → ℤ
  hyp : Fin N → X → ℤ
  w : Nat → Weight m
  hy : BinaryLabels y
  hh : BinaryHypothesesOnData x hyp
  horbit : IsAdaBoostOrbit (predictionMatrix x y hyp) w
  hnotie : ∀ t : Nat, NoTieAt (predictionMatrix x y hyp) (w t)
  hnonperiodic : ¬ EventuallyPeriodicSeq w

/-- A fully certified matrix counterexample refutes the matrix-form conjecture. -/
theorem not_matrix_conjecture_of_counterexample
    (hcounter : Nonempty ExhaustiveAdaBoostMatrixCounterexample) :
    ¬ MatrixGlobalConjecture := by
  intro hglobal
  obtain ⟨ce⟩ := hcounter
  exact ce.hnonperiodic
    (hglobal ce.m ce.N ce.hm ce.hN ce.M ce.w ce.hsign ce.horbit ce.hnotie)

/-- A fully certified dataset counterexample refutes the dataset-form conjecture. -/
theorem not_dataset_conjecture_of_counterexample
    (hcounter : Nonempty ExhaustiveAdaBoostDatasetCounterexample) :
    ¬ AdaBoostAlwaysCyclesGlobalConjecture := by
  intro hglobal
  obtain ⟨ce⟩ := hcounter
  exact ce.hnonperiodic
    (hglobal ce.m ce.N ce.hm ce.hN ce.X ce.x ce.y ce.hyp ce.w
      ce.hy ce.hh ce.horbit ce.hnotie)

/-- A fully certified matrix counterexample also refutes the dataset-form
conjecture, since every finite sign matrix is realized by a finite
binary-labeled dataset with binary hypotheses. -/
theorem not_dataset_conjecture_of_matrix_counterexample
    (hcounter : Nonempty ExhaustiveAdaBoostMatrixCounterexample) :
    ¬ AdaBoostAlwaysCyclesGlobalConjecture := by
  intro hglobal
  have hmatrix : MatrixGlobalConjecture :=
    dataset_conjecture_iff_matrix_conjecture.mp hglobal
  exact not_matrix_conjecture_of_counterexample hcounter hmatrix

/-- Sanity check: a constant sequence is eventually periodic with period `1`. -/
theorem constant_seq_eventuallyPeriodic {m : Nat} (w₀ : Weight m) :
    EventuallyPeriodicSeq (fun _ : Nat => w₀) := by
  refine ⟨0, 1, Nat.zero_lt_one, ?_⟩
  intro _ _
  rfl

end AdaBoostGlobalDynamics

end