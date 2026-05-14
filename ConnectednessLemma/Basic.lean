import Mathlib
open Nat Real Matrix

variable (n : ℕ)
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

/- Define skew-symmetric matrix -/
def IsSkewSymm' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, A i j = - A j i


/- Define connectedness of vertices -/
def IsConnectedTo (i j : (Fin n)) : Prop :=
  -- Here I add explicitly that A is SkewSymm
  (IsSkewSymm' A) ∧ (A i j ≠ 0) ∧ (∀ k, k ≠ i ∧ k ≠ j → ∃ m : ℕ, (A i k + A k j) / (A j i) = ↑m)


lemma Symmetry (i j : Fin n) (h1 : IsConnectedTo A i j) : IsConnectedTo A j i := by
    -- Unpack the connectedness condition
    rcases h1 with ⟨hA, h1_1, h1_2⟩
    -- Show that A j i is nonzero
    have hh1 : A j i ≠ 0 := by
        have h2 : A i j = - A j i := hA i j
        rw [h2] at h1_1
        exact neg_ne_zero.mp h1_1
    -- Show that the second condition holds for j and i
    have hh2 : ∀ k, k ≠ j ∧ k ≠ i → ∃ m : ℕ, (A j k + A k i) / (A i j) = ↑m := by
        intro k hk
        have h3 : k ≠ i ∧ k ≠ j := by
            rw [and_comm] at hk
            exact hk
        have h4 : ∃ m : ℕ, (A i k + A k j) / (A j i) = ↑m := h1_2 k h3
        have h5 : (A j k + A k i) / (A i j) = (A i k + A k j) / (A j i) := by
            have h6 : A j k = - A k j := hA j k
            have h7 : A k i = - A i k := hA k i
            rw [h6, h7, hA i j]
            ring
        rw [← h5] at h4
        exact h4
    exact ⟨hA, hh1, hh2⟩


lemma NoLoops (i j : (Fin n)) {h : IsSkewSymm' A} : IsConnectedTo A i j → ¬ i = j := by
    intro hcon hij
    have h1 : A i i ≠ 0 := by
        simpa [hij] using hcon.right.left
    have h2 : A i i = 0 := by
        have h3 : A i i = -A i i := h i i
        linarith
    exact h1 h2


/- State the Lemma statement -/
/- If i->j->k in A, then Aij is a positive mulitple of Ajk -/
theorem Lemma (i j k : Fin n) (h1 : IsConnectedTo A i j) (h2 : IsConnectedTo A j k) (hh: k ≠ i) :
    ∃ m > 0, A i j = m * A j k := by
    -- Unpack the connectedness conditions
    rcases h1 with ⟨hA, h1_1, h1_2⟩
    rcases h2 with ⟨hA, h2_1, h2_2⟩
    have h3 : ∃ M : ℕ, A i k + A k j = M * A j i := by
        sorry
    have h4 : ∃ N : ℕ, A j i + A i k = N * A k j := by
        sorry
    have h5 : ∃ (M N : ℕ), A i j = ((N + 1) / (M + 1)) * A j k := by
        sorry
    rcases h5 with ⟨M, N, h5⟩
    have h6 : (↑N + 1) / (↑M + 1) > 0 := by
        sorry
    exact ⟨(↑N + 1) / (↑M + 1), h6, h5⟩
