/-
# Theorem 1.1: the independence sequence of every large forest is unimodal

  There is an absolute integer `N₀` such that the independence sequence of every
  forest with at least `N₀` vertices is unimodal.

This is the main theorem of the paper, and Erdős problem #993 restricted to
forests of large order.

## Structure of the proof

Take `n` large enough for Theorem 1.2, and also `n ≥ 1000` — an auxiliary
numerical restriction used only for the rounding inequalities below, not a
claimed threshold.  Put

  `L = ⌈n/5⌉`, `U = ⌊64α/95⌋`, `P = ⌈n/4⌉`, `m = ⌈(2α−1)/3⌉`,  `α = α(F)`.

Since a forest is bipartite, `α ≥ n/2`, and these indices satisfy `L ≤ P < m ≤ U`:

* `⌈n/5⌉ ≤ ⌈n/4⌉` is immediate;
* `P < m` follows from `n/4 + 1 < (n−1)/3`, valid for `n ≥ 1000`;
* `m ≤ U` because `64α/95 − 2α/3 = 2α/285 ≥ n/285 > 2`, which absorbs the
  rounding errors.

Write `r_j = i_j/i_{j−1}`.  Theorem 1.2 says `r_L > r_{L+1} > ⋯ > r_{U+1}`;
Proposition 6.2 says `r_j ≥ 1` for `j ≤ P` and `r_j ≤ 1` for `j ≥ m+1`.  Between
these two ranges the ratios are strictly decreasing, so there cannot be a ratio
less than `1` followed later by a ratio greater than `1`, and the sequence is
unimodal (allowing equality at the mode or within the end segments).

## The arithmetic core

`isUnimodal_of_central_logConcave` isolates the combinatorial content as a
statement about an arbitrary sequence `f : ℕ → ℕ`; it involves no graphs and is
proved without division, by showing that

  `A = {k ∈ [L, U+1] : f(k−1) ≤ f(k)}`

is an initial segment of `[L, U+1]`.  Indeed if `f(k−1) ≤ f(k)` and
`L ≤ k−1 ≤ U`, then strict log-concavity at `k−1` gives
`f(k−2) f(k−1) ≤ f(k−2) f(k) < f(k−1)²`, whence `f(k−2) < f(k−1)` (no
positivity hypothesis is needed: the strict inequality already forces
`f(k−1) > 0`).  The mode is `max A`.
-/
import ErdosProblem993.Central
import ErdosProblem993.Ends

namespace ErdosProblem993

open Finset

/-! ## The arithmetic core -/

/-- **A unimodality criterion.**  A sequence that is weakly increasing on an
initial block `[0, P]`, weakly decreasing on a final block `[m, ∞)`, and strictly
log-concave on a central block `[L, U]` overlapping both (`L ≤ P < m ≤ U`) is
unimodal.

No division is used: strict log-concavity is expressed as
`f (k−1) * f (k+1) < f k ^ 2`.  No positivity of `f` is assumed either: the
strict inequality at `k−1` already rules out `f (k−1) = 0`. -/
theorem isUnimodal_of_central_logConcave {f : ℕ → ℕ} {L P m U : ℕ}
    (hLP : L ≤ P) (hPm : P < m) (hmU : m ≤ U)
    (hprefix : ∀ j k, j ≤ k → k ≤ P → f j ≤ f k)
    (htail : ∀ j k, m ≤ j → j ≤ k → f k ≤ f j)
    (hlc : ∀ k, L ≤ k → k ≤ U → f (k - 1) * f (k + 1) < f k ^ 2) :
    IsUnimodal f := by
  classical
  -- The key step: a non-descent at `j → j+1` inside the log-concave window forces a
  -- strict ascent at `j-1 → j`.
  have key : ∀ j, L ≤ j → j ≤ U → f j ≤ f (j + 1) → f (j - 1) < f j := by
    intro j hLj hjU hle
    have h1 := hlc j hLj hjU
    rw [sq] at h1
    have h2 : f (j - 1) * f j ≤ f (j - 1) * f (j + 1) := Nat.mul_le_mul_left _ hle
    exact lt_of_mul_lt_mul_right (h2.trans_lt h1) (Nat.zero_le _)
  -- `Q k` says that `k ∈ [L, ∞)` is a non-descent index; the mode is the largest such
  -- `k ≤ U + 1`.
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → Prop, Q = fun k => L ≤ k ∧ f (k - 1) ≤ f k := ⟨_, rfl⟩
  have hQL : Q L := by
    rw [hQ]
    exact ⟨le_rfl, hprefix (L - 1) L (Nat.sub_le _ _) hLP⟩
  have hLU : L ≤ U + 1 := by omega
  have hm₀U : Nat.findGreatest Q (U + 1) ≤ U + 1 := Nat.findGreatest_le _
  have hLm₀ : L ≤ Nat.findGreatest Q (U + 1) := Nat.le_findGreatest hLU hQL
  have hQm₀ : Q (Nat.findGreatest Q (U + 1)) := Nat.findGreatest_spec hLU hQL
  have hmax : ∀ k, Nat.findGreatest Q (U + 1) < k → k ≤ U + 1 → ¬ Q k :=
    fun _ hk hkU => Nat.findGreatest_is_greatest hk hkU
  generalize Nat.findGreatest Q (U + 1) = m₀ at hm₀U hLm₀ hQm₀ hmax
  rw [hQ] at hQm₀
  -- Downward propagation: every `i ∈ [L, m₀]` is a non-descent index.
  have down : ∀ d i, L ≤ i → i + d = m₀ → f (i - 1) ≤ f i := by
    intro d
    induction d with
    | zero =>
      intro i _ hi
      simp only [Nat.add_zero] at hi
      subst hi
      exact hQm₀.2
    | succ d ih =>
      intro i hLi hi
      have h1 : f i ≤ f (i + 1) := by
        have := ih (i + 1) (by omega) (by omega)
        simpa using this
      exact (key i hLi (by omega) h1).le
  -- One-step monotonicity below `m₀`.
  have step1 : ∀ i, i + 1 ≤ m₀ → f i ≤ f (i + 1) := by
    intro i hi
    by_cases hP : i + 1 ≤ P
    · exact hprefix i (i + 1) (Nat.le_succ i) hP
    · have := down (m₀ - (i + 1)) (i + 1) (by omega) (by omega)
      simpa using this
  -- One-step antitonicity above `m₀`.
  have step2 : ∀ i, m₀ ≤ i → f (i + 1) ≤ f i := by
    intro i hi
    by_cases hU : i + 1 ≤ U + 1
    · have h := hmax (i + 1) (by omega) hU
      rw [hQ] at h
      simp only [Nat.add_sub_cancel, not_and, not_le] at h
      exact (h (by omega)).le
    · exact htail i (i + 1) (by omega) (Nat.le_succ i)
  have mono : ∀ d j, j + d ≤ m₀ → f j ≤ f (j + d) := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j hj
      have h1 : f (j + d) ≤ f (j + d + 1) := step1 (j + d) (by omega)
      rw [← Nat.add_assoc]
      exact (ih j (by omega)).trans h1
  have anti : ∀ d j, m₀ ≤ j → f (j + d) ≤ f j := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j hj
      rw [← Nat.add_assoc]
      exact (step2 (j + d) (by omega)).trans (ih j hj)
  refine ⟨m₀, ?_, ?_⟩
  · intro j k hjk hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
    exact mono d j hk
  · intro j k hj hjk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
    exact anti d j hj

/-! ## Rounding inequalities

With `α ≥ n/2` and `n ≥ 1000`, the four indices interleave as `L ≤ P < m ≤ U`.
All four are written with `ℕ`-division:
`L = (n+4)/5 = ⌈n/5⌉`, `P = (n+3)/4 = ⌈n/4⌉`,
`m = (2α+1)/3 = ⌈(2α−1)/3⌉`, `U = 64α/95 = ⌊64α/95⌋`. -/

theorem index_interleave {n α : ℕ} (hn : 1000 ≤ n) (hα : n ≤ 2 * α) (hαn : α ≤ n) :
    1 ≤ (n + 4) / 5 ∧
    (n + 4) / 5 ≤ (n + 3) / 4 ∧
    (n + 3) / 4 < (2 * α + 1) / 3 ∧
    (2 * α + 1) / 3 ≤ 64 * α / 95 ∧
    64 * α / 95 ≤ α := by
  omega

/-! ## Theorem 1.1 -/

/-- **Theorem 1.1**, on the vertex type `Fin n`.

The existential `N₀` is quantified *outside* the quantification over `n` and over
the forest, so the threshold is absolute, exactly as in the statement of the
paper.  Stating it on `Fin n` is what makes this literally true rather than true
for each universe separately; `unimodal_of_isAcyclic` transfers it to an
arbitrary finite vertex type. -/
theorem main_fin :
    ∃ N₀ : ℕ, ∀ (n : ℕ), N₀ ≤ n → ∀ (G : SimpleGraph (Fin n)), G.IsAcyclic →
      IsUnimodal (icoeff G Finset.univ) := by
  obtain ⟨N₁, hN₁⟩ := central
  refine ⟨max 1000 N₁, fun n hn G hG => ?_⟩
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hn1000 : 1000 ≤ n := le_trans (le_max_left _ _) hn
  have hnN₁ : N₁ ≤ n := le_trans (le_max_right _ _) hn
  have h2α : n ≤ 2 * alpha G Finset.univ := by
    have := card_le_two_mul_alpha hG (Finset.univ : Finset (Fin n))
    rwa [hcard] at this
  have hαn : alpha G Finset.univ ≤ n := by
    have := alpha_le_card (G := G) (Finset.univ : Finset (Fin n))
    rwa [hcard] at this
  -- Only `L ≤ P < m ≤ U` is consumed; `1 ≤ L` and `U ≤ α` are recorded in
  -- `index_interleave` because the paper states them, but the criterion above
  -- does not need them.
  obtain ⟨-, h2, h3, h4, -⟩ := index_interleave hn1000 h2α hαn
  refine isUnimodal_of_central_logConcave (L := (n + 4) / 5)
    (P := (n + 3) / 4) (m := (2 * alpha G Finset.univ + 1) / 3)
    (U := 64 * alpha G Finset.univ / 95) h2 h3 h4 ?_ ?_ ?_
  · intro j k hjk hk
    exact monotoneOn_icoeff_prefix hG Finset.univ hjk (by rwa [hcard])
  · intro j k hj hjk
    exact antitoneOn_icoeff_tail (isBipartiteOn_of_isAcyclic hG Finset.univ) hj hjk
  · intro k hLk hkU
    exact hN₁ n G hG Finset.univ (by rwa [hcard]) k (by rwa [hcard]) hkU

end ErdosProblem993
