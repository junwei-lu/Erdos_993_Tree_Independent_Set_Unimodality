/-
# Proposition 6.2: the increasing initial segment and the decreasing final segment

Two one-sided statements about the independence sequence, both proved by
extension double counting (`eq:extensions`):

* **`eq:prefix`** — every nonempty forest `F` of order `n` satisfies
  `i₀ ≤ i₁ ≤ ⋯ ≤ i_{⌈n/4⌉}`.
  Proof: for a uniform independent `k`-set `J`, `e(J) ≥ n − k − ∑_{v∈J} d(v)`,
  so Lemma 6.1 gives `(k+1) i_{k+1} / i_k = E e(J) ≥ n − 3k`, and `n − 3k ≥ k+1`
  exactly when `k ≤ ⌊(n−1)/4⌋`.

* **`eq:tail`** — every bipartite graph satisfies
  `i_{⌈(2α−1)/3⌉} ≥ ⋯ ≥ i_α`.
  Proof: `S ∖ N[J]` is bipartite with independence number at most `α − k`, and a
  bipartite graph on `m` vertices has an independent set of size at least `m/2`,
  so `e(J) ≤ 2(α − k)` and `(k+1) i_{k+1} ≤ 2(α−k) i_k`.  The multiplier
  `2(α−k)` is at most `k+1` exactly when `k ≥ ⌈(2α−1)/3⌉`.

  This is the bipartite case of the decreasing-tail theorem of Levit and
  Mandrescu for König–Egerváry graphs; the proof here uses only extension
  counting.

## Ceilings as natural-number division

`⌈n/4⌉ = (n+3)/4` and `⌈(2α−1)/3⌉ = (2α+1)/3` in `ℕ`-division, which is how the
two thresholds are written below.  (For `α = 0` both sides are `0`, so the
second identity is correct there too, where `2α−1` would underflow.)
-/
import ErdosProblem993.DegreeLemma

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- The key ratio bound behind the initial segment:
`(k+1) i_{k+1} ≥ (n − 3k) i_k`. -/
theorem prefix_ratio (hG : G.IsAcyclic) (S : Finset V) (k : ℕ) :
    (S.card - 3 * k) * icoeff G S k ≤ (k + 1) * icoeff G S (k + 1) := by
  rw [← sum_numExtensions]
  -- pointwise: `n ≤ e(J) + k + ∑_{v ∈ J} d(v)` for every independent `k`-set `J`
  have h1 : ∀ J ∈ indepCard G S k,
      S.card ≤ numExtensions G S J + k + ∑ v ∈ J, degOn G S v := by
    intro J hJ
    obtain ⟨hJ, hk⟩ := mem_indepCard.1 hJ
    have := numExtensions_ge hJ
    rwa [hk] at this
  -- summed over `J`
  have h3 : ∑ J ∈ indepCard G S k, S.card ≤
      ∑ J ∈ indepCard G S k, (numExtensions G S J + k + ∑ v ∈ J, degOn G S v) :=
    Finset.sum_le_sum h1
  simp only [Finset.sum_const, card_indepCard, smul_eq_mul, Finset.sum_add_distrib] at h3
  -- Lemma 6.1: `∑_J ∑_{v ∈ J} d(v) ≤ 2k i_k`
  have h2 := sum_degOn_le hG S k
  rw [Nat.sub_mul, tsub_le_iff_right]
  nlinarith [h2, h3]

/-- **`eq:prefix`**: the independence sequence of a forest is weakly increasing
up to index `⌈n/4⌉ = (n+3)/4`. -/
theorem icoeff_le_icoeff_succ (hG : G.IsAcyclic) (S : Finset V) {k : ℕ}
    (hk : k + 1 ≤ (S.card + 3) / 4) :
    icoeff G S k ≤ icoeff G S (k + 1) := by
  have h := prefix_ratio hG S k
  have hk' : k + 1 ≤ S.card - 3 * k := by
    rw [Nat.le_div_iff_mul_le (by norm_num)] at hk
    omega
  have : (k + 1) * icoeff G S k ≤ (k + 1) * icoeff G S (k + 1) :=
    (Nat.mul_le_mul_right _ hk').trans h
  exact Nat.le_of_mul_le_mul_left this (Nat.succ_pos k)

/-- Monotone form of `eq:prefix`. -/
theorem monotoneOn_icoeff_prefix (hG : G.IsAcyclic) (S : Finset V) :
    ∀ ⦃j k : ℕ⦄, j ≤ k → k ≤ (S.card + 3) / 4 → icoeff G S j ≤ icoeff G S k := by
  intro j k hjk
  induction k, hjk using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hjk ih =>
    intro hk
    exact (ih (by omega)).trans (icoeff_le_icoeff_succ hG S hk)

/-- The key ratio bound behind the final segment:
`(k+1) i_{k+1} ≤ 2(α − k) i_k`. -/
theorem tail_ratio {S : Finset V} (h : IsBipartiteOn G S) (k : ℕ) :
    (k + 1) * icoeff G S (k + 1) ≤ 2 * (alpha G S - k) * icoeff G S k := by
  rw [← sum_numExtensions]
  calc ∑ J ∈ indepCard G S k, numExtensions G S J
      ≤ ∑ J ∈ indepCard G S k, 2 * (alpha G S - k) :=
        Finset.sum_le_sum fun J hJ => numExtensions_le_of_bipartite h hJ
    _ = 2 * (alpha G S - k) * icoeff G S k := by
        rw [Finset.sum_const, card_indepCard, smul_eq_mul, mul_comm]

/-- **`eq:tail`**: the independence sequence of a bipartite graph is weakly
decreasing from index `⌈(2α−1)/3⌉ = (2α+1)/3` onwards. -/
theorem icoeff_succ_le_icoeff {S : Finset V} (h : IsBipartiteOn G S) {k : ℕ}
    (hk : (2 * alpha G S + 1) / 3 ≤ k) :
    icoeff G S (k + 1) ≤ icoeff G S k := by
  have h1 := tail_ratio h k
  have hk' : 2 * (alpha G S - k) ≤ k + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)] at hk
    omega
  have : (k + 1) * icoeff G S (k + 1) ≤ (k + 1) * icoeff G S k :=
    h1.trans (Nat.mul_le_mul_right _ hk')
  exact Nat.le_of_mul_le_mul_left this (Nat.succ_pos k)

/-- Antitone form of `eq:tail`. -/
theorem antitoneOn_icoeff_tail {S : Finset V} (h : IsBipartiteOn G S) :
    ∀ ⦃j k : ℕ⦄, (2 * alpha G S + 1) / 3 ≤ j → j ≤ k → icoeff G S k ≤ icoeff G S j := by
  intro j k hj hjk
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
    exact (icoeff_succ_le_icoeff h (hj.trans hjk)).trans ih

omit [Fintype V] [DecidableEq V] in
/-- Forests are bipartite, so `eq:tail` applies to them.

A global proper `2`-colouring of `G` (mathlib's `IsAcyclic.coloringTwo`)
separates adjacent vertices everywhere, in particular inside `S`. -/
theorem isBipartiteOn_of_isAcyclic (hG : G.IsAcyclic) (S : Finset V) : IsBipartiteOn G S := by
  let c : G.Coloring (Fin 2) := hG.coloringTwo
  refine ⟨fun v => decide (c v = 0), fun u _ v _ huv hc => c.valid huv ?_⟩
  have key : ∀ a b : Fin 2, decide (a = 0) = decide (b = 0) → a = b := by decide
  exact key _ _ hc

end ErdosProblem993
