/-
# Theorem 1.2: strict log-concavity on a central interval

For every sufficiently large `n`, every forest `F` on `n` vertices satisfies

  `i_k(F)² > i_{k−1}(F) i_{k+1}(F)`   whenever   `⌈n/5⌉ ≤ k ≤ ⌊64 α(F)/95⌋`,

with a size threshold independent of `F`.

This is Proposition 4.2 combined with Proposition 5.1: the latter says that every
integer in the displayed interval lies between the means at activities `1/4` and
`12`, and the former gives strict log-concavity at every such integer, with a
threshold uniform over the forest and the activity.

The constants `1/5` and `64/95` are convenient choices, not claimed optimal.

## Ceilings and floors as natural-number division

`⌈n/5⌉ = (n+4)/5` and `⌊64α/95⌋ = 64α/95` in `ℕ`-division.
-/
import ErdosProblem993.Curvature
import ErdosProblem993.MeanRange

namespace ErdosProblem993

open Finset

/-- **Theorem 1.2** (`thm:central`).

`(n+4)/5` is `⌈n/5⌉` and `64 * α / 95` is `⌊64α/95⌋`, both in `ℕ`-division. -/
theorem central :
    ∃ N₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
      ∀ (S : Finset (Fin n)), N₀ ≤ S.card → ∀ k : ℕ,
        (S.card + 4) / 5 ≤ k → k ≤ 64 * alpha G S / 95 →
        icoeff G S (k - 1) * icoeff G S (k + 1) < icoeff G S k ^ 2 := by
  obtain ⟨N, hN⟩ := mean_lc
  refine ⟨max N 1, fun n G hG S hS k hk₁ hk₂ => ?_⟩
  have hS1 : 1 ≤ S.card := le_trans (le_max_right _ _) hS
  have hSne : S.Nonempty := Finset.card_pos.1 hS1
  obtain ⟨hlow, hhigh⟩ := mean_range hSne hG
  -- `⌈n/5⌉ ≤ k` means `n ≤ 5k`; `k ≤ ⌊64α/95⌋` means `95k ≤ 64α`.
  have h5 : S.card ≤ 5 * k := by omega
  have h95 : 95 * k ≤ 64 * alpha G S := by omega
  have h5' : (S.card : ℝ) ≤ 5 * k := by exact_mod_cast h5
  have h95' : (95 : ℝ) * k ≤ 64 * alpha G S := by exact_mod_cast h95
  refine hN n G hG S (le_trans (le_max_left _ _) hS) k ?_ ?_
  · calc hcMean G S (1 / 4) ≤ (S.card : ℝ) / 5 := hlow
      _ ≤ k := by linarith
  · calc (k : ℝ) ≤ 64 * (alpha G S : ℝ) / 95 := by linarith
      _ ≤ hcMean G S 12 := hhigh.le

end ErdosProblem993
