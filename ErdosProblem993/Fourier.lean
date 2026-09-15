/-
# Lemma 4.1: a characteristic-function bound at all frequencies

  `|E_λ e^{itX}| ≤ exp(−c n sin²(t/2))`

uniformly over forests of order `n` and activities `λ ∈ K = [1/4, 12]`.

A central limit theorem alone gives no sign information about three adjacent
coefficients; this bound at *all* frequencies is what upgrades it, through
Fourier inversion, to the second-difference estimate of Proposition 4.2.  No
bound on the maximum degree is assumed anywhere.

## Structure of the proof

Let `G` be bipartite with classes `L`, `R`.  Conditional on `I ∩ R`, the
available vertices of `L` are independently occupied with probability
`λ/(1+λ)`, so with `B` the number of available vertices of `L`,

  `|E(e^{itX} | I ∩ R)| = (1 − 4λ/(1+λ)² sin²(t/2))^{B/2} ≤ h^B`,

where `h = 1 − β sin²(t/2)` and `β = min{λ/(1+λ), 2λ/(1+λ)²}`; the inequality is
`√(1−z) ≤ 1 − z/2`.  The choice of `β` makes `0 ≤ τ ≤ λ` and `h > 0` for
`τ = (1+λ)h − 1`.

Summing first over subsets of `L` identifies the average of `h^B` with a ratio
of inhomogeneous partition functions (`eq:inhomogeneous-ratio`):

  `E_λ h^B = Z_G(τ, λ) / Z_G(λ, λ)`,

because a fixed subset of `R` has weight `λ^{|I∩R|}(1+λ)^B` and `(1+λ)h = 1+τ`.
Logarithmic differentiation in the `L`-activity, together with the occupation
lower bound `P_{s,λ}(v ∈ I) ≥ (s/(1+s))(1+λ)^{−d(v)}`, gives

  `d/ds log Z_G(s, λ) ≥ (1+s)^{−1} ∑_{v ∈ L} (1+λ)^{−d(v)}`,

and integrating from `τ` to `λ` yields
`|E_λ e^{itX}| ≤ h^{∑_{v∈L}(1+λ)^{−d(v)}}`.

Finally, for a forest choose the labelling so that `|L| ≥ n/2`.  Since
`∑_{v∈L} d(v) ≤ |E(F)| ≤ n`, Jensen's inequality gives
`∑_{v∈L}(1+λ)^{−d(v)} ≥ |L|(1+λ)^{−|E(F)|/|L|} ≥ n/(2(1+λ)²)`.
-/
import ErdosProblem993.HardCore

namespace ErdosProblem993

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

variable (G) in
/-- The inhomogeneous partition function `Z_G(s, λ)`: activity `s` on `L` and
activity `l` on the complement of `L`. -/
noncomputable def Zbi (S L : Finset V) (s l : ℝ) : ℝ :=
  ∑ J ∈ indepFinsets G S, s ^ (J ∩ L).card * l ^ (J \ L).card

/-! ### Basic properties of `Zbi` -/

/-- `Z_G(s, λ) > 0` already for nonnegative activities: every term is
nonnegative and the empty set contributes `1`. -/
theorem Zbi_pos_of_nonneg {S L : Finset V} {s l : ℝ} (hs : 0 ≤ s) (hl : 0 ≤ l) :
    0 < Zbi G S L s l := by
  unfold Zbi
  refine sum_pos' (fun J _ => by positivity) ⟨∅, empty_mem_indepFinsets S, ?_⟩
  simp

theorem Zbi_pos {S L : Finset V} {s l : ℝ} (hs : 0 < s) (hl : 0 < l) : 0 < Zbi G S L s l :=
  Zbi_pos_of_nonneg hs.le hl.le

theorem Zbi_nonneg {S L : Finset V} {s l : ℝ} (hs : 0 ≤ s) (hl : 0 ≤ l) :
    0 ≤ Zbi G S L s l :=
  (Zbi_pos_of_nonneg hs hl).le

omit [Fintype V] in
@[simp] theorem Zbi_self (S L : Finset V) (l : ℝ) : Zbi G S L l l = Zr G S l := by
  unfold Zbi Zr Zgen
  refine sum_congr rfl fun J _ => ?_
  rw [← pow_add, card_inter_add_card_sdiff]

/-- `Z_G(s, λ)` is monotone in the vertex set. -/
theorem Zbi_mono {S T L : Finset V} (hST : S ⊆ T) {s l : ℝ} (hs : 0 ≤ s) (hl : 0 ≤ l) :
    Zbi G S L s l ≤ Zbi G T L s l :=
  sum_le_sum_of_subset_of_nonneg (indepFinsets_mono hST) (fun J _ _ => by positivity)

/-! ### Root conditioning for `Zbi` -/

omit [Fintype V] in
/-- The weight of `insert u J` for `u ∉ J`. -/
private lemma weight_insert {L J : Finset V} {u : V} (huJ : u ∉ J) (s l : ℝ) :
    s ^ (insert u J ∩ L).card * l ^ (insert u J \ L).card =
      (if u ∈ L then s else l) * (s ^ (J ∩ L).card * l ^ (J \ L).card) := by
  by_cases huL : u ∈ L
  · rw [if_pos huL, insert_inter_of_mem huL, insert_sdiff_of_mem _ huL,
      card_insert_of_notMem (fun h => huJ (mem_inter.1 h).1), pow_succ]
    ring
  · rw [if_neg huL, insert_inter_of_notMem huL, insert_sdiff_of_notMem _ huL,
      card_insert_of_notMem (fun h => huJ (mem_sdiff.1 h).1), pow_succ]
    ring

/-- The total weight of the configurations containing `u`. -/
theorem sum_filter_mem_Zbi (S L : Finset V) {u : V} (hu : u ∈ S) (s l : ℝ) :
    ∑ J ∈ (indepFinsets G S).filter (fun J => u ∈ J), s ^ (J ∩ L).card * l ^ (J \ L).card =
      (if u ∈ L then s else l) * Zbi G (S \ closedNbr G u) L s l := by
  have hnot : ∀ J ∈ indepFinsets G (S \ closedNbr G u), u ∉ J := fun J hJ h =>
    (mem_sdiff.1 ((mem_indepFinsets.1 hJ).1 h)).2 (self_mem_closedNbr u)
  rw [indepFinsets_filter_mem S u hu, Zbi, mul_sum, sum_image]
  · exact sum_congr rfl fun J hJ => weight_insert (hnot J hJ) s l
  · intro J hJ J' hJ' hJJ'
    have e : insert u J = insert u J' := hJJ'
    rw [← erase_insert (hnot J hJ), ← erase_insert (hnot J' hJ'), e]

/-- The total weight of the configurations avoiding `u`. -/
theorem sum_filter_notMem_Zbi (S L : Finset V) (u : V) (s l : ℝ) :
    ∑ J ∈ (indepFinsets G S).filter (fun J => u ∉ J), s ^ (J ∩ L).card * l ^ (J \ L).card =
      Zbi G (S.erase u) L s l := by
  rw [indepFinsets_filter_notMem S u, Zbi]

/-- Root conditioning for the inhomogeneous partition function. -/
theorem Zbi_eq_erase_add (S L : Finset V) {u : V} (hu : u ∈ S) (s l : ℝ) :
    Zbi G S L s l = Zbi G (S.erase u) L s l +
      (if u ∈ L then s else l) * Zbi G (S \ closedNbr G u) L s l := by
  rw [Zbi, ← sum_filter_add_sum_filter_not (indepFinsets G S) (fun J => u ∈ J),
    sum_filter_mem_Zbi S L hu, sum_filter_notMem_Zbi S L u, add_comm]

/-- Deleting a vertex of `R` divides `Z_G(s, λ)` by at most `1 + λ`. -/
theorem Zbi_le_one_add_mul_erase {S L : Finset V} {u : V} (huL : u ∉ L) {s l : ℝ}
    (hs : 0 ≤ s) (hl : 0 ≤ l) :
    Zbi G S L s l ≤ (1 + l) * Zbi G (S.erase u) L s l := by
  by_cases hu : u ∈ S
  · rw [Zbi_eq_erase_add S L hu, if_neg huL, add_mul, one_mul]
    gcongr
    refine Zbi_mono (fun x hx => ?_) hs hl
    simp only [mem_sdiff, mem_closedNbr, not_or] at hx
    exact mem_erase.2 ⟨hx.2.1, hx.1⟩
  · rw [erase_eq_of_notMem hu]
    have := Zbi_nonneg (G := G) (S := S) (L := L) hs hl
    nlinarith

/-- Deleting a set `A` of vertices of `R` divides `Z_G(s, λ)` by at most `(1+λ)^{|A|}`;
this is `eq:absence` for the inhomogeneous model. -/
theorem Zbi_le_pow_mul_sdiff {S L A : Finset V} (hA : ∀ u ∈ A, u ∉ L) {s l : ℝ}
    (hs : 0 ≤ s) (hl : 0 ≤ l) :
    Zbi G S L s l ≤ (1 + l) ^ A.card * Zbi G (S \ A) L s l := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert u A huA ih =>
    have hA' : ∀ v ∈ A, v ∉ L := fun v hv => hA v (mem_insert_of_mem hv)
    calc Zbi G S L s l ≤ (1 + l) ^ A.card * Zbi G (S \ A) L s l := ih hA'
      _ ≤ (1 + l) ^ A.card * ((1 + l) * Zbi G ((S \ A).erase u) L s l) := by
          gcongr
          exact Zbi_le_one_add_mul_erase (hA u (mem_insert_self u A)) hs hl
      _ = (1 + l) ^ (insert u A).card * Zbi G (S \ insert u A) L s l := by
          rw [card_insert_of_notMem huA, sdiff_insert, pow_succ]; ring

/-! ### Fibre decomposition along `J ↦ J ∖ L`

When `L` is independent, an independent set `J ⊆ S` is the disjoint union of
`K = J ∖ L`, an independent subset of `S ∖ L`, and an arbitrary subset `A` of the
vertices of `L ∩ S` available given `K`, i.e. not adjacent to any vertex of `K`. -/

variable (G) in
/-- The vertices of `L ∩ S` available given the configuration `K` on `R`. -/
noncomputable def avail (S L K : Finset V) : Finset V := (S ∩ L) \ nbrSet G K

lemma mem_avail {S L K : Finset V} {a : V} :
    a ∈ avail G S L K ↔ (a ∈ S ∧ a ∈ L) ∧ ∀ k ∈ K, ¬ G.Adj k a := by
  simp [avail, nbrSet, mem_nbr]

omit [Fintype V] in
private lemma union_inter_eq_of_disjoint {K A L : Finset V} (hKL : Disjoint K L) (hAL : A ⊆ L) :
    (K ∪ A) ∩ L = A := by
  rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.1 hKL, inter_eq_left.2 hAL,
    empty_union]

omit [Fintype V] in
private lemma union_sdiff_eq_of_disjoint {K A L : Finset V} (hKL : Disjoint K L) (hAL : A ⊆ L) :
    (K ∪ A) \ L = K := by
  rw [union_sdiff_distrib, Finset.sdiff_eq_self_iff_disjoint.2 hKL, sdiff_eq_empty_iff_subset.2 hAL,
    union_empty]

/-- Summing over independent sets of `S` fibrewise over `J ∖ L`. -/
theorem sum_indepFinsets_eq_fibre {S L : Finset V} (h : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    {M : Type*} [AddCommMonoid M] (f : Finset V → M) :
    ∑ J ∈ indepFinsets G S, f J =
      ∑ K ∈ indepFinsets G (S \ L), ∑ A ∈ (avail G S L K).powerset, f (K ∪ A) := by
  have hmem : ∀ p : Finset V × Finset V,
      p ∈ (indepFinsets G S).image (fun J => (J \ L, J ∩ L)) ↔
        p.1 ∈ indepFinsets G (S \ L) ∧ p.2 ∈ (avail G S L p.1).powerset := by
    rintro ⟨K, A⟩
    simp only [mem_image, Prod.mk.injEq, mem_powerset]
    constructor
    · rintro ⟨J, hJ, rfl, rfl⟩
      obtain ⟨hJS, hJind⟩ := mem_indepFinsets.1 hJ
      refine ⟨mem_indepFinsets.2 ⟨sdiff_subset_sdiff hJS (Finset.Subset.refl L),
        (mem_indepFinsets.1 (indepFinsets_subset_mem hJ sdiff_subset)).2⟩, ?_⟩
      intro a ha
      rw [mem_inter] at ha
      rw [mem_avail]
      refine ⟨⟨hJS ha.1, ha.2⟩, fun k hk hadj => ?_⟩
      rw [mem_sdiff] at hk
      exact hJind (mem_coe.2 hk.1) (mem_coe.2 ha.1) (G.ne_of_adj hadj) hadj
    · rintro ⟨hK, hA⟩
      obtain ⟨hKS, hKind⟩ := mem_indepFinsets.1 hK
      have hKL : Disjoint K L := disjoint_of_subset_left hKS sdiff_disjoint
      have hAL : A ⊆ L := fun a ha => ((mem_avail.1 (hA ha)).1).2
      refine ⟨K ∪ A, mem_indepFinsets.2 ⟨?_, ?_⟩, union_sdiff_eq_of_disjoint hKL hAL,
        union_inter_eq_of_disjoint hKL hAL⟩
      · exact union_subset (hKS.trans sdiff_subset) (fun a ha => ((mem_avail.1 (hA ha)).1).1)
      · intro x hx y hy hne hadj
        rw [mem_coe, mem_union] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact hKind (mem_coe.2 hx) (mem_coe.2 hy) hne hadj
        · exact (mem_avail.1 (hA hy)).2 x hx hadj
        · exact (mem_avail.1 (hA hx)).2 y hy hadj.symm
        · exact h x (hAL hx) y (hAL hy) hadj
  have hinj : ∀ J ∈ indepFinsets G S, ∀ J' ∈ indepFinsets G S,
      (J \ L, J ∩ L) = (J' \ L, J' ∩ L) → J = J' := by
    intro J _ J' _ hJJ'
    simp only [Prod.mk.injEq] at hJJ'
    rw [← sdiff_union_inter J L, ← sdiff_union_inter J' L, hJJ'.1, hJJ'.2]
  calc ∑ J ∈ indepFinsets G S, f J
      = ∑ p ∈ (indepFinsets G S).image (fun J => (J \ L, J ∩ L)), f (p.1 ∪ p.2) := by
        rw [sum_image hinj]
        exact sum_congr rfl fun J _ => by rw [sdiff_union_inter]
    _ = _ := sum_finset_product' _ _ _ hmem (f := fun K A => f (K ∪ A))

omit [Fintype V] [DecidableEq V] in
private lemma sum_powerset_pow_card {R : Type*} [CommSemiring R] (x : R) (T : Finset V) :
    ∑ A ∈ T.powerset, x ^ A.card = (1 + x) ^ T.card := by
  rw [add_comm, ← sum_pow_mul_eq_add_pow x 1 T]
  simp

/-- A fixed configuration `K` on `R` has total weight `λ^{|K|}(1+s)^{B}`, `B` the number
of available vertices of `L`. -/
theorem Zbi_eq_sum_fibre {S L : Finset V} (h : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v) (s l : ℝ) :
    Zbi G S L s l =
      ∑ K ∈ indepFinsets G (S \ L), l ^ K.card * (1 + s) ^ (avail G S L K).card := by
  rw [Zbi, sum_indepFinsets_eq_fibre h]
  refine sum_congr rfl fun K hK => ?_
  have hKL : Disjoint K L := disjoint_of_subset_left (mem_indepFinsets.1 hK).1 sdiff_disjoint
  rw [← sum_powerset_pow_card, mul_sum]
  refine sum_congr rfl fun A hA => ?_
  have hAL : A ⊆ L := fun a ha => ((mem_avail.1 (mem_powerset.1 hA ha)).1).2
  rw [union_inter_eq_of_disjoint hKL hAL, union_sdiff_eq_of_disjoint hKL hAL, mul_comm]

/-- The numerator of the characteristic function, fibrewise: conditional on `K`, the
available vertices of `L` contribute `(1 + λe^{it})^B`. -/
theorem charFn_num_eq_sum_fibre {S L : Finset V} (h : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    (l t : ℝ) :
    ∑ J ∈ indepFinsets G S, Complex.exp (t * (J.card : ℝ) * Complex.I) * (l : ℂ) ^ J.card =
      ∑ K ∈ indepFinsets G (S \ L),
        Complex.exp (t * (K.card : ℝ) * Complex.I) * (l : ℂ) ^ K.card *
          (1 + l * Complex.exp (t * Complex.I)) ^ (avail G S L K).card := by
  rw [sum_indepFinsets_eq_fibre h]
  refine sum_congr rfl fun K hK => ?_
  have hKL : Disjoint K L := disjoint_of_subset_left (mem_indepFinsets.1 hK).1 sdiff_disjoint
  rw [← sum_powerset_pow_card, mul_sum]
  refine sum_congr rfl fun A hA => ?_
  have hAL : A ⊆ L := fun a ha => ((mem_avail.1 (mem_powerset.1 hA ha)).1).2
  have hKA : Disjoint K A := disjoint_of_subset_right hAL hKL
  have e1 : Complex.exp (t * (((K ∪ A).card : ℕ) : ℝ) * Complex.I) =
      Complex.exp (t * (K.card : ℝ) * Complex.I) * Complex.exp (t * Complex.I) ^ A.card := by
    rw [card_union_of_disjoint hKA, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e1, card_union_of_disjoint hKA, pow_add, mul_pow]
  ring

/-! ### The conditional modulus -/

private lemma norm_exp_mul_I (t x : ℝ) : ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
  rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

/-- `|1 + λe^{it}|² = (1+λ)² − 4λ sin²(t/2)`. -/
theorem norm_sq_one_add_mul_exp (l t : ℝ) :
    ‖(1 : ℂ) + l * Complex.exp (t * Complex.I)‖ ^ 2 =
      (1 + l) ^ 2 - 4 * l * Real.sin (t / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero,
    Complex.add_im, Complex.one_im, Complex.mul_im, zero_add]
  have hc : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have := Real.cos_two_mul (t / 2)
    rw [Real.cos_sq', show 2 * (t / 2) = t by ring] at this
    linarith
  have hs := Real.sin_sq_add_cos_sq t
  linear_combination l ^ 2 * hs + 2 * l * hc

/-- The conditional modulus is at most `(1+λ)h` with `h = 1 − β sin²(t/2)`,
`β = min{λ/(1+λ), 2λ/(1+λ)²}`; this is `√(1−z) ≤ 1 − z/2`. -/
theorem norm_one_add_mul_exp_le {l : ℝ} (hl : 0 < l) (t : ℝ) :
    ‖(1 : ℂ) + l * Complex.exp (t * Complex.I)‖ ≤
      (1 + l) * (1 - min (l / (1 + l)) (2 * l / (1 + l) ^ 2) * Real.sin (t / 2) ^ 2) := by
  set β := min (l / (1 + l)) (2 * l / (1 + l) ^ 2) with hβ
  set z := Real.sin (t / 2) ^ 2 with hz
  have hz0 : 0 ≤ z := sq_nonneg _
  have hz1 : z ≤ 1 := Real.sin_sq_le_one _
  have hβ1 : β ≤ l / (1 + l) := min_le_left _ _
  have hβ2 : β ≤ 2 * l / (1 + l) ^ 2 := min_le_right _ _
  have hβ0 : 0 ≤ β := le_min (by positivity) (by positivity)
  have hl1 : l / (1 + l) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hh : 0 ≤ 1 - β * z := by nlinarith
  have hβ2' : β * (1 + l) ^ 2 ≤ 2 * l := (le_div_iff₀ (by positivity)).1 hβ2
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (by linarith) hh) two_ne_zero,
    norm_sq_one_add_mul_exp, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_right hβ2' hz0, mul_nonneg (sq_nonneg (1 + l)) (sq_nonneg (β * z))]

/-! ### `eq:inhomogeneous-ratio` as an inequality -/

/-- `|E_λ e^{itX}| ≤ Z_G(τ, λ)/Z_G(λ, λ)` with `1 + τ = (1+λ)h`. -/
theorem norm_hcCharFn_le_Zbi_div {S L : Finset V} (h : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    {l : ℝ} (hl : 0 < l) (t : ℝ) :
    ‖hcCharFn G S l t‖ ≤
      Zbi G S L ((1 + l) * (1 - min (l / (1 + l)) (2 * l / (1 + l) ^ 2) * Real.sin (t / 2) ^ 2)
        - 1) l / Zr G S l := by
  have hZ : 0 < Zr G S l := Zbi_self S L l ▸ Zbi_pos hl hl
  rw [hcCharFn, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  refine div_le_div_of_nonneg_right ?_ hZ.le
  rw [charFn_num_eq_sum_fibre h, Zbi_eq_sum_fibre h]
  refine (norm_sum_le _ _).trans (sum_le_sum fun K _ => ?_)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_exp_mul_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hl.le, show 1 + ((1 + l) * (1 - min (l / (1 + l)) (2 * l / (1 + l) ^ 2)
      * Real.sin (t / 2) ^ 2) - 1) = (1 + l) * (1 - min (l / (1 + l)) (2 * l / (1 + l) ^ 2)
      * Real.sin (t / 2) ^ 2) by ring]
  gcongr
  exact norm_one_add_mul_exp_le hl t

/-! ### Occupation probabilities at inhomogeneous activities -/

/-- At inhomogeneous activities, a vertex of `L` is occupied with probability at
least `(s/(1+s))(1+λ)^{−d(v)}`, since its neighbours lie in `R` and each is
occupied with probability at most `λ/(1+λ)`, also after conditioning other
vertices of `R` to be absent. -/
theorem occ_bi_ge {S L : Finset V} (h : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    {s l : ℝ} (hs : 0 < s) (hl : 0 < l) {v : V} (hv : v ∈ S) (hvL : v ∈ L) :
    (s / (1 + s)) * (1 + l) ^ (-(degOn G S v : ℝ)) ≤
      (∑ J ∈ (indepFinsets G S).filter (fun J => v ∈ J),
          s ^ (J ∩ L).card * l ^ (J \ L).card) / Zbi G S L s l := by
  rw [sum_filter_mem_Zbi S L hv, if_pos hvL]
  have hZ : 0 < Zbi G S L s l := Zbi_pos hs hl
  have hZ' : 0 ≤ Zbi G (S \ closedNbr G v) L s l := Zbi_nonneg hs.le hl.le
  have hA : ∀ u ∈ nbr G v ∩ S, u ∉ L := fun u hu huL =>
    h v hvL u huL (mem_nbr.1 (mem_inter.1 hu).1)
  have h2 : Zbi G S L s l ≤ (1 + l) ^ degOn G S v * Zbi G (S \ nbr G v) L s l := by
    have := Zbi_le_pow_mul_sdiff (G := G) (S := S) hA hs.le hl.le
    rwa [show S \ (nbr G v ∩ S) = S \ nbr G v by
      ext x; simp only [mem_sdiff, mem_inter]; tauto] at this
  have h3 : Zbi G (S \ nbr G v) L s l = (1 + s) * Zbi G (S \ closedNbr G v) L s l := by
    have hv' : v ∈ S \ nbr G v := mem_sdiff.2 ⟨hv, fun h' => G.irrefl (mem_nbr.1 h')⟩
    rw [Zbi_eq_erase_add (S \ nbr G v) L hv', if_pos hvL]
    have e1 : (S \ nbr G v).erase v = S \ closedNbr G v := by
      ext x; simp only [mem_erase, mem_sdiff, mem_closedNbr, mem_nbr, not_or]; tauto
    have e2 : (S \ nbr G v) \ closedNbr G v = S \ closedNbr G v := by
      ext x; simp only [mem_sdiff, mem_closedNbr, mem_nbr, not_or]; tauto
    rw [e1, e2]; ring
  rw [h3] at h2
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast, le_div_iff₀ hZ]
  have hd : 0 < (1 + l) ^ degOn G S v := by positivity
  have h1s : (1 + s) ≠ 0 := by positivity
  calc s / (1 + s) * ((1 + l) ^ degOn G S v)⁻¹ * Zbi G S L s l
      ≤ s / (1 + s) * ((1 + l) ^ degOn G S v)⁻¹ *
          ((1 + l) ^ degOn G S v * ((1 + s) * Zbi G (S \ closedNbr G v) L s l)) := by
        gcongr
    _ = s * Zbi G (S \ closedNbr G v) L s l := by
        field_simp

omit [Fintype V] in
/-- The `s`-derivative of `Z_G(s, λ)`. -/
private lemma hasDerivAt_Zbi (S L : Finset V) (l s : ℝ) :
    HasDerivAt (fun x => Zbi G S L x l)
      (∑ J ∈ indepFinsets G S,
        ((J ∩ L).card : ℝ) * s ^ ((J ∩ L).card - 1) * l ^ (J \ L).card) s := by
  unfold Zbi
  exact HasDerivAt.fun_sum fun J _ => (hasDerivAt_pow _ s).mul_const _

/-- `s · d/ds Z_G(s,λ) = ∑_{v ∈ L} (weight of configurations containing v)`. -/
private lemma mul_deriv_Zbi_eq {S L : Finset V} (s l : ℝ) :
    s * ∑ J ∈ indepFinsets G S,
        ((J ∩ L).card : ℝ) * s ^ ((J ∩ L).card - 1) * l ^ (J \ L).card =
      ∑ v ∈ L ∩ S, ∑ J ∈ (indepFinsets G S).filter (fun J => v ∈ J),
        s ^ (J ∩ L).card * l ^ (J \ L).card := by
  simp_rw [sum_filter]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun J hJ => ?_
  have hJS : J ⊆ S := (mem_indepFinsets.1 hJ).1
  have hJL : J ∩ L = (L ∩ S).filter (fun v => v ∈ J) := by
    ext x
    simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨hxJ, hxL⟩; exact ⟨⟨hxL, hJS hxJ⟩, hxJ⟩
    · rintro ⟨⟨hxL, _⟩, hxJ⟩; exact ⟨hxJ, hxL⟩
  have hcard : ((J ∩ L).card : ℝ) = ∑ v ∈ L ∩ S, if v ∈ J then (1 : ℝ) else 0 := by
    rw [hJL, card_filter]
    push_cast
    rfl
  have hpow : s * (((J ∩ L).card : ℝ) * s ^ ((J ∩ L).card - 1)) =
      ((J ∩ L).card : ℝ) * s ^ (J ∩ L).card := by
    rcases Nat.eq_zero_or_pos (J ∩ L).card with h0 | hpos
    · rw [h0]; simp
    · rw [mul_left_comm, mul_pow_sub_one hpos.ne']
  calc s * (((J ∩ L).card : ℝ) * s ^ ((J ∩ L).card - 1) * l ^ (J \ L).card)
      = ((J ∩ L).card : ℝ) * (s ^ (J ∩ L).card * l ^ (J \ L).card) := by
        rw [← mul_assoc, hpow, mul_assoc]
    _ = ∑ v ∈ L ∩ S, if v ∈ J then s ^ (J ∩ L).card * l ^ (J \ L).card else 0 := by
        rw [hcard, sum_mul]
        refine sum_congr rfl fun v _ => ?_
        split_ifs <;> simp

/-- Logarithmic differentiation of `Z_G(s, λ)` in the `L`-activity. -/
theorem deriv_log_Zbi_ge {S L : Finset V} (h : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    {s l : ℝ} (hs : 0 < s) (hl : 0 < l) :
    (1 + s)⁻¹ * ∑ v ∈ L ∩ S, (1 + l) ^ (-(degOn G S v : ℝ))
      ≤ deriv (fun t => Real.log (Zbi G S L t l)) s := by
  have hZ : 0 < Zbi G S L s l := Zbi_pos hs hl
  rw [((hasDerivAt_Zbi S L l s).log hZ.ne').deriv]
  have key : (s / (1 + s)) * ∑ v ∈ L ∩ S, (1 + l) ^ (-(degOn G S v : ℝ)) ≤
      (s * ∑ J ∈ indepFinsets G S,
        ((J ∩ L).card : ℝ) * s ^ ((J ∩ L).card - 1) * l ^ (J \ L).card) / Zbi G S L s l := by
    rw [mul_deriv_Zbi_eq, sum_div, mul_sum]
    exact sum_le_sum fun v hv => occ_bi_ge h hs hl (mem_inter.1 hv).2 (mem_inter.1 hv).1
  have e : (s / (1 + s)) * ∑ v ∈ L ∩ S, (1 + l) ^ (-(degOn G S v : ℝ)) =
      s * ((1 + s)⁻¹ * ∑ v ∈ L ∩ S, (1 + l) ^ (-(degOn G S v : ℝ))) := by ring
  rw [e, mul_div_assoc] at key
  exact le_of_mul_le_mul_left key hs

/-! ### Integration from `τ` to `λ` -/

/-- `eq:inhomogeneous-ratio` combined with the integration above: the
conditional-independence bound on the characteristic function. -/
theorem norm_hcCharFn_le_pow {S L : Finset V} (h : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    {l : ℝ} (hl : 0 < l) (t : ℝ) :
    ‖hcCharFn G S l t‖ ≤
      (1 - min (l / (1 + l)) (2 * l / (1 + l) ^ 2) * Real.sin (t / 2) ^ 2)
        ^ (∑ v ∈ L ∩ S, (1 + l) ^ (-(degOn G S v : ℝ))) := by
  set β := min (l / (1 + l)) (2 * l / (1 + l) ^ 2) with hβ
  set z := Real.sin (t / 2) ^ 2 with hz
  set Sg := ∑ v ∈ L ∩ S, (1 + l) ^ (-(degOn G S v : ℝ)) with hSg
  set η := 1 - β * z with hη
  set τ := (1 + l) * η - 1 with hτ
  have hz0 : 0 ≤ z := sq_nonneg _
  have hz1 : z ≤ 1 := Real.sin_sq_le_one _
  have hβ1 : β ≤ l / (1 + l) := min_le_left _ _
  have hβ0 : 0 ≤ β := le_min (by positivity) (by positivity)
  have hl1 : l / (1 + l) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hη1 : η ≤ 1 := by rw [hη]; nlinarith
  have hβz : β * z ≤ l / (1 + l) := by
    have : β * z ≤ β := by nlinarith
    linarith
  have hη0 : 0 < η := by rw [hη]; linarith
  have hτ0 : 0 ≤ τ := by
    have h1 : (1 + l) * (1 - l / (1 + l)) = 1 := by field_simp; ring
    have h2 : (1 + l) * (1 - l / (1 + l)) ≤ (1 + l) * η := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [hη]; linarith
    rw [hτ]; linarith
  have hτl : τ ≤ l := by rw [hτ]; nlinarith
  have hSg0 : 0 ≤ Sg := sum_nonneg fun v _ => Real.rpow_nonneg (by linarith) _
  -- the monotone function `log Z(s,λ) − Sg log(1+s)`
  have hderiv : ∀ x : ℝ, 0 ≤ x →
      HasDerivAt (fun x => Real.log (Zbi G S L x l) - Sg * Real.log (1 + x))
        (deriv (fun t => Real.log (Zbi G S L t l)) x - Sg * (1 / (1 + x))) x := by
    intro x hx
    have hZ : Zbi G S L x l ≠ 0 := (Zbi_pos_of_nonneg hx hl.le).ne'
    have h1 := (hasDerivAt_Zbi S L l x).log hZ
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
      have := ((hasDerivAt_id x).const_add 1).log (by simp only [id]; positivity)
      simpa using this
    rw [h1.deriv]
    exact h1.sub (h2.const_mul Sg)
  have hmono : MonotoneOn (fun x => Real.log (Zbi G S L x l) - Sg * Real.log (1 + x))
      (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(hderiv x hx'.le).deriv]
      have := deriv_log_Zbi_ge (S := S) h hx' hl
      have e : Sg * (1 / (1 + x)) = (1 + x)⁻¹ * Sg := by ring
      rw [e]
      linarith
  have hmon := hmono (Set.mem_Ici.2 hτ0) (Set.mem_Ici.2 hl.le) hτl
  simp only at hmon
  have hZτ : 0 < Zbi G S L τ l := Zbi_pos_of_nonneg hτ0 hl.le
  have hZl : 0 < Zbi G S L l l := Zbi_pos hl hl
  have hratio : Zbi G S L τ l / Zbi G S L l l ≤ η ^ Sg := by
    rw [Real.rpow_def_of_pos hη0, ← Real.exp_log (div_pos hZτ hZl), Real.exp_le_exp,
      Real.log_div hZτ.ne' hZl.ne']
    have h1τ : Real.log (1 + τ) = Real.log (1 + l) + Real.log η := by
      rw [show 1 + τ = (1 + l) * η by rw [hτ]; ring, Real.log_mul (by positivity) hη0.ne']
    rw [h1τ] at hmon
    nlinarith [hmon]
  calc ‖hcCharFn G S l t‖ ≤ Zbi G S L τ l / Zr G S l := norm_hcCharFn_le_Zbi_div h hl t
    _ = Zbi G S L τ l / Zbi G S L l l := by rw [Zbi_self]
    _ ≤ η ^ Sg := hratio

/-! ### Forests: the edge count and Jensen -/

omit [Fintype V] [DecidableEq V] in
/-- In a forest, a vertex has at most one neighbour strictly closer to a fixed root. -/
private lemma parent_unique (hG : G.IsAcyclic) {r x y y' : V} (hr : G.Reachable r x)
    (hy : G.Adj x y) (hy' : G.Adj x y') (hdy : G.dist r y + 1 = G.dist r x)
    (hdy' : G.dist r y' + 1 = G.dist r x) : y = y' := by
  obtain ⟨p, hp, hpl⟩ := (hr.trans hy.reachable).exists_path_of_dist
  obtain ⟨p', hp', hpl'⟩ := (hr.trans hy'.reachable).exists_path_of_dist
  have hq : (p.concat hy.symm).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _
      (by rw [SimpleGraph.Walk.length_concat, hpl, hdy])
  have hq' : (p'.concat hy'.symm).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _
      (by rw [SimpleGraph.Walk.length_concat, hpl', hdy'])
  have huniq := hG.path_unique ⟨_, hq⟩ ⟨_, hq'⟩
  have := congrArg (fun q : G.Path r x => (q : G.Walk r x).penultimate) huniq
  simpa [SimpleGraph.Walk.penultimate_concat] using this

variable (G) in
/-- A representative of the connected component of `v`. -/
private noncomputable def croot (v : V) : V := (G.connectedComponentMk v).out

omit [Fintype V] [DecidableEq V] in
private lemma reachable_croot (v : V) : G.Reachable (croot G v) v :=
  SimpleGraph.ConnectedComponent.eq.1 (Quot.out_eq _)

omit [Fintype V] [DecidableEq V] in
private lemma croot_eq_of_adj {v w : V} (h : G.Adj v w) : croot G v = croot G w := by
  unfold croot
  rw [SimpleGraph.ConnectedComponent.sound h.reachable]

/-- In a forest, the degrees inside `S` of an independent set `L ⊆ S` sum to at most `|S|`:
the ordered pairs `(v, w)` with `v ∈ L`, `w ∈ S` adjacent inject into `S` by sending each
to the endpoint farther from a root of its component. -/
theorem sum_degOn_le_card_of_isAcyclic (hG : G.IsAcyclic) {S L : Finset V} (hLS : L ⊆ S)
    (h : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v) : ∑ v ∈ L, degOn G S v ≤ S.card := by
  classical
  have hcard : ∑ v ∈ L, degOn G S v = (L.sigma fun v => nbr G v ∩ S).card := by
    rw [card_sigma]; rfl
  rw [hcard]
  let far : (Σ _ : V, V) → V := fun p =>
    if G.dist (croot G p.1) p.1 + 1 = G.dist (croot G p.1) p.2 then p.2 else p.1
  have hfar : ∀ p ∈ L.sigma (fun v => nbr G v ∩ S),
      G.Adj p.1 p.2 ∧ croot G p.2 = croot G p.1 ∧
      ((far p = p.2 ∧ G.dist (croot G p.1) p.1 + 1 = G.dist (croot G p.1) p.2) ∨
       (far p = p.1 ∧ G.dist (croot G p.1) p.2 + 1 = G.dist (croot G p.1) p.1)) := by
    rintro ⟨v, w⟩ hp
    simp only [mem_sigma, mem_inter, mem_nbr] at hp
    obtain ⟨-, hadj, -⟩ := hp
    have hfv : far ⟨v, w⟩ =
        if G.dist (croot G v) v + 1 = G.dist (croot G v) w then w else v := rfl
    dsimp only
    rw [hfv]
    refine ⟨hadj, (croot_eq_of_adj hadj).symm, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable (croot G v) hadj (reachable_croot v)
      with h1 | h1
    · exact Or.inr ⟨if_neg (by omega), h1.symm⟩
    · exact Or.inl ⟨if_pos h1.symm, h1.symm⟩
  refine card_le_card_of_injOn far ?_ ?_
  · rintro ⟨v, w⟩ hp
    have hp' := hp
    rw [mem_coe, mem_sigma, mem_inter] at hp'
    obtain ⟨hv, -, hw⟩ := hp'
    rw [mem_coe]
    rcases (hfar ⟨v, w⟩ hp).2.2 with ⟨hf, -⟩ | ⟨hf, -⟩ <;> rw [hf]
    · exact hw
    · exact hLS hv
  · rintro ⟨v, w⟩ hp ⟨v', w'⟩ hp' heq
    obtain ⟨hadj, hroot, hcase⟩ := hfar ⟨v, w⟩ hp
    obtain ⟨hadj', hroot', hcase'⟩ := hfar ⟨v', w'⟩ hp'
    have hvL : v ∈ L := (mem_sigma.1 (mem_coe.1 hp)).1
    have hvL' : v' ∈ L := (mem_sigma.1 (mem_coe.1 hp')).1
    simp only at hadj hroot hcase hadj' hroot' hcase' heq
    rcases hcase with ⟨hf, hd⟩ | ⟨hf, hd⟩ <;> rcases hcase' with ⟨hf', hd'⟩ | ⟨hf', hd'⟩
    · have hww : w = w' := hf.symm.trans (heq.trans hf')
      subst hww
      have hr : croot G v = croot G v' := by rw [← hroot, ← hroot']
      rw [hr] at hd
      have := parent_unique hG ((reachable_croot v').trans hadj'.reachable) hadj.symm hadj'.symm
        hd hd'
      subst this; rfl
    · have hwv : w = v' := hf.symm.trans (heq.trans hf')
      subst hwv
      exact absurd hadj (h v hvL w hvL')
    · have hvw : v = w' := hf.symm.trans (heq.trans hf')
      subst hvw
      exact absurd hadj' (h v' hvL' v hvL)
    · have hvv : v = v' := hf.symm.trans (heq.trans hf')
      subst hvv
      have := parent_unique hG (reachable_croot v) hadj hadj' hd hd'
      subst this; rfl

omit [Fintype V] [DecidableEq V] in
/-- Jensen's inequality for the convex function `x ↦ b^x`, `0 < b ≤ 1`: if the `d(v)`
average at most `m` over `L` then `∑_{v∈L} b^{d(v)} ≥ |L| b^m`. -/
private lemma card_mul_rpow_le_sum_rpow {L : Finset V} (hL : L.Nonempty) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b ≤ 1) (d : V → ℕ) {m : ℝ} (hm : (∑ v ∈ L, (d v : ℝ)) ≤ m * L.card) :
    (L.card : ℝ) * b ^ m ≤ ∑ v ∈ L, b ^ (d v : ℝ) := by
  have hcard : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  have hJ := (convexOn_rpow_left hb0).map_sum_le (t := L) (w := fun _ => (L.card : ℝ)⁻¹)
    (p := fun v => (d v : ℝ)) (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  rw [← mul_sum, ← mul_sum] at hJ
  have hexp : (L.card : ℝ)⁻¹ * ∑ v ∈ L, (d v : ℝ) ≤ m := by
    rw [inv_mul_le_iff₀ hcard]; linarith [hm]
  have h1 : b ^ m ≤ b ^ ((L.card : ℝ)⁻¹ * ∑ v ∈ L, (d v : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hexp
  calc (L.card : ℝ) * b ^ m ≤ (L.card : ℝ) * ((L.card : ℝ)⁻¹ * ∑ v ∈ L, b ^ (d v : ℝ)) := by
        gcongr; exact h1.trans hJ
    _ = ∑ v ∈ L, b ^ (d v : ℝ) := by field_simp

/-- **Lemma 4.1** on a general vertex type, with the explicit constant `1/114244`. -/
theorem charFn_bound_aux (hG : G.IsAcyclic) (S : Finset V) {l : ℝ} (hl : l ∈ Kact) (t : ℝ) :
    ‖hcCharFn G S l t‖ ≤
      Real.exp (-(1 / 114244) * (S.card : ℝ) * Real.sin (t / 2) ^ 2) := by
  classical
  have hl0 : 0 < l := Kact_pos hl
  obtain ⟨hl1, hl2⟩ := hl
  -- a colour class of a proper 2-colouring containing at least half of `S`
  obtain ⟨C⟩ := hG.colorable_two
  obtain ⟨L, hLS, hLind, hLcard⟩ : ∃ L : Finset V, L ⊆ S ∧
      (∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v) ∧ S.card ≤ 2 * L.card := by
    have hsum : (S.filter (fun v => C v = 0)).card + (S.filter (fun v => ¬ C v = 0)).card
        = S.card := card_filter_add_card_filter_not _
    have key : ∀ a b : Fin 2, a ≠ 0 → b ≠ 0 → a = b := by decide
    by_cases hc : (S.filter (fun v => ¬ C v = 0)).card ≤ (S.filter (fun v => C v = 0)).card
    · refine ⟨S.filter (fun v => C v = 0), filter_subset _ _, ?_, by omega⟩
      intro u hu v hv hadj
      rw [mem_filter] at hu hv
      exact C.valid hadj (hu.2.trans hv.2.symm)
    · refine ⟨S.filter (fun v => ¬ C v = 0), filter_subset _ _, ?_, by omega⟩
      intro u hu v hv hadj
      rw [mem_filter] at hu hv
      exact C.valid hadj (key _ _ hu.2 hv.2)
  set β := min (l / (1 + l)) (2 * l / (1 + l) ^ 2) with hβ
  set z := Real.sin (t / 2) ^ 2 with hz
  have hLS' : L ∩ S = L := inter_eq_left.2 hLS
  have hbound := norm_hcCharFn_le_pow (S := S) hLind hl0 t
  rw [hLS'] at hbound
  set Sg := ∑ v ∈ L, (1 + l) ^ (-(degOn G S v : ℝ)) with hSg
  have hz0 : 0 ≤ z := sq_nonneg _
  have hz1 : z ≤ 1 := Real.sin_sq_le_one _
  have hβ1 : β ≤ l / (1 + l) := min_le_left _ _
  have hβ0 : 0 ≤ β := le_min (by positivity) (by positivity)
  have hl1' : l / (1 + l) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hη0 : 0 < 1 - β * z := by nlinarith
  have hSg0 : 0 ≤ Sg := sum_nonneg fun v _ => Real.rpow_nonneg (by linarith) _
  -- `h^Σ ≤ exp(−β sin²(t/2) Σ)`
  have h1 : (1 - β * z) ^ Sg ≤ Real.exp (-(β * z * Sg)) := by
    rw [Real.rpow_def_of_pos hη0, Real.exp_le_exp]
    have := Real.log_le_sub_one_of_pos hη0
    nlinarith [hSg0]
  -- `β Σ ≥ c |S|`
  have hβlow : (1 / 338 : ℝ) ≤ β := by
    refine le_min ?_ ?_
    · rw [le_div_iff₀ (by linarith)]; nlinarith
    · rw [le_div_iff₀ (by positivity)]; nlinarith
  have h2 : (1 / 114244 : ℝ) * S.card ≤ β * Sg := by
    rcases L.eq_empty_or_nonempty with hL | hL
    · have : S.card = 0 := by rw [hL] at hLcard; simpa using hLcard
      rw [this]; simp only [Nat.cast_zero, mul_zero]; positivity
    · have hb0 : (0 : ℝ) < (1 + l)⁻¹ := by positivity
      have hb1 : (1 + l)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hm : (∑ v ∈ L, (degOn G S v : ℝ)) ≤ 2 * L.card := by
        have := sum_degOn_le_card_of_isAcyclic hG hLS hLind
        have h' : ((∑ v ∈ L, degOn G S v : ℕ) : ℝ) ≤ 2 * L.card := by exact_mod_cast this.trans hLcard
        simpa [Nat.cast_sum] using h'
      have hJ := card_mul_rpow_le_sum_rpow hL hb0 hb1 (degOn G S) hm
      have hSgeq : Sg = ∑ v ∈ L, (1 + l)⁻¹ ^ (degOn G S v : ℝ) := by
        refine sum_congr rfl fun v _ => ?_
        rw [Real.inv_rpow (by linarith), Real.rpow_neg (by linarith)]
      rw [Real.inv_rpow (by linarith), Real.rpow_two] at hJ
      rw [hSgeq]
      have hsq : (1 + l) ^ 2 ≤ 169 := by nlinarith
      have hLpos : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
      have hinv : (1 / 169 : ℝ) ≤ ((1 + l) ^ 2)⁻¹ := by
        rw [one_div]; exact inv_anti₀ (by positivity) hsq
      have hSL : (S.card : ℝ) ≤ 2 * L.card := by exact_mod_cast hLcard
      calc (1 / 114244 : ℝ) * S.card ≤ (1 / 338) * ((L.card : ℝ) * (1 / 169)) := by nlinarith
        _ ≤ β * ((L.card : ℝ) * ((1 + l) ^ 2)⁻¹) := by gcongr
        _ ≤ β * ∑ v ∈ L, (1 + l)⁻¹ ^ (degOn G S v : ℝ) := by gcongr
  calc ‖hcCharFn G S l t‖ ≤ (1 - β * z) ^ Sg := hbound
    _ ≤ Real.exp (-(β * z * Sg)) := h1
    _ ≤ Real.exp (-(1 / 114244) * S.card * z) := by
        rw [Real.exp_le_exp]
        nlinarith [mul_le_mul_of_nonneg_right h2 hz0]

/-- **Lemma 4.1** (`eq:fourier`).  The constant `c` depends only on the fixed
activity interval `K = [1/4, 12]`. -/
theorem charFn_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic →
        ∀ (S : Finset (Fin n)) (l : ℝ), l ∈ Kact → ∀ t : ℝ,
          ‖hcCharFn G S l t‖ ≤ Real.exp (-c * (S.card : ℝ) * Real.sin (t / 2) ^ 2) :=
  ⟨1 / 114244, by norm_num, fun _ G hG S _ hl t => charFn_bound_aux hG S hl t⟩

end ErdosProblem993
