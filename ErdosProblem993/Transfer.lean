/-
# Isomorphism invariance, and Theorem 1.1 for an arbitrary vertex type

The uniform statements of this development are phrased on the vertex type
`Fin n`.  That is not a restriction: every finite graph is isomorphic to one on
`Fin (card V)`, and the independence sequence is an isomorphism invariant.

Phrasing them on `Fin n` is what makes the threshold `N₀` of Theorem 1.1
genuinely **absolute**.  Had the theorem been stated as
`∃ N₀, ∀ {V : Type u} …`, the constant would be allowed to depend on the
universe parameter `u`; here a single natural number, obtained once in `Type 0`,
serves every finite vertex type in every universe.
-/
import ErdosProblem993.Main

namespace ErdosProblem993

open Finset

universe u v

variable {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The independence sequence is an isomorphism invariant. -/
theorem icoeff_congr {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ x y : V, G.Adj x y ↔ H.Adj (e x) (e y)) (k : ℕ) :
    icoeff G univ k = icoeff H univ k := by
  unfold icoeff
  refine Finset.card_nbij' (fun J => J.map e.toEmbedding) (fun K => K.map e.symm.toEmbedding)
    ?_ ?_ ?_ ?_
  · intro J hJ
    rw [Finset.mem_coe, Finset.mem_filter, mem_indepFinsets] at hJ
    rw [Finset.mem_coe, Finset.mem_filter, mem_indepFinsets]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, by rw [Finset.card_map]; exact hJ.2⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    simp only [Equiv.coe_toEmbedding] at hxy ⊢
    rw [← he]
    exact hJ.1.2 (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) (fun h => hxy (congrArg e h))
  · intro K hK
    rw [Finset.mem_coe, Finset.mem_filter, mem_indepFinsets] at hK
    rw [Finset.mem_coe, Finset.mem_filter, mem_indepFinsets]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, by rw [Finset.card_map]; exact hK.2⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    simp only [Equiv.coe_toEmbedding] at hxy ⊢
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hK.1.2 (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) (fun h => hxy (congrArg e.symm h))
  · intro J _
    ext x
    simp
  · intro K _
    ext x
    simp

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Acyclicity is an isomorphism invariant. -/
theorem isAcyclic_congr {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ x y : V, G.Adj x y ↔ H.Adj (e x) (e y)) (hG : G.IsAcyclic) : H.IsAcyclic :=
  (SimpleGraph.Iso.isAcyclic_iff (⟨e, fun {a b} => (he a b).symm⟩ : G ≃g H)).1 hG

/-- Transporting a graph along `V ≃ Fin (card V)`. -/
noncomputable def toFin (G : SimpleGraph V) : SimpleGraph (Fin (Fintype.card V)) :=
  G.map (Equiv.toEmbedding (Fintype.equivFin V))

omit [DecidableEq V] in
theorem toFin_adj (G : SimpleGraph V) (x y : V) :
    (toFin G).Adj (Fintype.equivFin V x) (Fintype.equivFin V y) ↔ G.Adj x y := by
  show (G.map (Fintype.equivFin V).toEmbedding).Adj ((Fintype.equivFin V).toEmbedding x)
    ((Fintype.equivFin V).toEmbedding y) ↔ G.Adj x y
  exact SimpleGraph.map_adj_apply

/-- **Theorem 1.1** for an arbitrary finite vertex type: there is an absolute
integer `N₀` such that the independence sequence of every forest with at least
`N₀` vertices is unimodal.

The `N₀` here is literally the one produced by `main_fin`, so it does not depend
on the universe `u`. -/
theorem unimodal_of_isAcyclic :
    ∃ N₀ : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsAcyclic → N₀ ≤ Fintype.card V → IsUnimodal (icoeff G univ) := by
  obtain ⟨N₀, hN₀⟩ := main_fin
  refine ⟨N₀, ?_⟩
  intro V _ _ G hG hn
  have he : ∀ x y : V,
      G.Adj x y ↔ (toFin G).Adj (Fintype.equivFin V x) (Fintype.equivFin V y) :=
    fun x y => (toFin_adj G x y).symm
  have h := hN₀ (Fintype.card V) hn (toFin G) (isAcyclic_congr (Fintype.equivFin V) he hG)
  have hcongr : icoeff G univ = icoeff (toFin G) univ :=
    funext fun k => icoeff_congr (Fintype.equivFin V) he k
  rw [hcongr]
  exact h

end ErdosProblem993
