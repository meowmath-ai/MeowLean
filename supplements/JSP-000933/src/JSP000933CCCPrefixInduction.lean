import JSP000933CCCTupleCluster

namespace JSP000933
namespace OpenGraphForcing

abbrev IndexedEdge {X : Type} (K : Set (X × X)) (Y : OmegaOneIndex → X) :
    Set (OmegaOneIndex × OmegaOneIndex) :=
  {xy | (Y xy.1,Y xy.2) ∈ K}

noncomputable def prefixFinset_r64 {n : ℕ} (p : Fin (n+1) → OmegaOneIndex) : Finset OmegaOneIndex :=
  Finset.univ.image (fun i : Fin n => p i.castSucc)

theorem mem_prefixFinset_r64 {n : ℕ} {p : Fin (n+1) → OmegaOneIndex} {x : OmegaOneIndex} :
    x ∈ prefixFinset_r64 p ↔ ∃ i : Fin n, p i.castSucc = x := by
  classical
  simp [prefixFinset_r64,Finset.mem_image]

theorem card_prefixFinset_r64 {n : ℕ} {p : Fin (n+1) → OmegaOneIndex} (hp : StrictMono p) :
    (prefixFinset_r64 p).card = n := by
  classical
  have hI : Function.Injective (fun i : Fin n => p i.castSucc) :=
    hp.injective.comp (Fin.castSucc_injective n)
  unfold prefixFinset_r64
  rw [Finset.card_image_of_injective _ hI,Finset.card_univ,Fintype.card_fin]

theorem lowerPrefix_match_r64 {X : Type} {K : Set (X × X)} (Y : OmegaOneIndex → X)
    (hY : Function.Injective Y) {n : ℕ} (V : Set (Fin (n+1) → OmegaOneIndex))
    (hMono : ∀ p ∈ V, StrictMono p)
    (hDisj : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → Disjoint (Set.range p) (Set.range q))
    (hSelf : ∀ p ∈ V, ∀ i j, i ≠ j → (Y (p i),Y (p j)) ∈ K)
    (hIH : ∀ F : Set (Finset OmegaOneIndex), ¬ F.Countable →
      (∀ a ∈ F, a.card = n ∧ FiniteClique (IndexedEdge K Y) a) →
      ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ FiniteClique (IndexedEdge K Y) (a ∪ b)) :
    ∀ H : Set (Sample X n), H ⊆ orderedSample_r63 Y '' V → ¬ H.Countable →
      ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ Matched K a.1 b.1 := by
  classical
  intro H hHV hH
  by_cases nzero : n = 0
  · subst n
    have hNE : H.Nonempty := by
      by_contra h
      apply hH
      rw [Set.not_nonempty_iff_eq_empty.mp h]
      exact Set.countable_empty
    obtain ⟨a,ha⟩ := hNE
    have hSub : ¬ H ⊆ ({a} : Set (Sample X 0)) := fun h =>
      hH ((Set.countable_singleton a).mono h)
    obtain ⟨b,hb,hba⟩ := Set.not_subset.mp hSub
    exact ⟨a,ha,b,hb,fun e => hba (Set.mem_singleton_iff.mpr e.symm),fun i => Fin.elim0 i⟩
  · let f := orderedSample_r63 Y (n := n)
    let P : Set (Fin (n+1) → OmegaOneIndex) := V ∩ f ⁻¹' H
    have hP : ¬ P.Countable := by
      intro h
      apply hH
      apply (h.image f).mono
      intro a ha
      obtain ⟨p,hp,rfl⟩ := hHV ha
      exact ⟨p,⟨hp,ha⟩,rfl⟩
    let F := prefixFinset_r64 '' P
    have hInj : Set.InjOn (prefixFinset_r64 (n := n)) P := by
      intro p hp q hq he
      by_contra hn
      let i : Fin n := ⟨0,Nat.pos_of_ne_zero nzero⟩
      have hx : p i.castSucc ∈ prefixFinset_r64 p := mem_prefixFinset_r64.mpr ⟨i,rfl⟩
      rw [he] at hx
      obtain ⟨j,hj⟩ := mem_prefixFinset_r64.mp hx
      exact (Set.disjoint_left.mp (hDisj p hp.1 q hq.1 hn))
        ⟨i.castSucc,rfl⟩ ⟨j.castSucc,hj⟩
    have hF : ¬ F.Countable := fun h => hP (Set.countable_of_injective_of_countable_image hInj h)
    have hProp (s : Finset OmegaOneIndex) (hs : s ∈ F) :
        s.card = n ∧ FiniteClique (IndexedEdge K Y) s := by
      obtain ⟨p,hp,rfl⟩ := hs
      refine ⟨card_prefixFinset_r64 (hMono p hp.1),fun x hx y hy hxy => ?_⟩
      obtain ⟨i,rfl⟩ := mem_prefixFinset_r64.mp hx
      obtain ⟨j,rfl⟩ := mem_prefixFinset_r64.mp hy
      exact hSelf p hp.1 i.castSucc j.castSucc (fun he => hxy (congrArg p he))
    obtain ⟨a,ha,b,hb,hne,hCl⟩ := hIH F hF hProp
    obtain ⟨p,hp,rfl⟩ := ha
    obtain ⟨q,hq,rfl⟩ := hb
    have hpq : p ≠ q := fun he => hne (congrArg prefixFinset_r64 he)
    have hmatched (i : Fin n) : (Y (p i.castSucc),Y (q i.castSucc)) ∈ K := by
      have hpi : p i.castSucc ∈ prefixFinset_r64 p := mem_prefixFinset_r64.mpr ⟨i,rfl⟩
      have hqi : q i.castSucc ∈ prefixFinset_r64 q := mem_prefixFinset_r64.mpr ⟨i,rfl⟩
      refine hCl _ (Finset.mem_union.mpr (Or.inl hpi)) _ (Finset.mem_union.mpr (Or.inr hqi)) ?_
      intro he
      exact (Set.disjoint_left.mp (hDisj p hp.1 q hq.1 hpq))
        ⟨i.castSucc,rfl⟩ ⟨i.castSucc,he.symm⟩
    refine ⟨f p,hp.2,f q,hq.2,?_,hmatched⟩
    intro he
    apply hpq
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hY (congrArg Prod.snd he)
    · exact hY (congrFun (congrArg Prod.fst he) j)

end OpenGraphForcing
end JSP000933
