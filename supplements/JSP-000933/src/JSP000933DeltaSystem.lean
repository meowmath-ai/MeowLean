import JSP000933CCCSchedule

namespace JSP000933
namespace OpenGraphForcing

def IsDeltaSystem {T : Type} [DecidableEq T] (G : Set (Finset T)) (root : Finset T) : Prop :=
  ∀ a ∈ G, ∀ b ∈ G, a ≠ b → a ∩ b = root

private theorem exists_deltaSystem_of_card_r74 {T : Type} [DecidableEq T] :
    ∀ n : ℕ, ∀ F : Set (Finset T), ¬ F.Countable → (∀ a ∈ F, a.card = n) →
      ∃ root G, G ⊆ F ∧ ¬ G.Countable ∧ IsDeltaSystem G root := by
  intro n
  induction n with
  | zero =>
    intro F hF hCard
    exfalso
    apply hF
    apply (Set.countable_singleton (∅ : Finset T)).mono
    intro a ha
    exact Finset.card_eq_zero.mp (hCard a ha)
  | succ n ih =>
    intro F hF hCard
    by_cases hc : ∃ c : T, ¬ {s : Finset T | s ∈ F ∧ c ∈ s}.Countable
    · obtain ⟨c,hc⟩ := hc
      let W : Set (Finset T) := {s : Finset T | s ∈ F ∧ c ∈ s}
      let E : Set (Finset T) := (fun a : Finset T => a.erase c) '' W
      have hInj : Set.InjOn (fun a : Finset T => a.erase c) W := by
        intro a ha b hb hab
        exact congrArg Subtype.val (eraseOnContaining_injective_r59 c
          (a₁ := ⟨a,ha.2⟩) (a₂ := ⟨b,hb.2⟩) hab)
      have hE : ¬ E.Countable := fun h => hc (Set.countable_of_injective_of_countable_image hInj h)
      have hECard (a : Finset T) (ha : a ∈ E) : a.card = n := by
        obtain ⟨s,hs,rfl⟩ := ha
        rw [Finset.card_erase_of_mem hs.2,hCard s hs.1] <;> omega
      obtain ⟨r,H,hHE,hH,hDelta⟩ := ih E hE hECard
      let G : Set (Finset T) := {a | a ∈ W ∧ a.erase c ∈ H}
      refine ⟨insert c r,G,fun a ha => ha.1.1,?_,?_⟩
      · intro h
        apply hH
        apply (h.image (fun a : Finset T => a.erase c)).mono
        intro a ha
        obtain ⟨s,hs,his⟩ := hHE ha
        change s.erase c = a at his
        exact ⟨s,⟨hs,by rwa [his]⟩,his⟩
      · intro a ha b hb hab
        have hne : a.erase c ≠ b.erase c := fun h => hab (hInj ha.1 hb.1 h)
        have hi := hDelta _ ha.2 _ hb.2 hne
        apply Finset.ext
        intro t
        by_cases ht : t = c
        · subst t
          simp [ha.1.2,hb.1.2]
        · have ht' : t ∈ a.erase c ∩ b.erase c ↔ t ∈ r := by rw [hi]
          simpa [Finset.mem_inter,Finset.mem_erase,Finset.mem_insert,ht] using ht'
    · have hHit (c : T) : ({s : Finset T | s ∈ F ∧ c ∈ s}).Countable := by
        by_contra h
        exact hc ⟨c,h⟩
      obtain ⟨G,hGF,hG,hDis⟩ := exists_disjoint_uncountable_subfamily_r59
        OmegaOneIndex_not_countable_r61 OmegaOneIndex_initial_countable_r61 F hF hHit
      refine ⟨∅,G,hGF,hG,fun a ha b hb hab => ?_⟩
      apply Finset.ext
      intro t
      constructor
      · intro ht
        obtain ⟨hta,htb⟩ := Finset.mem_inter.mp ht
        exact False.elim (Finset.disjoint_left.mp (hDis a ha b hb hab) hta htb)
      · intro ht
        exact False.elim (Finset.notMem_empty _ ht)

theorem exists_deltaSystem_r74 {T : Type} [DecidableEq T] (F : Set (Finset T))
    (hF : ¬ F.Countable) :
    ∃ root G, G ⊆ F ∧ ¬ G.Countable ∧ IsDeltaSystem G root := by
  obtain ⟨n,hn⟩ := exists_fixedCard_uncountable_r59 F hF
  obtain ⟨root,G,hG,hGc,hD⟩ := exists_deltaSystem_of_card_r74 n
    {a | a ∈ F ∧ a.card = n} hn (fun _ h => h.2)
  exact ⟨root,G,fun a ha => (hG ha).1,hGc,hD⟩

end OpenGraphForcing
end JSP000933
