import JSP000933CCCPrefixInduction
import Mathlib.Data.Finset.Sort

open scoped Cardinal

namespace JSP000933
namespace OpenGraphForcing

variable {X : Type} [TopologicalSpace X] [SecondCountableTopology X]

private theorem indexedClique_union_of_cross_r65 {K : Set (X × X)} (Y : OmegaOneIndex → X)
    (hSym : ∀ x y, (x,y) ∈ K → (y,x) ∈ K) {a b : Finset OmegaOneIndex}
    (ha : FiniteClique (IndexedEdge K Y) a) (hb : FiniteClique (IndexedEdge K Y) b)
    (hCross : ∀ i ∈ a, ∀ j ∈ b, (Y i,Y j) ∈ K) :
    FiniteClique (IndexedEdge K Y) (a ∪ b) := by
  intro i hi j hj hne
  rcases Finset.mem_union.mp hi with hi | hi <;> rcases Finset.mem_union.mp hj with hj | hj
  · exact ha i hi j hj hne
  · exact hCross i hi j hj
  · exact hSym (Y j) (Y i) (hCross j hj i hi)
  · exact hb i hi j hj hne

private theorem disjoint_fixedCard_pair_r65 {K : Set (X × X)} (hK : IsOpen K)
    (hSym : ∀ x y, (x,y) ∈ K → (y,x) ∈ K) (hIrr : ∀ x, (x,x) ∉ K)
    (S : AvoidanceSchedule X OmegaOneIndex)
    (hCode : ∀ n : ℕ, ∀ D : Set (Sample X n), D.Countable → ∃ e, S.graphCode e = ⟨n,D⟩)
    (Y : OmegaOneIndex → X) (hY : Function.Injective Y)
    (hAvoid : ∀ j, AvoidsEarlier K S j (fun i => Y i.1) (Y j))
    {n : ℕ} (G : Set (Finset OmegaOneIndex)) (hG : ¬ G.Countable)
    (hProps : ∀ a ∈ G, a.card = n+1 ∧ FiniteClique (IndexedEdge K Y) a)
    (hDisj : ∀ a ∈ G, ∀ b ∈ G, a ≠ b → Disjoint a b)
    (hIH : ∀ F : Set (Finset OmegaOneIndex), ¬ F.Countable →
      (∀ a ∈ F, a.card = n ∧ FiniteClique (IndexedEdge K Y) a) →
      ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ FiniteClique (IndexedEdge K Y) (a ∪ b)) :
    ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ FiniteClique (IndexedEdge K Y) (a ∪ b) := by
  classical
  let O (s : ↥G) : Fin (n+1) ≃o ↥(s.1) := s.1.orderIsoOfFin ((hProps s.1 s.2).1)
  let P (s : ↥G) (i : Fin (n+1)) : OmegaOneIndex := (O s i).1
  have hMono (s : ↥G) : StrictMono (P s) := fun i j hij => (O s).strictMono hij
  have hRange (s : ↥G) : Set.range (P s) = (s.1 : Set OmegaOneIndex) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact (O s i).2
    · intro hx
      refine ⟨(O s).symm ⟨x,hx⟩,?_⟩
      exact congrArg Subtype.val ((O s).apply_symm_apply ⟨x,hx⟩)
  have hInject : Function.Injective P := by
    intro a b h
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← hRange a,← hRange b,h]
  have hU : ¬ (Set.univ : Set ↥G).Countable := by
    intro h
    exact hG (Set.countable_coe_iff.mp (Set.countable_univ_iff.mp h))
  have hOwn (s : ↥G) (i j : Fin (n+1)) (hij : i ≠ j) : (Y (P s i),Y (P s j)) ∈ K :=
    (hProps s.1 s.2).2 (P s i) (O s i).2 (P s j) (O s j).2
      (fun h => hij ((hMono s).injective h))
  obtain ⟨B,_,hB,hCross⟩ := exists_uncountable_rectangular_slice_r62 hK Set.univ hU
    (fun s i => Y (P s i)) (fun s _ => hOwn s)
  let U := P '' B
  have hU' : ¬ U.Countable := fun h => hB (Set.countable_of_injective_of_countable_image hInject.injOn h)
  have hUmono (a : Fin (n+1) → OmegaOneIndex) (ha : a ∈ U) : StrictMono a := by
    obtain ⟨s,_,rfl⟩ := ha
    exact hMono s
  have hUdis (a : Fin (n+1) → OmegaOneIndex) (ha : a ∈ U)
      (b : Fin (n+1) → OmegaOneIndex) (hb : b ∈ U) (hne : a ≠ b) :
      Disjoint (Set.range a) (Set.range b) := by
    obtain ⟨s,hs,rfl⟩ := ha
    obtain ⟨t,ht,rfl⟩ := hb
    have hsne : s.1 ≠ t.1 := fun h => hne (congrArg P (Subtype.ext h))
    rw [hRange s,hRange t]
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (hDisj s.1 s.2 t.1 t.2 hsne) hx hy
  have hUCross (a : Fin (n+1) → OmegaOneIndex) (ha : a ∈ U)
      (b : Fin (n+1) → OmegaOneIndex) (hb : b ∈ U) (i j : Fin (n+1)) (hne : i ≠ j) :
      (Y (a i),Y (b j)) ∈ K := by
    obtain ⟨s,hs,rfl⟩ := ha
    obtain ⟨t,ht,rfl⟩ := hb
    exact hCross s hs t ht i j hne
  have hLower := lowerPrefix_match_r64 (K := K) Y hY U hUmono hUdis
    (fun p hp => hUCross p hp p hp) hIH
  obtain ⟨a,ha,b,hb,hne,hEdges⟩ :=
    tupleCluster_pair_r63 hK hSym hIrr S hCode Y hY hAvoid U hU' hUmono hUdis hUCross hLower
  obtain ⟨s,hs,rfl⟩ := ha
  obtain ⟨t,ht,rfl⟩ := hb
  refine ⟨s.1,s.2,t.1,t.2,fun h => hne (congrArg P (Subtype.ext h)),?_⟩
  apply indexedClique_union_of_cross_r65 Y hSym (hProps s.1 s.2).2 (hProps t.1 t.2).2
  intro x hx y hy
  have hxR : x ∈ Set.range (P s) := by rw [hRange s]; exact hx
  have hyR : y ∈ Set.range (P t) := by rw [hRange t]; exact hy
  obtain ⟨i,rfl⟩ := hxR
  obtain ⟨j,rfl⟩ := hyR
  exact hEdges i j

theorem fixedCard_finiteClique_pair_r65 {K : Set (X × X)} (hK : IsOpen K)
    (hSym : ∀ x y, (x,y) ∈ K → (y,x) ∈ K) (hIrr : ∀ x, (x,x) ∉ K)
    (S : AvoidanceSchedule X OmegaOneIndex)
    (hCode : ∀ n : ℕ, ∀ D : Set (Sample X n), D.Countable → ∃ e, S.graphCode e = ⟨n,D⟩)
    (Y : OmegaOneIndex → X) (hY : Function.Injective Y)
    (hAvoid : ∀ j, AvoidsEarlier K S j (fun i => Y i.1) (Y j)) :
    ∀ n : ℕ, ∀ F : Set (Finset OmegaOneIndex), ¬ F.Countable →
      (∀ a ∈ F, a.card = n ∧ FiniteClique (IndexedEdge K Y) a) →
      ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ FiniteClique (IndexedEdge K Y) (a ∪ b) := by
  classical
  intro n
  induction n with
  | zero =>
    intro F hF hProps
    exfalso
    apply hF
    apply (Set.countable_singleton (∅ : Finset OmegaOneIndex)).mono
    intro a ha
    exact Set.mem_singleton_iff.mpr (Finset.card_eq_zero.mp (hProps a ha).1)
  | succ n ih =>
    intro F hF hProps
    by_cases h : ∃ c : OmegaOneIndex, ¬ {s : Finset OmegaOneIndex | s ∈ F ∧ c ∈ s}.Countable
    · obtain ⟨c,hc⟩ := h
      let T : Set (Finset OmegaOneIndex) := {s | s ∈ F ∧ c ∈ s}
      let f (s : Finset OmegaOneIndex) := s.erase c
      let G := f '' T
      have hInj : Set.InjOn f T := by
        intro a ha b hb he
        have hx := congrArg (insert c) he
        simpa only [f,Finset.insert_erase ha.2,Finset.insert_erase hb.2] using hx
      have hG : ¬ G.Countable := fun h => hc (Set.countable_of_injective_of_countable_image hInj h)
      have hGProp (a : Finset OmegaOneIndex) (ha : a ∈ G) :
          a.card = n ∧ FiniteClique (IndexedEdge K Y) a := by
        obtain ⟨s,hs,rfl⟩ := ha
        refine ⟨?_,(hProps s hs.1).2.subset_r59 (Finset.erase_subset _ _)⟩
        rw [show (f s).card = s.card - 1 from Finset.card_erase_of_mem hs.2,(hProps s hs.1).1]
        omega
      obtain ⟨a,ha,b,hb,hNe,hCl⟩ := ih G hG hGProp
      obtain ⟨a',ha',rfl⟩ := ha
      obtain ⟨b',hb',rfl⟩ := hb
      refine ⟨a',ha'.1,b',hb'.1,fun e => hNe (congrArg f e),?_⟩
      exact restore_shared_vertex_r59 (hProps a' ha'.1).2 (hProps b' hb'.1).2 ha'.2 hb'.2 hCl
    · have hHit (c : OmegaOneIndex) : {s : Finset OmegaOneIndex | s ∈ F ∧ c ∈ s}.Countable := by
        by_contra hc
        exact h ⟨c,hc⟩
      obtain ⟨G,hSub,hG,hDisj⟩ := exists_disjoint_uncountable_subfamily_r59
        OmegaOneIndex_not_countable_r61 OmegaOneIndex_initial_countable_r61 F hF hHit
      obtain ⟨a,ha,b,hb,hne,hCl⟩ := disjoint_fixedCard_pair_r65 hK hSym hIrr S hCode
        Y hY hAvoid G hG (fun s hs => hProps s (hSub hs)) hDisj ih
      exact ⟨a,hSub ha,b,hSub hb,hne,hCl⟩

theorem exists_indexed_ccc_clique_forcing_r65
    {K : Set (X × X)} (hK : IsOpen K) (hSym : ∀ x y, (x,y) ∈ K → (y,x) ∈ K)
    (hIrr : ∀ x, (x,x) ∉ K) (hChrom : UncountablyChromatic K)
    (embed : X → RealCode) (hEmbed : Function.Injective embed)
    (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ Y : OmegaOneIndex → X, Function.Injective Y ∧
      ∀ F : Set (Finset OmegaOneIndex), ¬ F.Countable →
        (∀ a ∈ F, FiniteClique (IndexedEdge K Y) a) →
        ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ FiniteClique (IndexedEdge K Y) (a ∪ b) := by
  obtain ⟨S,_,hCode⟩ := exists_exhaustive_avoidanceSchedule_r61 embed hEmbed CH
  obtain ⟨Y,hY,hAvoid⟩ := exists_avoidingSequence_r58 hChrom hIrr OmegaOneIndex_initial_countable_r61 S
  refine ⟨Y,hY,fun F hF hProps => ?_⟩
  obtain ⟨n,hn⟩ := exists_fixedCard_uncountable_r59 F hF
  obtain ⟨a,ha,b,hb,hne,hCl⟩ :=
    fixedCard_finiteClique_pair_r65 hK hSym hIrr S hCode Y hY hAvoid n _ hn
      (fun a ha => ⟨ha.2,hProps a ha.1⟩)
  exact ⟨a,ha.1,b,hb.1,hne,hCl⟩

end OpenGraphForcing
end JSP000933
