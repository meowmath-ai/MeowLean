import JSP000933CCCRectangles

namespace JSP000933
namespace OpenGraphForcing

variable {X : Type} [TopologicalSpace X] [SecondCountableTopology X]

def orderedSample_r63 (Y : OmegaOneIndex → X) {n : ℕ}
    (p : Fin (n+1) → OmegaOneIndex) : Sample X n :=
  (fun i => Y (p i.castSucc),Y (p (Fin.last n)))

theorem orderedSample_injective_r63 {Y : OmegaOneIndex → X} (hY : Function.Injective Y) {n : ℕ} :
    Function.Injective (orderedSample_r63 Y (n := n)) := by
  intro a b h
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hY (congrArg Prod.snd h)
  · exact hY (congrFun (congrArg Prod.fst h) j)

theorem tupleCluster_pair_r63 {K : Set (X × X)} (hK : IsOpen K)
    (hSym : ∀ x y, (x,y) ∈ K → (y,x) ∈ K) (hIrr : ∀ x, (x,x) ∉ K)
    (S : AvoidanceSchedule X OmegaOneIndex)
    (hCode : ∀ n : ℕ, ∀ D : Set (Sample X n), D.Countable → ∃ e, S.graphCode e = ⟨n,D⟩)
    (Y : OmegaOneIndex → X) (hY : Function.Injective Y)
    (hAvoid : ∀ j, AvoidsEarlier K S j (fun i => Y i.1) (Y j))
    {n : ℕ} (G : Set (Fin (n+1) → OmegaOneIndex)) (hG : ¬ G.Countable)
    (hMono : ∀ p ∈ G, StrictMono p)
    (hDisj : ∀ p ∈ G, ∀ q ∈ G, p ≠ q → Disjoint (Set.range p) (Set.range q))
    (hCross : ∀ p ∈ G, ∀ q ∈ G, ∀ i j, i ≠ j → (Y (p i),Y (q j)) ∈ K)
    (hLower : ∀ H : Set (Sample X n), H ⊆ orderedSample_r63 Y '' G → ¬ H.Countable →
      ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ Matched K a.1 b.1) :
    ∃ p ∈ G, ∃ q ∈ G, p ≠ q ∧ ∀ i j, (Y (p i),Y (q j)) ∈ K := by
  classical
  let f := orderedSample_r63 Y (n := n)
  let F := f '' G
  have hf : Function.Injective f := orderedSample_injective_r63 hY
  have hExc : (Exceptional K F).Countable := exceptional_countable_r57 K F hLower
  obtain ⟨D,hD,hDsub,hDense⟩ := TopologicalSpace.exists_countable_dense_subset F
  obtain ⟨e,hE⟩ := hCode n D hD
  let last (p : Fin (n+1) → OmegaOneIndex) := p (Fin.last n)
  have hInj : Set.InjOn last G := by
    intro p hp q hq hEq
    by_contra hn
    exact (Set.disjoint_left.mp (hDisj p hp q hq hn))
      (Set.mem_range_self (Fin.last n)) ⟨Fin.last n,hEq.symm⟩
  let Bad := (f ⁻¹' Exceptional K F) ∪ (G ∩ last ⁻¹' Set.Iic e)
  have hLow : (Set.Iic e).Countable := by
    have hS : (Set.Iio e : Set OmegaOneIndex).Countable :=
      (OmegaOneIndex_initial_countable_r61 e).to_set
    apply (hS.insert e).mono
    intro j hj
    rcases lt_or_eq_of_le (Set.mem_Iic.mp hj) with h | h
    · exact Set.mem_insert_of_mem _ h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
  have hLowPart : (G ∩ last ⁻¹' Set.Iic e).Countable := by
    have hm : Set.MapsTo last (G ∩ last ⁻¹' Set.Iic e) (Set.Iic e) := fun _ h => h.2
    exact hm.countable_of_injOn (hInj.mono Set.inter_subset_left) hLow
  have hB : Bad.Countable := (hExc.preimage hf).union hLowPart
  have hNot : ¬ G ⊆ Bad := fun h => hG (hB.mono h)
  obtain ⟨p,hp,hpNot⟩ := Set.not_subset.mp hNot
  have hLast : e < last p := lt_of_not_ge (fun h => hpNot (Or.inr ⟨hp,h⟩))
  have hpF : f p ∈ F := ⟨p,hp,rfl⟩
  have hpCl : (f p).2 ∈ edgeCluster K F (f p).1 := by
    by_contra h
    exact hpNot (Or.inl ⟨hpF,h⟩)
  have hpClD : (f p).2 ∈ edgeCluster K D (f p).1 := by
    rw [← edgeCluster_eq_of_dense_subgraph_r56 hK hDsub hDense]
    exact hpCl
  let oldStem (i : Fin n) : ↥(Set.Iio (last p)) :=
    ⟨p i.castSucc,hMono p hp (Fin.castSucc_lt_last i)⟩
  have hAvoidP := (hAvoid (last p)).2.2 (⟨e,hLast⟩ : ↥(Set.Iio (last p)))
  have hCode' : S.graphCode (⟨e,hLast⟩ : ↥(Set.Iio (last p))).1 = ⟨n,D⟩ := hE
  rw [hCode'] at hAvoidP
  have hNon : ¬ Independent K (edgeCluster K D (f p).1) := by
    intro h
    exact hAvoidP oldStem h hpClD
  obtain ⟨x,hx,y,hy,hEdge⟩ : ∃ x ∈ edgeCluster K D (f p).1,
      ∃ y ∈ edgeCluster K D (f p).1, (x,y) ∈ K := by
    by_contra h
    exact hNon (fun x hx y hy hxy => h ⟨x,hx,y,hy,hxy⟩)
  obtain ⟨a,ha,b,hb,hMat,hLastEdge⟩ :=
    exists_matched_samples_of_edgeCluster_r56 hK hSym hx hy hEdge
  obtain ⟨s,hs,rfl⟩ := hDsub ha
  obtain ⟨t,ht,rfl⟩ := hDsub hb
  have hst : s ≠ t := by
    rintro rfl
    exact hIrr _ hLastEdge
  refine ⟨s,hs,t,ht,hst,fun i j => ?_⟩
  by_cases he : i = j
  · subst j
    refine Fin.lastCases ?_ (fun l => ?_) i
    · exact hLastEdge
    · exact hMat l
  · exact hCross s hs t ht i j he

end OpenGraphForcing
end JSP000933
