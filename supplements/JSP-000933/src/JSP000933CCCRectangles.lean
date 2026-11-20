import JSP000933CCCSchedule

open Filter
open scoped Topology

namespace JSP000933
namespace OpenGraphForcing

variable {X : Type} [TopologicalSpace X] [SecondCountableTopology X]

abbrev RectCode (X : Type) [TopologicalSpace X] [SecondCountableTopology X] (n : ℕ) :=
  Fin n → ↥(TopologicalSpace.countableBasis X)

def IsCrossRectangle {n : ℕ} (K : Set (X × X)) (W : RectCode X n) : Prop :=
  ∀ i j : Fin n, i ≠ j → (W i).1 ×ˢ (W j).1 ⊆ K

theorem exists_basis_rectangle_r62 {K : Set (X × X)} (hK : IsOpen K)
    {n : ℕ} (p : Fin n → X) (hp : ∀ i j, i ≠ j → (p i,p j) ∈ K) :
    ∃ W : RectCode X n, (∀ i, p i ∈ (W i).1) ∧ IsCrossRectangle K W := by
  classical
  have hPair (i j : Fin n) :
      ∃ U V : Set X, IsOpen U ∧ p i ∈ U ∧ IsOpen V ∧ p j ∈ V ∧
        (i ≠ j → U ×ˢ V ⊆ K) := by
    by_cases h : i = j
    · exact ⟨Set.univ,Set.univ,isOpen_univ,Set.mem_univ _,isOpen_univ,Set.mem_univ _,
        fun hn => False.elim (hn h)⟩
    · obtain ⟨U,V,hU,hi,hV,hj,hK⟩ := mem_nhds_prod_iff'.mp (hK.mem_nhds (hp i j h))
      exact ⟨U,V,hU,hi,hV,hj,fun _ => hK⟩
  choose U V hU hUi hV hVj hRect using hPair
  let W (i : Fin n) := (⋂ j, U i j) ∩ (⋂ j, V j i)
  have hWOpen (i : Fin n) : IsOpen (W i) :=
    (isOpen_iInter_of_finite (hU i)).inter (isOpen_iInter_of_finite (fun j => hV j i))
  have hWM (i : Fin n) : p i ∈ W i :=
    ⟨Set.mem_iInter.mpr (hUi i),Set.mem_iInter.mpr (fun j => hVj j i)⟩
  have hB (i : Fin n) : ∃ B : ↥(TopologicalSpace.countableBasis X), p i ∈ B.1 ∧ B.1 ⊆ W i := by
    obtain ⟨B,hB,hpB,hS⟩ :=
      (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open (hWM i) (hWOpen i)
    exact ⟨⟨B,hB⟩,hpB,hS⟩
  choose B hBM hBS using hB
  refine ⟨B,hBM,fun i j hij z hz => ?_⟩
  have hi : z.1 ∈ W i := hBS i hz.1
  have hj : z.2 ∈ W j := hBS j hz.2
  exact hRect i j hij ⟨Set.mem_iInter.mp hi.1 j,Set.mem_iInter.mp hj.2 i⟩

theorem exists_uncountable_rectangular_slice_r62 {T : Type} {n : ℕ}
    {K : Set (X × X)} (hK : IsOpen K) (F : Set T) (hF : ¬ F.Countable)
    (p : T → Fin n → X) (hP : ∀ a ∈ F, ∀ i j, i ≠ j → (p a i,p a j) ∈ K) :
    ∃ G ⊆ F, ¬ G.Countable ∧ ∀ a ∈ G, ∀ b ∈ G, ∀ i j, i ≠ j → (p a i,p b j) ∈ K := by
  classical
  let sub (W : RectCode X n) : Set T :=
    {a | a ∈ F ∧ (∀ i, p a i ∈ (W i).1) ∧ IsCrossRectangle K W}
  have hSub : F ⊆ ⋃ W, sub W := by
    intro a ha
    obtain ⟨W,hW,hR⟩ := exists_basis_rectangle_r62 hK (p a) (hP a ha)
    exact Set.mem_iUnion.mpr ⟨W,ha,hW,hR⟩
  have hE : ∃ W : RectCode X n, ¬ (sub W).Countable := by
    by_contra h
    have hc (W : RectCode X n) : (sub W).Countable := by
      by_contra hn
      exact h ⟨W,hn⟩
    exact hF ((Set.countable_iUnion hc).mono hSub)
  obtain ⟨W,hW⟩ := hE
  exact ⟨sub W,fun _ h => h.1,hW,fun a ha b hb i j hij =>
    ha.2.2 i j hij ⟨ha.2.1 i,hb.2.1 j⟩⟩

end OpenGraphForcing
end JSP000933
