import JSP000930OldRawRefinementTransport

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B D I J : Type} [NontrivialCompleteBooleanAlgebra B]
variable [Preorder D] [Nonempty D] [Fintype I]

theorem finite_support_has_stage (A : D → J → Prop) (Y : J → Prop)
    (hMono : ∀ {d e},d ≤ e → ∀ j,A d j → A e j)
    (hDirected : ∀ d e : D,∃ f : D,d ≤ f ∧ e ≤ f)
    (hCover : ∀ j,Y j → ∃ d,A d j)
    (s : Finset J) (hS : ∀ j ∈ s,Y j) :
    ∃ d : D,∀ j ∈ s,A d j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨d⟩ := ‹Nonempty D›
    exact ⟨d,fun j hj => False.elim (by simpa using hj)⟩
  | @insert j s hj ih =>
    obtain ⟨d,hd⟩ := ih (fun k hk => hS k (Finset.mem_insert_of_mem hk))
    obtain ⟨e,he⟩ := hCover j (hS j (Finset.mem_insert_self j s))
    obtain ⟨f,hdf,hef⟩ := hDirected d e
    refine ⟨f,?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact hMono hef _ he
    · exact hMono hdf _ (hd _ hk)

theorem rowProduct_support_has_stage (A : D → J → Prop) (Y : J → Prop)
    (hMono : ∀ {d e},d ≤ e → ∀ j,A d j → A e j)
    (hDirected : ∀ d e : D,∃ f : D,d ≤ f ∧ e ≤ f)
    (hCover : ∀ j,Y j → ∃ d,A d j)
    (p : I → SupportedSymbolic J Y) :
    ∃ d : D,∀ i,SymbolicLabelAt (A d) (p i).val := by
  classical
  let s (i : I) : Finset J := match (p i).val with
    | none => ∅
    | some t => (t.pins.map Prod.fst).toFinset
  have hS (i : I) {j : J} (hj : j ∈ s i) : Y j := by
    cases he : (p i).val with
    | none => simp [s,he] at hj
    | some t =>
      have ht := (p i).2
      rw [he] at ht
      have hi : j ∈ (t.pins.map Prod.fst).toFinset := by simpa only [s,he] using hj
      exact ht j (List.mem_toFinset.mp hi)
  obtain ⟨d,hd⟩ := finite_support_has_stage A Y hMono hDirected hCover
    (Finset.univ.biUnion s) (by
      intro j hj
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hj
      exact hS i hi)
  refine ⟨d,?_⟩
  intro i
  cases he : (p i).val with
  | none => exact True.intro
  | some t =>
    intro j hj
    apply hd
    apply Finset.mem_biUnion.mpr
    exact ⟨i,Finset.mem_univ _,by simpa only [s,he] using (List.mem_toFinset.mpr hj)⟩

end JSP000930.Negative
