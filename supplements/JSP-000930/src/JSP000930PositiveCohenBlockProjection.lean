import JSP000930PositiveMarkedCohen

namespace JSP000930.Positive.Cohen

variable {X : Type}

def Supported (p : Trace X) (S : Set X) : Prop :=
  ∀ x ∈ p.1.dom, x ∈ S

abbrev BlockTrace (S : Set X) := {p : Trace X // Supported p S}

noncomputable def restrict (p : Trace X) (S : Set X) : BlockTrace S := by
  classical
  let cut : Condition X := ⟨p.1.dom.filter (fun x => x ∈ S), p.1.bit⟩
  refine ⟨normalize cut, ?_⟩
  intro x hx
  have h : x ∈ p.1.dom.filter (fun x => x ∈ S) := hx
  exact (Finset.mem_filter.mp h).2

theorem restrict_mem_dom (p : Trace X) (S : Set X) (x : X) :
    x ∈ (restrict p S).1.1.dom ↔ x ∈ p.1.dom ∧ x ∈ S := by
  classical
  exact Finset.mem_filter

theorem restrict_bit_eq (p : Trace X) (S : Set X) (x : X)
    (hx : x ∈ p.1.dom) (hs : x ∈ S) :
    (restrict p S).1.1.bit x = p.1.bit x := by
  classical
  have h : x ∈ p.1.dom.filter (fun x => x ∈ S) :=
    Finset.mem_filter.mpr ⟨hx, hs⟩
  exact normalize_bit _ x h

theorem le_restrict (p : Trace X) (S : Set X) : p ≤ (restrict p S).1 := by
  change Extends p.1 (restrict p S).1.1
  refine ⟨fun x hx => ((restrict_mem_dom p S x).mp hx).1, ?_⟩
  intro x hx
  obtain ⟨hp,hs⟩ := (restrict_mem_dom p S x).mp hx
  exact (restrict_bit_eq p S x hp hs).symm

theorem restrict_monotone (S : Set X) :
    Monotone (fun p : Trace X => (restrict p S).1) := by
  intro p q hpq
  change Extends p.1 q.1 at hpq
  change Extends (restrict p S).1.1 (restrict q S).1.1
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hq,hs⟩ := (restrict_mem_dom q S x).mp hx
    exact (restrict_mem_dom p S x).mpr ⟨hpq.1 hq,hs⟩
  · intro x hx
    obtain ⟨hq,hs⟩ := (restrict_mem_dom q S x).mp hx
    rw [restrict_bit_eq p S x (hpq.1 hq) hs, restrict_bit_eq q S x hq hs]
    exact hpq.2 x hq

theorem lift_stronger_block (p : Trace X) (S : Set X) (q : BlockTrace S)
    (hq : q.1 ≤ (restrict p S).1) :
    ∃ r : Trace X, r ≤ p ∧ r ≤ q.1 := by
  change Extends q.1.1 (restrict p S).1.1 at hq
  apply (trace_common_extension_iff p q.1).mpr
  intro x hp hx
  have hs : x ∈ S := q.2 x hx
  have hr : x ∈ (restrict p S).1.1.dom :=
    (restrict_mem_dom p S x).mpr ⟨hp,hs⟩
  exact (restrict_bit_eq p S x hp hs).symm.trans (hq.2 x hr).symm

theorem separate_domains_compatible {S T : Set X} (hd : Disjoint S T)
    (p : BlockTrace S) (q : BlockTrace T) :
    ∃ r : Trace X, r ≤ p.1 ∧ r ≤ q.1 := by
  apply (trace_common_extension_iff p.1 q.1).mpr
  intro x hp hq
  exact False.elim (Set.disjoint_left.mp hd (p.2 x hp) (q.2 x hq))

end JSP000930.Positive.Cohen
