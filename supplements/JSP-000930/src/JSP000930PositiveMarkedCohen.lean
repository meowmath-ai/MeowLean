import JSP000930PositiveCohenConditions
import JSP000933MarkedBaseEmbedding

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {X : Type}

def Trace (X : Type) :=
  {p : Condition X // ∀ x, x ∉ p.dom → p.bit x = false}

def emptyTrace (X : Type) : Trace X :=
  ⟨⟨∅, fun _ => false⟩, fun _ _ => rfl⟩

instance : Preorder (Trace X) where
  le p q := Extends p.1 q.1
  le_refl p := extends_refl p.1
  le_trans _ _ _ hp hq := extends_trans hp hq

theorem trace_le_empty (p : Trace X) : p ≤ emptyTrace X := by
  change Extends p.1 (emptyTrace X).1
  refine ⟨?_, ?_⟩
  · intro x hx
    have : x ∈ (∅ : Finset X) := hx
    simpa using this
  · intro x hx
    have : x ∈ (∅ : Finset X) := hx
    simpa using this

noncomputable def normalize (p : Condition X) : Trace X := by
  classical
  exact ⟨⟨p.dom, fun x => if x ∈ p.dom then p.bit x else false⟩,
    fun x hx => by simp [hx]⟩

theorem normalize_dom (p : Condition X) : (normalize p).1.dom = p.dom := rfl

theorem normalize_bit (p : Condition X) (x : X) (hx : x ∈ p.dom) :
    (normalize p).1.bit x = p.bit x := by
  classical
  simp [normalize, hx]

theorem normalized_extends (p : Condition X) : Extends (normalize p).1 p :=
  ⟨fun _ hx => hx, normalize_bit p⟩

theorem trace_common_extension_iff (p q : Trace X) :
    (∃ r : Trace X, r ≤ p ∧ r ≤ q) ↔
      (∀ x ∈ p.1.dom, x ∈ q.1.dom → p.1.bit x = q.1.bit x) := by
  classical
  constructor
  · rintro ⟨r, hrp, hrq⟩
    exact (common_extension_iff p.1 q.1).mp ⟨r.1, hrp, hrq⟩
  · intro h
    obtain ⟨r, hrp, hrq⟩ := (common_extension_iff p.1 q.1).mpr h
    exact ⟨normalize r, extends_trans (normalized_extends r) hrp,
      extends_trans (normalized_extends r) hrq⟩

theorem trace_decide_fresh (p : Trace X) (x : X) (b : Bool)
    (hx : x ∉ p.1.dom) :
    ∃ q : Trace X, q ≤ p ∧ x ∈ q.1.dom ∧ q.1.bit x = b := by
  classical
  let q := prescribe p.1 x b
  have h := prescribe_sets p.1 x b
  exact ⟨normalize q,
    extends_trans (normalized_extends q) (prescribe_extends p.1 x b hx),
    h.1, (normalize_bit q x h.1).trans h.2⟩

noncomputable def valuedCohen (B X : Type) [CompleteBooleanAlgebra B] :
    ValuedPoset B (Trace X) := by
  classical
  exact
    { valid := fun _ => ⊤
      refines := fun p q => if p ≤ q then ⊤ else ⊥
      refine_valid := fun _ _ => by simp
      refl := fun p => by simp
      trans := by
        intro n m k
        by_cases hn : n ≤ m
        · by_cases hm : m ≤ k
          · simp [hn, hm, hn.trans hm]
          · simp [hm]
        · simp [hn]
      weakest := emptyTrace X
      weakest_valid := rfl
      weaker := fun p => by simp [trace_le_empty] }

abbrev CohenBA (B X : Type) [CompleteBooleanAlgebra B] :=
  TotalBA (valuedCohen B X)

variable {B : Type} [CompleteBooleanAlgebra B]

theorem cohen_total_le_iff (p q : TotalCondition (valuedCohen B X)) :
    p ≤ q ↔ p.mask ≤ q.mask ∧ p.trace ≤ q.trace := by
  classical
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hnot
    have hm : p.mask ≤ (valuedCohen B X).refines p.trace q.trace := h.2
    simp [valuedCohen, hnot] at hm
    exact p.nonzero hm
  · rintro ⟨hm, ht⟩
    refine ⟨hm, ?_⟩
    change p.mask ≤ (valuedCohen B X).refines p.trace q.trace
    simp [valuedCohen, ht]

end JSP000930.Positive.Cohen
