import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

namespace JSP000930.Positive.Cohen

universe u v

structure Condition (X : Type u) where
  dom : Finset X
  bit : X → Bool

variable {X : Type u}

def Extends (p q : Condition X) : Prop :=
  q.dom ⊆ p.dom ∧ ∀ x ∈ q.dom, p.bit x = q.bit x

theorem extends_refl (p : Condition X) : Extends p p :=
  ⟨fun _ hx => hx, fun _ _ => rfl⟩

theorem extends_trans {p q r : Condition X}
    (hpq : Extends p q) (hqr : Extends q r) : Extends p r :=
  ⟨fun _ hx => hpq.1 (hqr.1 hx),
    fun x hx => (hpq.2 x (hqr.1 hx)).trans (hqr.2 x hx)⟩

section
variable [DecidableEq X]

def merge (p q : Condition X) : Condition X :=
  ⟨p.dom ∪ q.dom, fun x => if x ∈ p.dom then p.bit x else q.bit x⟩

theorem merge_extends_left (p q : Condition X) : Extends (merge p q) p := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  · intro x hx
    simp [merge, hx]

theorem merge_extends_right (p q : Condition X)
    (h : ∀ x ∈ p.dom, x ∈ q.dom → p.bit x = q.bit x) :
    Extends (merge p q) q := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_union.mpr (Or.inr hx)
  · intro x hx
    by_cases hy : x ∈ p.dom
    · simpa [merge, hy] using h x hy hx
    · simp [merge, hy]

theorem common_extension_iff (p q : Condition X) :
    (∃ r, Extends r p ∧ Extends r q) ↔
      (∀ x ∈ p.dom, x ∈ q.dom → p.bit x = q.bit x) := by
  constructor
  · rintro ⟨r, hp, hq⟩ x hx hy
    exact (hp.2 x hx).symm.trans (hq.2 x hy)
  · intro h
    exact ⟨merge p q, merge_extends_left p q, merge_extends_right p q h⟩

def prescribe (p : Condition X) (x : X) (b : Bool) : Condition X :=
  ⟨insert x p.dom, fun y => if y = x then b else p.bit y⟩

theorem prescribe_extends (p : Condition X) (x : X) (b : Bool)
    (h : x ∉ p.dom) : Extends (prescribe p x b) p := by
  refine ⟨?_, ?_⟩
  · intro y hy
    exact Finset.mem_insert.mpr (Or.inr hy)
  · intro y hy
    have hne : y ≠ x := fun he => h (he ▸ hy)
    simp [prescribe, hne]

theorem prescribe_sets (p : Condition X) (x : X) (b : Bool) :
    x ∈ (prescribe p x b).dom ∧ (prescribe p x b).bit x = b := by
  simp [prescribe]

end

def usedRows {I : Type u} {J : Type v} [DecidableEq I]
    (p : Condition (I × J)) : Finset I :=
  p.dom.image Prod.fst

theorem outside_row_not_mem {I : Type u} {J : Type v} [DecidableEq I]
    (p : Condition (I × J)) {i : I} (h : i ∉ usedRows p) (j : J) :
    (i, j) ∉ p.dom := by
  intro hj
  exact h (Finset.mem_image.mpr ⟨(i, j), hj, rfl⟩)

end JSP000930.Positive.Cohen
