import JSP000930PositiveMarkedCohen
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace JSP000930.Positive.Cohen

open Cardinal

variable {X : Type}

noncomputable def traceGraph (p : Trace X) : Finset (X × Bool) := by
  classical
  exact p.1.dom.image fun x => (x, p.1.bit x)

theorem mem_traceGraph (p : Trace X) (x : X) (b : Bool) :
    (x,b) ∈ traceGraph p ↔ x ∈ p.1.dom ∧ p.1.bit x = b := by
  classical
  unfold traceGraph
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
    have hyx : y = x := congrArg Prod.fst he
    subst y
    exact ⟨hy, congrArg Prod.snd he⟩
  · rintro ⟨hx,hb⟩
    exact Finset.mem_image.mpr ⟨x,hx,congrArg (Prod.mk x) hb⟩

theorem traceGraph_injective : Function.Injective (traceGraph (X := X)) := by
  classical
  intro p q h
  have hd : p.1.dom = q.1.dom := by
    ext x
    constructor
    · intro hx
      have h' := (mem_traceGraph p x (p.1.bit x)).mpr ⟨hx,rfl⟩
      rw [h] at h'
      exact ((mem_traceGraph q x (p.1.bit x)).mp h').1
    · intro hx
      have h' := (mem_traceGraph q x (q.1.bit x)).mpr ⟨hx,rfl⟩
      rw [← h] at h'
      exact ((mem_traceGraph p x (q.1.bit x)).mp h').1
  have hb : p.1.bit = q.1.bit := by
    funext x
    by_cases hx : x ∈ p.1.dom
    · have h' := (mem_traceGraph p x (p.1.bit x)).mpr ⟨hx,rfl⟩
      rw [h] at h'
      exact ((mem_traceGraph q x (p.1.bit x)).mp h').2.symm
    · have hy : x ∉ q.1.dom := by rwa [hd] at hx
      exact (p.2 x hx).trans (q.2 x hy).symm
  apply Subtype.ext
  have helper (a b : Condition X) (h₁ : a.dom = b.dom) (h₂ : a.bit = b.bit) : a = b := by
    cases a
    cases b
    cases h₁
    cases h₂
    rfl
  exact helper p.1 q.1 hd hb

noncomputable def traceGraphEmbedding (X : Type) : Trace X ↪ Finset (X × Bool) where
  toFun := traceGraph
  inj' := traceGraph_injective

theorem trace_card_le_finset (X : Type) :
    Cardinal.mk (Trace X) ≤ Cardinal.mk (Finset (X × Bool)) :=
  Cardinal.mk_le_of_injective traceGraph_injective

end JSP000930.Positive.Cohen
