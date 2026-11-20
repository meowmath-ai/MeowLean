import JSP000933DeltaSystem

namespace JSP000933
namespace FiniteSupport

variable {A : Type} [LinearOrder A] {N : A → Type}

abbrev Trace (N : A → Type) := (i : A) → Option (N i)

def present (p : Trace N) (i : A) : Prop := ∃ n, p i = some n

def cut (p : Trace N) (a : A) : Trace N := fun i => if i < a then p i else none

theorem cut_apply_of_lt {p : Trace N} {i a : A} (h : i < a) : cut p a i = p i := by
  simp [cut,h]

theorem cut_apply_of_not_lt {p : Trace N} {i a : A} (h : ¬ i < a) : cut p a i = none := by
  simp [cut,h]

theorem cut_cut_of_le_r75 (p : Trace N) {a b : A} (h : a ≤ b) :
    cut (cut p b) a = cut p a := by
  funext i
  by_cases hi : i < a
  · simp [cut,hi,hi.trans_le h]
  · simp [cut,hi]

abbrev LocalOrder (N : A → Type) := (i : A) → Trace N → N i → N i → Prop

def coordinateLE (leAt : LocalOrder N) (i : A) (p q : Trace N) : Prop :=
  ∀ s : N i, q i = some s → ∃ t : N i, p i = some t ∧ leAt i (cut p i) t s

structure Rules (N : A → Type) where
  valid : (i : A) → Trace N → N i → Prop
  leAt : LocalOrder N
  refl : ∀ i p t, leAt i p t t
  trans : ∀ i p r s t, leAt i p r s → leAt i p s t → leAt i p r t
  persist_valid : ∀ i p q t, (∀ j < i, coordinateLE leAt j p q) →
    valid i (cut q i) t → valid i (cut p i) t
  persist_le : ∀ i p q s t, (∀ j < i, coordinateLE leAt j p q) →
    leAt i (cut q i) s t → leAt i (cut p i) s t

structure Condition (R : Rules N) where
  trace : Trace N
  finite : ({i | present trace i} : Set A).Finite
  valid : ∀ i (s : N i), trace i = some s → R.valid i (cut trace i) s

instance conditionPreorder (R : Rules N) : Preorder (Condition R) where
  le p q := ∀ i, coordinateLE R.leAt i p.trace q.trace
  le_refl p i s hs := ⟨s,hs,R.refl ..⟩
  le_trans p q r hpq hqr i t ht := by
    obtain ⟨s,hs,hst⟩ := hqr i t ht
    obtain ⟨v,hv,hvs⟩ := hpq i s hs
    exact ⟨v,hv,R.trans i _ _ _ _ hvs
      (R.persist_le i p.trace q.trace _ _ (fun j _ => hpq j) hst)⟩

abbrev Before (R : Rules N) (a : A) :=
  {p : Condition R // ∀ i, present p.trace i → i < a}

def restrict {R : Rules N} (p : Condition R) (a : A) : Before R a := by
  refine ⟨⟨cut p.trace a,?_,?_⟩,?_⟩
  · apply p.finite.subset
    rintro i ⟨s,hs⟩
    by_cases hi : i < a
    · exact ⟨s,by simpa [cut,hi] using hs⟩
    · simp [cut,hi] at hs
  · intro i s hs
    by_cases hi : i < a
    · rw [cut_cut_of_le_r75 p.trace hi.le]
      exact p.valid i s (by simpa [cut,hi] using hs)
    · simp [cut,hi] at hs
  · rintro i ⟨s,hs⟩
    by_contra hi
    simp [cut,hi] at hs

theorem restrict_mono_r75 {R : Rules N} {p q : Condition R} (h : p ≤ q) (a : A) :
    restrict p a ≤ restrict q a := by
  change ∀ i, coordinateLE R.leAt i (cut p.trace a) (cut q.trace a)
  intro i s hs
  by_cases hi : i < a
  · obtain ⟨t,ht,hle⟩ := h i s (by simpa [cut,hi] using hs)
    exact ⟨t,by simpa [cut,hi] using ht,by rwa [cut_cut_of_le_r75 p.trace hi.le]⟩
  · simp [cut,hi] at hs

theorem restrict_coherent_r75 {R : Rules N} (p : Condition R) {a b : A} (h : a ≤ b) :
    (restrict (restrict p b).1 a).1.trace = (restrict p a).1.trace :=
  cut_cut_of_le_r75 p.trace h

noncomputable def support {R : Rules N} (p : Condition R) : Finset A := p.finite.toFinset

@[simp] theorem mem_support_r75 {R : Rules N} (p : Condition R) (i : A) :
    i ∈ support p ↔ present p.trace i := p.finite.mem_toFinset

end FiniteSupport
end JSP000933
