import JSP000930ActualIndependentSuccessor

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.BooleanCompletion JSP000933.ForcingTransport

variable {B M N : Type} [CompleteBooleanAlgebra B]

def taggedValid (Q : ValuedPoset B N) (load : M → Option N) (m : M) : B :=
  (load m).elim ⊥ Q.valid

def taggedRefines (Q : ValuedPoset B N) (load : M → Option N) (m n : M) : B :=
  (load m).elim ⊥ (fun r => (load n).elim ⊥ (Q.refines r))

def taggedValuedPoset (Q : ValuedPoset B N) (load : M → Option N) (zero : M)
    (hZero : load zero = some Q.weakest) : ValuedPoset B M where
  valid := taggedValid Q load
  refines := taggedRefines Q load
  refine_valid := by
    intro x y
    cases hx : load x <;> cases hy : load y <;>
      simp only [taggedValid,taggedRefines,hx,hy,Option.elim_none,Option.elim_some,bot_le]
    exact Q.refine_valid _ _
  refl := by
    intro x
    cases hx : load x <;>
      simp only [taggedValid,taggedRefines,hx,Option.elim_none,Option.elim_some,le_rfl]
    exact Q.refl _
  trans := by
    intro x y z
    cases hx : load x <;> cases hy : load y <;> cases hz : load z <;>
      simp only [taggedRefines,hx,hy,hz,Option.elim_none,Option.elim_some,bot_le,inf_bot_eq,bot_inf_eq]
    exact Q.trans _ _ _
  weakest := zero
  weakest_valid := by simp only [taggedValid,hZero,Option.elim_some,Q.weakest_valid]
  weaker := by
    intro x
    cases hx : load x <;> simp only [taggedValid,taggedRefines,hx,hZero,Option.elim_none,
      Option.elim_some,le_rfl]
    exact Q.weaker _

theorem taggedCondition_has_real_label (Q : ValuedPoset B N) (load : M → Option N)
    (zero : M) (hZero : load zero = some Q.weakest) (p : TotalCondition (taggedValuedPoset Q load zero hZero)) :
    load p.trace = some ((load p.trace).getD Q.weakest) := by
  cases he : load p.trace with
  | some t => rfl
  | none =>
    have hp : p.mask ≤ taggedValid Q load p.trace := p.valid
    rw [taggedValid,he] at hp
    exact (p.nonzero (le_bot_iff.mp hp)).elim

def taggedCondition_decode (Q : ValuedPoset B N) (load : M → Option N)
    (zero : M) (hZero : load zero = some Q.weakest) (p : TotalCondition (taggedValuedPoset Q load zero hZero)) :
    TotalCondition Q :=
  ⟨p.mask,(load p.trace).getD Q.weakest,p.nonzero,by
    have h : p.mask ≤ taggedValid Q load p.trace := p.valid
    unfold taggedValid at h
    rw [taggedCondition_has_real_label Q load zero hZero p] at h
    exact h⟩

theorem taggedCondition_decode_le_iff (Q : ValuedPoset B N) (load : M → Option N)
    (zero : M) (hZero : load zero = some Q.weakest)
    (p q : TotalCondition (taggedValuedPoset Q load zero hZero)) :
    taggedCondition_decode Q load zero hZero p ≤ taggedCondition_decode Q load zero hZero q ↔ p ≤ q := by
  change (p.mask≤q.mask ∧ p.mask≤Q.refines _ _) ↔ (p.mask≤q.mask ∧ p.mask≤taggedRefines Q load p.trace q.trace)
  have hp := taggedCondition_has_real_label Q load zero hZero p
  have hq := taggedCondition_has_real_label Q load zero hZero q
  unfold taggedRefines
  conv_rhs => rw [hp,hq]
  rfl

def taggedCondition_encode (Q : ValuedPoset B N) (load : M → Option N)
    (zero : M) (hZero : load zero = some Q.weakest)
    (put : N → M) (hPut : ∀ n,load (put n) = some n) (p : TotalCondition Q) :
    TotalCondition (taggedValuedPoset Q load zero hZero) :=
  ⟨p.mask,put p.trace,p.nonzero,by
    change p.mask ≤ taggedValid Q load (put p.trace)
    rw [taggedValid,hPut]
    exact p.valid⟩

theorem totalCondition_eq_of_data {Q : ValuedPoset B N} (p q : TotalCondition Q)
    (hB : p.mask = q.mask) (hN : p.trace = q.trace) : p = q := by
  cases p
  cases q
  cases hB
  cases hN
  rfl

theorem taggedCondition_decode_encode (Q : ValuedPoset B N) (load : M → Option N)
    (zero : M) (hZero : load zero = some Q.weakest)
    (put : N → M) (hPut : ∀ n,load (put n) = some n) (p : TotalCondition Q) :
    taggedCondition_decode Q load zero hZero (taggedCondition_encode Q load zero hZero put hPut p) = p := by
  refine totalCondition_eq_of_data _ p ?_ ?_
  · rfl
  change (load (put p.trace)).getD Q.weakest = p.trace
  rw [hPut] <;> rfl

noncomputable def taggedDenseMap (Q : ValuedPoset B N) (load : M → Option N)
    (zero : M) (hZero : load zero = some Q.weakest)
    (put : N → M) (hPut : ∀ n,load (put n) = some n) :
    DenseForcingMap (TotalCondition (taggedValuedPoset Q load zero hZero)) (TotalCondition Q) where
  map := taggedCondition_decode Q load zero hZero
  monotone := fun _ _ h => (taggedCondition_decode_le_iff Q load zero hZero _ _).mpr h
  dense := fun p => ⟨taggedCondition_encode Q load zero hZero put hPut p,
    (taggedCondition_decode_encode Q load zero hZero put hPut p).le⟩
  reflect_compatible := by
    intro p q h
    obtain ⟨r,hrp,hrq⟩ := h
    let s := taggedCondition_encode Q load zero hZero put hPut r
    have hs := taggedCondition_decode_encode Q load zero hZero put hPut r
    exact ⟨s,(taggedCondition_decode_le_iff Q load zero hZero _ _).mp (hs.le.trans hrp),
      (taggedCondition_decode_le_iff Q load zero hZero _ _).mp (hs.le.trans hrq)⟩

end JSP000930.Negative
