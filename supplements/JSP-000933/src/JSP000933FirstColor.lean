import JSP000933NeatFamily

namespace JSP000933

noncomputable section

def representativeLiftOfHom {f g : EUWeight}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    (A : Set ℕ) : Set ℕ :=
  Classical.choose (weightedClass_surjective g.weight g.nonneg
    (F (weightedClass f.weight f.nonneg A)))

theorem representativeLiftOfHom_spec {f g : EUWeight}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    (A : Set ℕ) :
    weightedClass g.weight g.nonneg (representativeLiftOfHom (f := f) (g := g) F A) =
      F (weightedClass f.weight f.nonneg A) :=
  Classical.choose_spec (weightedClass_surjective g.weight g.nonneg
    (F (weightedClass f.weight f.nonneg A)))

theorem representativeLiftOfHom_inter_error {f g : EUWeight}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    (A B : Set ℕ) :
    WeightedNull g.weight
      (xorSet (representativeLiftOfHom (f := f) (g := g) F A ∩ representativeLiftOfHom (f := f) (g := g) F B)
        (representativeLiftOfHom (f := f) (g := g) F (A ∩ B))) := by
  apply (weightedClass_eq_iff g.weight g.nonneg _ _).mp
  simp only [weightedClass_inter,representativeLiftOfHom_spec,map_mul]

private theorem crossing_xor_subset_r12 (a b c d H : Set ℕ) :
    xorSet (a ∩ d) (b ∩ c) ⊆ xorSet (H ∩ a) c ∪ xorSet (H ∩ b) d := by
  intro m hm
  simp only [xorSet,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff] at hm ⊢
  tauto

theorem countable_of_crossing_first_color {X : Type*} (g : EUWeight)
    (F : Set ℕ → Set ℕ) (cap payload : X → Set ℕ)
    (hbelow : ∀ p : X, payload p ⊆ cap p)
    (hMeet : ∀ A B : Set ℕ, WeightedNull g.weight (xorSet (F A ∩ F B) (F (A ∩ B))))
    {ε : ℝ} (hε : 0 < ε)
    (hCross : ∀ p q : X, p ≠ q →
      cap p ∩ payload q = cap q ∩ payload p ∧
      xorSet (F (cap p) ∩ F (payload q)) (F (cap q) ∩ F (payload p))
        ∉ euPrefixSmall g (ε + ε)) :
    Countable X := by
  classical
  let U : Set ℕ := ⋃ p : X, payload p
  have hCut (p : X) : U ∩ cap p = payload p := by
    ext m
    constructor
    · rintro ⟨hm,hmp⟩
      obtain ⟨q,hmq⟩ := Set.mem_iUnion.mp hm
      by_cases h : p = q
      · simpa only [h] using hmq
      · have hX := (hCross p q h).1
        have hh : m ∈ cap p ∩ payload q := ⟨hmp,hmq⟩
        rw [hX] at hh
        exact hh.2
    · intro hm
      exact ⟨Set.mem_iUnion.mpr ⟨p,hm⟩,hbelow p hm⟩
  let E (p : X) := xorSet (F U ∩ F (cap p)) (F (payload p))
  have hE (p : X) : WeightedNull g.weight (E p) := by
    have h := hMeet U (cap p)
    rw [hCut p] at h
    exact h
  have hTail (p : X) : ∃ N : ℕ, E p \ Set.Iio N ∈ euPrefixSmall g ε :=
    weightedNull_has_euPrefixSmall_tail g (hE p) hε
  choose N hN using hTail
  let code (p : X) : ℕ × Finset ℕ × Finset ℕ :=
    (N p,restrictSet (Finset.range (N p)) (F (cap p)),restrictSet (Finset.range (N p)) (F (payload p)))
  by_contra hUnc
  have hpq : ∃ p q : X, p ≠ q ∧ code p = code q := by
    by_contra hn
    apply hUnc
    refine Function.Injective.countable (f := code) (fun p q hp => ?_)
    by_contra hpq
    exact hn ⟨p,q,hpq,hp⟩
  obtain ⟨p,q,hne,heq⟩ := hpq
  have hNpq : N p = N q := congrArg Prod.fst heq
  have hCap : restrictSet (Finset.range (N p)) (F (cap p)) =
      restrictSet (Finset.range (N p)) (F (cap q)) := by
    have h : restrictSet (Finset.range (N p)) (F (cap p)) =
        restrictSet (Finset.range (N q)) (F (cap q)) := congrArg (fun z => z.2.1) heq
    simpa only [← hNpq] using h
  have hPayload : restrictSet (Finset.range (N p)) (F (payload p)) =
      restrictSet (Finset.range (N p)) (F (payload q)) := by
    have h : restrictSet (Finset.range (N p)) (F (payload p)) =
        restrictSet (Finset.range (N q)) (F (payload q)) := congrArg (fun z => z.2.2) heq
    simpa only [← hNpq] using h
  let D := xorSet (F (cap p) ∩ F (payload q)) (F (cap q) ∩ F (payload p))
  have hNoEarly (m : ℕ) (hm : m ∈ D) : m ∉ Set.Iio (N p) := by
    intro hlt
    change m < N p at hlt
    have heC : m ∈ F (cap p) ↔ m ∈ F (cap q) := by
      have h : m ∈ restrictSet (Finset.range (N p)) (F (cap p)) ↔
          m ∈ restrictSet (Finset.range (N p)) (F (cap q)) := by rw [hCap]
      simpa only [mem_restrictSet,Finset.mem_range,hlt,true_and] using h
    have heP : m ∈ F (payload p) ↔ m ∈ F (payload q) := by
      have h : m ∈ restrictSet (Finset.range (N p)) (F (payload p)) ↔
          m ∈ restrictSet (Finset.range (N p)) (F (payload q)) := by rw [hPayload]
      simpa only [mem_restrictSet,Finset.mem_range,hlt,true_and] using h
    have hm' : m ∈ xorSet (F (cap p) ∩ F (payload q)) (F (cap q) ∩ F (payload p)) := hm
    simp only [xorSet,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff] at hm'
    tauto
  have hD : D ⊆ (E p \ Set.Iio (N p)) ∪ (E q \ Set.Iio (N q)) := by
    intro m hm
    have hEp : m ∈ E p ∪ E q :=
      crossing_xor_subset_r12 (F (cap p)) (F (cap q)) (F (payload p)) (F (payload q)) (F U) hm
    have hlt := hNoEarly m hm
    rcases hEp with hp | hq
    · exact Or.inl ⟨hp,hlt⟩
    · exact Or.inr ⟨hq,by simpa only [← hNpq] using hlt⟩
  have hSmall := euPrefixSmall_downward g (ε + ε) hD (euPrefixSmall_union g (hN p) (hN q))
  exact (hCross p q hne).2 hSmall

end

end JSP000933
