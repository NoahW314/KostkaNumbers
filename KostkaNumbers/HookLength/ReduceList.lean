import Mathlib
import KostkaNumbers.Util.MinMaxEl

def ltCount (i : ℕ) (L : List ℕ) : ℕ := List.countP (fun j ↦ j ∈ L) (List.range i)

def reduceList (L : List ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (L.length) ↦ ltCount (L.get i) L)

def unreduceList (a : ℕ) (L : List ℕ) : List ℕ := [a] ++ List.ofFn (fun i ↦
  if L[i] < a then L[i] else L[i] + 1)



-- ltCount Lemmas

lemma ltCount_zero (L : List ℕ) : ltCount 0 L = 0 := by simp [ltCount]

lemma ltCount_le (i : ℕ) (L : List ℕ) : ltCount i L ≤ i := by
  unfold ltCount
  have hi : i = (List.range i).length := by symm; exact List.length_range
  nth_rw 2 [hi]
  exact List.countP_le_length

lemma ltCount_full {i : ℕ} {L : List ℕ} (h : ↑L = Multiset.range L.length) (hi : i ≤ L.length) :
    ltCount i L = i := by
  unfold ltCount
  have hl : i = (List.range i).length := by symm; exact List.length_range
  nth_rw 2 [hl]
  rw [List.countP_eq_length]
  simp only [List.mem_range, decide_eq_true_eq]
  intro j hj
  suffices j ∈ Multiset.ofList L by exact this
  rw [h, Multiset.mem_range]
  omega

lemma ltCount_tail {i : ℕ} {L : List ℕ} (hL : L ≠ []) (h : i ≤ L.head hL) :
    ltCount i L.tail = ltCount i L := by
  refine List.countP_congr ?_
  simp only [List.mem_range, decide_eq_true_eq]
  nth_rw 2 [← List.cons_head_tail hL]
  intro j hj
  rw [List.mem_cons]
  have hjh : j ≠ L.head hL := by omega
  simp [hjh]

lemma List.Nodup.head_notMem_tail {α : Type*} [BEq α] [LawfulBEq α] {L : List α}
    (hL : L ≠ []) (h : L.Nodup) : L.head hL ∉ L.tail := by
  by_contra!
  have hch : List.count (L.head hL) L ≥ 2 := by
    nth_rw 2 [← List.cons_head_tail hL]
    rw [List.count_cons]
    simp [this]
  rw [List.nodup_iff_count] at h
  specialize h (L.head hL)
  omega

lemma ltCount_cons (i a : ℕ) (L : List ℕ) (ha : a ∉ L) : ltCount i (a :: L) =
    ltCount i L + if a < i then 1 else 0 := by
  unfold ltCount
  by_cases hai : a < i
  · have hli : Multiset.range i = a ::ₘ (Multiset.range i).erase a := by
      rw [Multiset.cons_erase]
      rw [Multiset.mem_range]
      exact hai
    rw [← Multiset.coe_countP, ← Multiset.coe_countP, Multiset.coe_range i,
      hli, Multiset.countP_cons, Multiset.countP_cons]
    have hasd : Multiset.countP (Membership.mem (a :: L))  ((Multiset.range i).erase a) =
        Multiset.countP (Membership.mem L) ((Multiset.range i).erase a) := by
      refine Multiset.countP_congr (by rfl) ?_
      intro x hx
      simp only [List.mem_cons, eq_iff_iff, or_iff_right_iff_imp]
      intro hxa
      subst hxa
      have hx' : x ∉ (Multiset.range i).erase x := Multiset.Nodup.notMem_erase
        (Multiset.nodup_range i)
      contradiction
    rw [hasd]
    simp [ha, hai]
  · simp only [List.mem_cons, Bool.decide_or, hai, ↓reduceIte, add_zero]
    refine List.countP_congr ?_
    intro x
    simp only [List.mem_range, Bool.or_eq_true, decide_eq_true_eq, or_iff_right_iff_imp]
    intro hxi hxa
    omega

lemma ltCount_coe (i : ℕ) (L L' : List ℕ) (h : Multiset.ofList L = Multiset.ofList L') :
    ltCount i L = ltCount i L' := by
  unfold ltCount
  refine List.countP_congr ?_
  simp [← Multiset.mem_coe, h]

lemma ltCount_erase (i a : ℕ) (L : List ℕ) (ha : a ∈ L) (h : L.Nodup) :
    ltCount i (L.erase a) = ltCount i L - if a < i then 1 else 0 := by
  rw [ltCount_coe i L (a :: (L.erase a)), ltCount_cons]
  · simp only [add_tsub_cancel_right]
  · exact List.Nodup.not_mem_erase h
  · rw [← Multiset.cons_coe, ← Multiset.coe_erase, Multiset.cons_erase ha]


lemma ltCount_tail' {i : ℕ} {L : List ℕ} (hL : L ≠ []) (hn : L.Nodup) (h : i > L.head hL) :
    ltCount i L.tail + 1 = ltCount i L := by
  nth_rw 2 [← List.cons_head_tail hL]
  rw [ltCount_cons _ _ _ <| List.Nodup.head_notMem_tail hL hn]
  simp [h]

lemma ltCount_add_one (i : ℕ) (L : List ℕ) (h : i ∈ L) :
    ltCount (i + 1) L = ltCount i L + 1 := by
  unfold ltCount
  rw [List.range_succ, List.countP_append]
  simp [h]

lemma ltCount_mono {i j : ℕ} (L : List ℕ) (h : i ≤ j) : ltCount i L ≤ ltCount j L := by
  refine List.Sublist.countP_le ?_
  exact List.range_sublist.mpr h

lemma ltCount_min_eq_zero {L : List ℕ} (hL : Multiset.ofList L ≠ 0) :
    ltCount (min_el L hL) L = 0 := by
  simp only [ltCount, List.countP_eq_zero, List.mem_range, decide_eq_true_eq]
  intro a
  contrapose!
  exact min_el_le' hL

lemma ltCount_max_eq_length {L : List ℕ} (hL : Multiset.ofList L ≠ 0) (h : L.Nodup) :
    ltCount ((max_el L hL) + 1) L = L.length := by
  unfold ltCount
  rw [← Finset.sum_filter_count_eq_countP, ← List.toFinset_card_of_nodup h]
  simp only [List.count_range, Finset.sum_boole, Nat.cast_id]
  symm
  congr
  ext x
  constructor; swap
  · simp only [Finset.mem_filter, List.mem_toFinset, List.mem_range, and_imp]
    exact fun a a _ ↦ a
  · intro hx
    simp only [List.mem_toFinset] at hx
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_range, hx, and_true, and_self]
    have hjx := le_max_el' hL hx
    omega

lemma ltCount_le_length (i : ℕ) (L : List ℕ) (h : L.Nodup) : ltCount i L ≤ L.length := by
  by_cases hL : Multiset.ofList L = 0
  · rw [Multiset.coe_eq_zero] at hL
    simp [hL, ltCount]

  let j := (max_el (↑L) hL) + 1
  have hj := ltCount_max_eq_length hL h
  rw [← hj]
  by_cases hi : i ≤ j
  · exact ltCount_mono L hi
  · refine le_of_eq ?_
    unfold ltCount
    push_neg at hi
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hi
    rw [hk, Nat.add_assoc, List.range_add]
    simp only [j, List.countP_append, List.countP_map, Nat.add_eq_left, List.countP_eq_zero,
      List.mem_range, Function.comp_apply, decide_eq_true_eq]
    intro a _
    by_contra!
    apply le_max_el' hL at this
    omega

lemma ltCount_eq_length (i : ℕ) (L : List ℕ) (hL : Multiset.ofList L ≠ 0) (h : L.Nodup) :
    ltCount i L = L.length ↔ i > max_el L hL := by
  constructor
  · contrapose!
    intro hi
    refine ne_of_lt ?_
    unfold ltCount
    rw [← Finset.sum_filter_count_eq_countP, ← List.toFinset_card_of_nodup h]
    simp only [List.count_range, Finset.sum_boole, Nat.cast_id]
    refine Finset.card_lt_card ?_
    refine Finset.ssubset_iff_subset_ne.mpr ?_
    constructor
    · intro x
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_range, and_imp]
      exact fun _ a _ ↦ a
    · rw [← Finset.symmDiff_nonempty]
      use (max_el L hL)
      rw [Finset.mem_symmDiff]
      right
      simp only [List.mem_toFinset, Finset.mem_filter, List.mem_range, not_and, not_lt, hi,
        implies_true, and_true]
      exact max_el_mem hL
  · intro hi
    refine le_antisymm (ltCount_le_length i L h) ?_
    rw [← ltCount_max_eq_length hL h]
    exact ltCount_mono L hi

lemma ltCount_tail_lt {i : ℕ} {L : List ℕ} (hL : L ≠ []) (h : ↑L = Multiset.range L.length)
    (hc : ltCount i L.tail < L.head hL) (hi : i < L.length) :
    ltCount i L.tail = i := by
  induction i with
  | zero => simp [ltCount]
  | succ i ih =>
    have hc : ltCount i L.tail < L.head hL :=
      lt_of_le_of_lt (ltCount_mono L.tail (Nat.le_add_right i 1)) hc
    specialize ih hc (by omega)
    rw [ltCount_tail hL, ltCount_full h (by omega)]
    omega

lemma ltCount_tail_gt {i : ℕ} {L : List ℕ} (hL : L ≠ []) (h : ↑L = Multiset.range L.length)
    (hc : ltCount i L.tail > L.head hL) (hi : i < L.length) :
    ltCount i L.tail + 1 = i := by
  rw [ltCount_tail' hL, ltCount_full h (by omega)]
  · rw [← Multiset.coe_nodup, h]
    exact Multiset.nodup_range _
  · refine lt_of_lt_of_le hc ?_
    exact ltCount_le _ _

lemma le_ltCount_add_one {i : ℕ} {L : List ℕ} (hL : L ≠ []) (h : ↑L = Multiset.range L.length)
    (hi : i ≤ L.length) : i ≤ ltCount i L.tail + 1 := by
  nth_rw 1 [← ltCount_full h hi]
  conv => lhs; rhs; rw [← List.cons_head_tail hL]
  rw [ltCount_cons, add_le_add_iff_left]
  · split_ifs
    all_goals simp
  · refine List.Nodup.head_notMem_tail hL ?_
    rw [← Multiset.coe_nodup, h]
    exact Multiset.nodup_range _

-- reduceList and unreduceList lemmas

lemma reduceList_length (L : List ℕ) : (reduceList L).length = L.length := by simp [reduceList]

lemma unreduceList_length {a : ℕ} {L : List ℕ} : (unreduceList a L).length = L.length + 1 := by
  simp [unreduceList]

lemma reduceList_multiset (L : List ℕ) (h : L.Nodup) : Multiset.ofList (reduceList L) =
    Multiset.range L.length := by
  by_cases hL : Multiset.ofList L = 0
  · rw [Multiset.coe_eq_zero] at hL
    simp [hL, reduceList]

  ext x
  rw [Multiset.coe_count, Multiset.count_eq_of_nodup (Multiset.nodup_range _)]
  split_ifs with hx
  · refine List.count_eq_one_of_mem ?_ ?_
    · unfold reduceList
      rw [List.nodup_ofFn]
      intro i j hij
      simp only [List.get_eq_getElem, ltCount] at hij
      suffices L[i.1] = L[j.1] by
        rw [List.Nodup.getElem_inj_iff h] at this
        exact Fin.eq_of_val_eq this
      contrapose! hij
      wlog hl : L[i.1] < L[j.1] generalizing i j
      · symm
        symm at hij
        have hl : L[i.1] > L[j.1] := by omega
        exact this hij hl
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hl
        rw [hk, Nat.add_assoc, List.range_add]
        simp
        use 0
        simp
    · unfold reduceList
      simp only [List.get_eq_getElem, List.mem_ofFn]
      by_cases h0 : x = 0
      · let k := min_el L hL
        have hkL := min_el_mem hL
        obtain ⟨i, ⟨hi, him⟩⟩ := List.getElem_of_mem hkL
        use ⟨i, hi⟩
        simp [him, h0, ltCount_min_eq_zero]

      let k := sSup {k : ℕ | ltCount k L < x}
      have hbd : BddAbove {k : ℕ | ltCount k L < x} := by
        use ((max_el L hL) + 1)
        simp [upperBounds]
        intro j hj
        contrapose! hj
        have hj : j > max_el L hL := by omega
        apply (ltCount_eq_length _ _ hL h).mpr at hj
        rw [Multiset.mem_range] at hx
        omega
      have hk : ltCount k L < x := by
        suffices k ∈ {k : ℕ | ltCount k L < x} by rw [Set.mem_setOf] at this; exact this
        refine Nat.sSup_mem ?_ hbd
        use 0
        rw [Set.mem_setOf_eq, ltCount_zero]
        omega
      have hk' : ltCount (k + 1) L ≥ x := by
        suffices k + 1 ∉ {k : ℕ | ltCount k L < x} by
          rw [Set.mem_setOf] at this; push_neg at this; exact this
        exact notMem_of_csSup_lt (by omega) hbd
      have hkL : k ∈ L := by
        have : ltCount k L < ltCount (k + 1) L := by omega
        unfold ltCount at this
        rw [List.range_add] at this
        simp only [List.range_one, List.map_cons, add_zero, List.map_nil, List.countP_append,
          List.countP_singleton, decide_eq_true_eq, lt_add_iff_pos_right] at this
        split at this
        next h1 => exact h1
        next _ => contradiction
      have hk'' : ltCount (k + 1) L = ltCount k L + 1 := ltCount_add_one _ _ hkL
      have hkx : ltCount k L = x - 1 := by omega
      obtain ⟨i, ⟨hi, hik⟩⟩ := List.getElem_of_mem hkL
      suffices ∃ j : Fin (L.length), L[j.1] > L[i] ∧ ∀ y ∈ L, ¬(L[i] < y ∧ y < L[j.1]) by
        obtain ⟨j, ⟨hij, hj⟩⟩ := this
        use j
        simp only [not_and, not_lt] at hj
        obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt hij
        unfold ltCount
        rw [hl, Nat.add_assoc, List.range_add, List.countP_append, List.countP_map,
          ← ltCount, hik, hkx]
        suffices List.countP ((fun j ↦ decide (j ∈ L)) ∘ (fun x ↦ k + x)) (List.range (l + 1))
          = 1 by omega
        suffices List.countP ((fun j ↦ decide (j ∈ L)) ∘ (fun x ↦ k + x)) (List.range 1) = 1 by
          rw [Nat.add_comm, List.range_add, List.countP_append]
          simp only [List.range_one, Function.comp_apply, add_zero, hkL, decide_true,
            List.countP_cons_of_pos, List.countP_nil, zero_add, List.countP_map, Nat.add_eq_left,
            List.countP_eq_zero, List.mem_range, decide_eq_true_eq]
          intro a ha
          contrapose! hj
          use (k + (1 + a))
          simp only [hj, hik, lt_add_iff_pos_right, add_pos_iff, zero_lt_one, true_or, hl, true_and]
          omega
        simp [hkL]
      let y := sInf {y ∈ L | L[i] < y}
      have hy : y ∈ {y ∈ L | L[i] < y} := by
        refine csInf_mem ?_
        use (max_el L hL)
        rw [Set.mem_setOf]
        constructor
        · exact max_el_mem hL
        · refine lt_of_le_of_ne (le_max_el' hL (by simp)) ?_
          contrapose! hx
          rw [Multiset.mem_range, ← ltCount_max_eq_length hL h, ← hx, hik, hk'', hkx]
          omega
      rw [Set.mem_setOf] at hy
      obtain ⟨hyL, hyi⟩ := hy
      obtain ⟨j, ⟨hj, hyj⟩⟩ := List.getElem_of_mem hyL
      use ⟨j, hj⟩
      simp only [hyj, gt_iff_lt, hyi, not_and, not_lt, true_and]
      intro z hzL hzi
      refine Nat.sInf_le ?_
      simp [hzL, hzi]
  · rw [List.count_eq_zero]
    rw [Multiset.mem_range] at hx
    simp [reduceList]
    intro i
    have hiL := ltCount_le_length L[i.1] L h
    by_cases hlx : ltCount L[i.1] L < x
    · exact ne_of_lt hlx
    have hix : ltCount L[i.1] L = L.length := by omega
    rw [ltCount_eq_length _ _ hL h] at hix
    have hli : L[i.1] ∈ L := by simp
    have := le_max_el' hL hli
    omega

-- proof of the inverse relationships

lemma unreduce_reduce (L : List ℕ) (hL : L ≠ []) (h : ↑L = Multiset.range L.length) :
    unreduceList (L.head hL) (reduceList L.tail) = L := by
  unfold unreduceList
  conv => rhs; rw [← List.cons_head_tail hL]
  simp only [Fin.getElem_fin, List.cons_append, List.nil_append]
  rw [List.cons_inj_right]
  refine List.ext_getElem ?_ ?_
  · rw [List.length_ofFn, reduceList_length]
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_tail]
    split_ifs with hh
    · simp_all only [reduceList, List.length_tail, List.get_eq_getElem, Fin.coe_cast,
        List.getElem_tail, List.getElem_ofFn]
      refine ltCount_tail_lt hL h hh ?_
      rw [← Multiset.mem_range, ← h, Multiset.mem_coe]
      simp
    · simp_all only [reduceList, List.length_tail, List.get_eq_getElem, Fin.coe_cast,
        List.getElem_tail, List.getElem_ofFn]
      push_neg at hh
      rw [List.length_tail] at h₂
      by_cases hh2 : L.head hL < ltCount L[i + 1] L.tail
      · refine ltCount_tail_gt hL h hh2 ?_
        rw [← Multiset.mem_range, ← h, Multiset.mem_coe]
        simp
      · apply eq_of_le_of_not_lt at hh
        specialize hh hh2
        clear hh2
        suffices L[i + 1] ≤ ltCount L[i + 1] L.tail + 1 by
          have hLh := ltCount_le L[i + 1] L.tail
          by_cases hLh2 : ltCount L[i + 1] L.tail + 1 = L[i + 1]
          · exact hLh2
          · have hlh : L.head hL = L[i + 1] := by omega
            rw [List.head_eq_getElem hL, List.Nodup.getElem_inj_iff] at hlh
            · apply Nat.zero_ne_add_one i at hlh
              contradiction
            · rw [← Multiset.coe_nodup, h]
              exact Multiset.nodup_range L.length
        refine le_ltCount_add_one hL h <| le_of_lt ?_
        rw [← Multiset.mem_range, ← h, Multiset.mem_coe]
        simp

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 2000000 in
lemma reduce_unreduce (a : ℕ) (L : List ℕ) (h : ↑L = Multiset.range L.length) :
    reduceList (unreduceList a L).tail = L := by
  refine List.ext_getElem ?_ ?_
  · simp [reduceList_length, unreduceList_length]
  · intro i h₁ h₂

    unfold reduceList unreduceList
    simp only [Fin.getElem_fin, List.cons_append, List.nil_append, List.tail_cons, List.length_ofFn,
      List.get_eq_getElem, Fin.coe_cast, List.getElem_ofFn]
    have hLL : L[i] < L.length := by
      rw [← Multiset.mem_range, ← h]
      simp
    split_ifs with hLa
    · have hltc : ltCount L[i] (List.ofFn fun i ↦ if L[i.1] < a then L[i.1] else L[i.1] + 1) =
          ltCount L[i] (List.ofFn fun i ↦ L[i.1]) := by
        refine List.countP_congr ?_
        intro x
        simp only [List.mem_range, List.mem_ofFn, decide_eq_true_eq, List.ofFn_getElem]
        intro hx
        constructor
        · intro ⟨j, hj⟩
          suffices L[j.1] < a by
            simp only [this, ↓reduceIte] at hj
            rw [← hj]
            exact List.getElem_mem j.2
          by_contra hja
          simp only [hja, ↓reduceIte] at hj
          omega
        · intro hxL
          apply List.getElem_of_mem at hxL
          obtain ⟨j, ⟨hj, hjx⟩⟩ := hxL
          use ⟨j, hj⟩
          simp [show x < a by omega, hjx]
      rw [hltc, List.ofFn_getElem]
      exact ltCount_full h <| le_of_lt hLL
    · have hltc : ltCount (L[i] + 1) (List.ofFn fun i ↦ if L[i.1] < a then L[i.1] else L[i.1] + 1) =
          ltCount (L[i] + 1) ((L.length :: L).erase a) := by
        refine List.countP_congr ?_
        simp only [List.mem_range, List.mem_ofFn, decide_eq_true_eq]
        intro x hx
        constructor
        · intro ⟨j, hj⟩
          rw [← Multiset.mem_coe, ← Multiset.coe_erase, ← Multiset.cons_coe, h,
            ← Multiset.range_succ, Multiset.mem_erase_of_ne, Multiset.mem_range]
          · omega
          · contrapose! hj
            subst hj
            split_ifs with hj
            all_goals omega
        · intro hxL
          by_cases hxa : x < a
          · suffices x ∈ L by
              obtain ⟨j, ⟨hj, hjx⟩⟩ := List.getElem_of_mem this
              use ⟨j, hj⟩
              simp [hxa, hjx]
            rw [← Multiset.mem_coe, h, Multiset.mem_range]
            omega
          · have hxan : x ≠ a := by
              contrapose! hxL
              rw [hxL, List.Nodup.mem_erase_iff]
              · simp
              · rw [← Multiset.coe_nodup, ← Multiset.cons_coe, h, ← Multiset.range_succ]
                exact Multiset.nodup_range _
            suffices x - 1 ∈ L by
              obtain ⟨j, ⟨hj, hjx⟩⟩ := List.getElem_of_mem this
              use ⟨j, hj⟩
              simp only [hjx, show ¬x - 1 < a by omega, ↓reduceIte]
              omega
            apply List.mem_of_mem_erase at hxL
            rw [← Multiset.mem_coe, ← Multiset.cons_coe, h, ← Multiset.range_succ,
              Multiset.mem_range] at hxL
            rw [← Multiset.mem_coe, h, Multiset.mem_range]
            omega
      rw [hltc, ltCount_erase, ltCount_cons, ltCount_full h]
      · simp only [show a < L[i] + 1 by omega, ↓reduceIte, Nat.succ_add_sub_one, Nat.add_eq_left,
          ite_eq_right_iff, one_ne_zero, imp_false, not_lt, ge_iff_le]
        omega
      · omega
      · rw [← Multiset.mem_coe, h, Multiset.mem_range]
        omega
      · rw [List.mem_cons]
        right
        rw [← Multiset.mem_coe, h, Multiset.mem_range]
        omega
      · rw [← Multiset.coe_nodup, ← Multiset.cons_coe, h]
        simp only [Multiset.nodup_cons, Multiset.mem_range, lt_self_iff_false, not_false_eq_true,
          true_and]
        exact Multiset.nodup_range _
