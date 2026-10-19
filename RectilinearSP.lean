import Mathlib

set_option maxHeartbeats 400000

namespace KeyLemma

def alphaPairs : Finset (ℤ × ℤ) :=
  {(1, 0), (0, 1), (1, 1)}

def R (A B : Finset ℤ) : Finset ℤ :=
  (A ×ˢ B).biUnion fun ab =>
    ((alphaPairs ×ˢ alphaPairs).filter
      (fun uv =>
        ab.1 - uv.1.1 - uv.2.1 =
        ab.2 + uv.1.2 + uv.2.2)).image
      (fun uv =>
        ab.1 - uv.1.1 - uv.2.1)

def sigmaP (A B : Finset ℤ) : Finset ℤ :=
  let S := R A B ∪ R B A
  S ∪ S.image (fun x => -x)

def pieces (S : Finset ℤ) : ℕ :=
  (S.filter (fun x => x - 1 ∉ S)).card

def symInterval (c : ℕ) : Finset ℤ :=
  Finset.Icc (-(c : ℤ)) (c : ℤ)

def negSet (S : Finset ℤ) : Finset ℤ :=
  S.image (fun x => -x)

def IntConvex (S : Finset ℤ) : Prop :=
  ∀ x y z : ℤ,
    x ∈ S → y ∈ S →
    x ≤ z → z ≤ y → z ∈ S

private theorem mem_negSet (S : Finset ℤ) (x : ℤ) :
    x ∈ negSet S ↔ -x ∈ S := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
    have h : y = -x := by omega
    simpa [h] using hy
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨-x, hx, by omega⟩

private theorem negSet_invol (S : Finset ℤ) :
    negSet (negSet S) = S := by
  classical
  ext x
  simp only [mem_negSet, neg_neg]

private theorem negSet_union (S T : Finset ℤ) :
    negSet (S ∪ T) = negSet S ∪ negSet T := by
  classical
  simp only [negSet, Finset.image_union]

private theorem pieces_empty :
    pieces (∅ : Finset ℤ) = 0 := by
  simp [pieces]

private theorem pieces_union_le (S T : Finset ℤ) :
    pieces (S ∪ T) ≤ pieces S + pieces T := by
  classical
  have hsub :
      ((S ∪ T).filter
        (fun x => x - 1 ∉ S ∪ T)) ⊆
      (S.filter (fun x => x - 1 ∉ S)) ∪
      (T.filter (fun x => x - 1 ∉ T)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_union] at hx ⊢
    obtain ⟨hx, hp⟩ := hx
    rcases hx with hs | ht
    · left
      refine ⟨hs, ?_⟩
      intro hprev
      apply hp
      exact Or.inl hprev
    · right
      refine ⟨ht, ?_⟩
      intro hprev
      apply hp
      exact Or.inr hprev
  unfold pieces
  exact
    (Finset.card_le_card hsub).trans
      (Finset.card_union_le _ _)

private theorem pieces_convex_le_one
    (S : Finset ℤ) (hS : IntConvex S) :
    pieces S ≤ 1 := by
  classical
  unfold pieces
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxS, hxprev⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyS, hyprev⟩ := Finset.mem_filter.mp hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have h : y - 1 ∈ S :=
      hS x y (y - 1) hxS hyS (by omega) (by omega)
    exact hyprev h
  · have h : x - 1 ∈ S :=
      hS y x (x - 1) hyS hxS (by omega) (by omega)
    exact hxprev h

private theorem convex_neg
    (S : Finset ℤ) (hS : IntConvex S) :
    IntConvex (negSet S) := by
  intro x y z hx hy hxz hzy
  rw [mem_negSet] at hx hy ⊢
  exact hS (-y) (-x) (-z) hy hx (by omega) (by omega)

private theorem convex_union_common
    (S T : Finset ℤ)
    (hS : IntConvex S)
    (hT : IntConvex T)
    (hcommon : ∃ p, p ∈ S ∧ p ∈ T) :
    IntConvex (S ∪ T) := by
  obtain ⟨p, hpS, hpT⟩ := hcommon
  intro x y z hx hy hxz hzy
  simp only [Finset.mem_union] at hx hy ⊢
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hS x y z hx hy hxz hzy)
  · by_cases hzp : z ≤ p
    · exact Or.inl (hS x p z hx hpS hxz hzp)
    · exact Or.inr (hT p y z hpT hy (by omega) hzy)
  · by_cases hzp : z ≤ p
    · exact Or.inr (hT x p z hx hpT hxz hzp)
    · exact Or.inl (hS p y z hpS hy (by omega) hzy)
  · exact Or.inr (hT x y z hx hy hxz hzy)

private theorem R_union
    (A₁ A₂ B : Finset ℤ) :
    R (A₁ ∪ A₂) B = R A₁ B ∪ R A₂ B := by
  classical
  ext s
  simp only [R, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_product, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, uv, huv, hs⟩
    rcases ha with ha | ha
    · exact Or.inl
        ⟨(a, b), ⟨ha, hb⟩, uv, huv, hs⟩
    · exact Or.inr
        ⟨(a, b), ⟨ha, hb⟩, uv, huv, hs⟩
  · rintro (⟨⟨a, b⟩, ⟨ha, hb⟩, uv, huv, hs⟩ |
             ⟨⟨a, b⟩, ⟨ha, hb⟩, uv, huv, hs⟩)
    · exact ⟨(a, b), ⟨Or.inl ha, hb⟩, uv, huv, hs⟩
    · exact ⟨(a, b), ⟨Or.inr ha, hb⟩, uv, huv, hs⟩

private theorem R_empty_left (B : Finset ℤ) :
    R ∅ B = ∅ := by
  simp [R]

private theorem symInterval_symm (c : ℕ) (x : ℤ) :
    x ∈ symInterval c ↔ -x ∈ symInterval c := by
  simp only [symInterval, Finset.mem_Icc]
  constructor <;> intro h <;> omega

private theorem R_swap_neg
    (A B : Finset ℤ)
    (hA : ∀ x, x ∈ A ↔ -x ∈ A)
    (hB : ∀ x, x ∈ B ↔ -x ∈ B) :
    R B A = negSet (R A B) := by
  classical
  have aux :
      ∀ (U V : Finset ℤ),
        (∀ x, x ∈ U ↔ -x ∈ U) →
        (∀ x, x ∈ V ↔ -x ∈ V) →
        ∀ t, t ∈ R U V → -t ∈ R V U := by
    intro U V hU hV t ht
    simp only [R, Finset.mem_biUnion, Finset.mem_product,
      Finset.mem_image, Finset.mem_filter] at ht ⊢
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, ⟨p, q⟩,
      ⟨⟨hp, hq⟩, heq⟩, hval⟩ := ht
    rcases p with ⟨pl, pr⟩
    rcases q with ⟨ql, qr⟩

    change a - pl - ql = b + pr + qr at heq
    change a - pl - ql = t at hval

    have hps : (pr, pl) ∈ alphaPairs := by
      simp only [alphaPairs, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq] at hp ⊢
      omega

    have hqs : (qr, ql) ∈ alphaPairs := by
      simp only [alphaPairs, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq] at hq ⊢
      omega

    refine ⟨(-b, -a), ?_, ((pr, pl), (qr, ql)), ?_, ?_⟩
    · exact ⟨(hV b).mp hb, (hU a).mp ha⟩
    · refine ⟨⟨hps, hqs⟩, ?_⟩
      change -b - pr - qr = -a + pl + ql
      omega
    · change -b - pr - qr = -t
      omega

  ext s
  constructor
  · intro hs
    apply (mem_negSet (R A B) s).mpr
    exact aux B A hB hA s hs
  · intro hs
    have ht := (mem_negSet (R A B) s).mp hs
    have hu := aux A B hA hB (-s) ht
    simpa only [neg_neg] using hu

private theorem sigma_eq_R
    (A B : Finset ℤ)
    (hA : ∀ x, x ∈ A ↔ -x ∈ A)
    (hB : ∀ x, x ∈ B ↔ -x ∈ B) :
    sigmaP A B = R A B ∪ negSet (R A B) := by
  classical
  simp only [sigmaP, R_swap_neg A B hA hB]
  rw [Finset.image_union]
  change
    (R A B ∪ negSet (R A B)) ∪
      (negSet (R A B) ∪ negSet (negSet (R A B))) =
    R A B ∪ negSet (R A B)
  rw [negSet_invol]
  ext x
  simp only [Finset.mem_union, mem_negSet, neg_neg]
  by_cases h₁ : x ∈ R A B <;>
    by_cases h₂ : -x ∈ R A B <;>
      simp_all

private theorem mem_R_interval
    (A : Finset ℤ) (c : ℕ) (s : ℤ) :
    s ∈ R A (symInterval c) ↔
      ∃ a ∈ A,
        2 - (c : ℤ) ≤ a ∧
        a - 2 ≤ s ∧
        s ≤ a ∧
        s ≤ 2 + (c : ℤ) := by
  classical
  constructor
  · intro hs
    simp only [R, Finset.mem_biUnion, Finset.mem_product,
      Finset.mem_image, Finset.mem_filter] at hs
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩,
      ⟨p, q⟩, ⟨⟨hp, hq⟩, heq⟩, hval⟩ := hs
    rcases p with ⟨pl, pr⟩
    rcases q with ⟨ql, qr⟩

    change a - pl - ql = b + pr + qr at heq
    change a - pl - ql = s at hval

    have hb' := Finset.mem_Icc.mp hb

    simp only [alphaPairs, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq] at hp hq

    rcases hp with ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ <;>
      rcases hq with ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ <;>
      refine ⟨a, ha, ?_, ?_, ?_, ?_⟩ <;>
      omega

  · rintro ⟨a, ha, had, has, hsa, hsc⟩

    have build
        (b : ℤ) (p q : ℤ × ℤ)
        (hb : b ∈ symInterval c)
        (hp : p ∈ alphaPairs)
        (hq : q ∈ alphaPairs)
        (heq :
          a - p.1 - q.1 = b + p.2 + q.2)
        (hval : a - p.1 - q.1 = s) :
        s ∈ R A (symInterval c) := by
      unfold R
      apply Finset.mem_biUnion.mpr
      refine ⟨(a, b), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨ha, hb⟩
      · apply Finset.mem_image.mpr
        refine ⟨(p, q), ?_, hval⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hp, hq⟩, heq⟩

    by_cases h0 : a = s
    · apply build (s - 2) (0, 1) (0, 1)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        (by decide) (by decide) (by omega) (by omega)

    by_cases h1 : a = s + 1
    · by_cases hc : 2 - (c : ℤ) ≤ s
      · apply build (s - 2) (1, 1) (0, 1)
          (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          (by decide) (by decide) (by omega) (by omega)
      · apply build (s - 1) (1, 0) (0, 1)
          (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          (by decide) (by decide) (by omega) (by omega)

    have h2 : a = s + 2 := by omega

    by_cases hc0 : s ≤ (c : ℤ)
    · apply build s (1, 0) (1, 0)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        (by decide) (by decide) (by omega) (by omega)

    by_cases hc1 : s ≤ (c : ℤ) + 1
    · apply build (s - 1) (1, 1) (1, 0)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        (by decide) (by decide) (by omega) (by omega)
    · apply build (s - 2) (1, 1) (1, 1)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        (by decide) (by decide) (by omega) (by omega)

private theorem T_convex
    (l u : ℤ) (c : ℕ) :
    IntConvex (R (Finset.Icc l u) (symInterval c)) := by
  intro x y z hx hy hxz hzy

  obtain ⟨a, ha, had, hax, hxa, hxe⟩ :=
    (mem_R_interval (Finset.Icc l u) c x).mp hx

  obtain ⟨b, hb, hbd, hby, hyb, hye⟩ :=
    (mem_R_interval (Finset.Icc l u) c y).mp hy

  have hal := (Finset.mem_Icc.mp ha).1
  have hau := (Finset.mem_Icc.mp ha).2
  have hbl := (Finset.mem_Icc.mp hb).1
  have hbu := (Finset.mem_Icc.mp hb).2

  let w : ℤ := max l (max (2 - (c : ℤ)) z)

  have hwl : l ≤ w := by
    dsimp [w]
    exact le_max_left _ _

  have hwd : 2 - (c : ℤ) ≤ w := by
    dsimp [w]
    exact (le_max_left _ _).trans (le_max_right _ _)

  have hwz : z ≤ w := by
    dsimp [w]
    exact (le_max_right _ _).trans (le_max_right _ _)

  have hwu : w ≤ u := by
    dsimp [w]
    apply max_le
    · omega
    · apply max_le <;> omega

  have hwz2 : w ≤ z + 2 := by
    dsimp [w]
    apply max_le
    · omega
    · apply max_le <;> omega

  apply (mem_R_interval (Finset.Icc l u) c z).mpr
  refine ⟨w, Finset.mem_Icc.mpr ⟨hwl, hwu⟩,
    hwd, ?_, hwz, ?_⟩
  · omega
  · omega

private theorem T_central_zero
    (d : ℤ) (c : ℕ)
    (hd : 0 ≤ d)
    (hne :
      R (Finset.Icc (-d) d) (symInterval c) ≠ ∅) :
    0 ∈ R (Finset.Icc (-d) d) (symInterval c) := by

  have hnon :
      (R (Finset.Icc (-d) d) (symInterval c)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne

  obtain ⟨s, hs⟩ := hnon

  obtain ⟨a, ha, had, has, hsa, hsc⟩ :=
    (mem_R_interval (Finset.Icc (-d) d) c s).mp hs

  have hau := (Finset.mem_Icc.mp ha).2
  have hcd : 2 - (c : ℤ) ≤ d := by omega

  apply (mem_R_interval (Finset.Icc (-d) d) c 0).mpr
  refine ⟨min d 2, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  · omega
  · omega
  · omega
  · omega

private theorem T_pair_convex
    (l u : ℤ) (c : ℕ)
    (hl : 1 ≤ l) (hlu : l ≤ u) :
    IntConvex
      (R (Finset.Icc l u) (symInterval c) ∪
       negSet
         (R (Finset.Icc (-u) (-l)) (symInterval c))) := by

  let P := R (Finset.Icc l u) (symInterval c)
  let N := R (Finset.Icc (-u) (-l)) (symInterval c)

  have hP : IntConvex P := T_convex l u c
  have hN : IntConvex N := T_convex (-u) (-l) c

  have hNegN : IntConvex (negSet N) :=
    convex_neg N hN

  by_cases hempty : N = ∅
  · simpa [N, hempty, negSet] using hP

  · have hn : N.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty

    obtain ⟨s, hs⟩ := hn

    obtain ⟨a, ha, had, has, hsa, hsc⟩ :=
      (mem_R_interval (Finset.Icc (-u) (-l)) c s).mp hs

    have hau := (Finset.mem_Icc.mp ha).2
    have hc : l + 2 ≤ (c : ℤ) := by omega

    have hp : l ∈ P := by
      apply (mem_R_interval (Finset.Icc l u) c l).mpr
      refine ⟨l, Finset.mem_Icc.mpr ⟨by omega, hlu⟩,
        ?_, ?_, ?_, ?_⟩
      all_goals omega

    have hn' : -l ∈ N := by
      apply (mem_R_interval
        (Finset.Icc (-u) (-l)) c (-l)).mpr
      refine ⟨-l, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        ?_, ?_, ?_, ?_⟩
      all_goals omega

    have hcommon : l ∈ negSet N :=
      (mem_negSet N l).mpr hn'

    exact convex_union_common P (negSet N)
      hP hNegN ⟨l, hp, hcommon⟩

private theorem union_rearrange (P Q N : Finset ℤ) :
    (P ∪ Q ∪ N) ∪ negSet (P ∪ Q ∪ N) =
      ((P ∪ negSet P) ∪ (Q ∪ negSet N)) ∪
        negSet (Q ∪ negSet N) := by
  ext x
  simp only [Finset.mem_union, mem_negSet,
    negSet_union, neg_neg]
  by_cases h1 : x ∈ P <;>
    by_cases h2 : -x ∈ P <;>
      by_cases h3 : x ∈ Q <;>
        by_cases h4 : -x ∈ Q <;>
          by_cases h5 : x ∈ N <;>
            by_cases h6 : -x ∈ N <;>
              simp [h1, h2, h3, h4, h5, h6]

theorem key_lemma
    (A : Finset ℤ) (c : ℕ)
    (hA : ∀ x, x ∈ A ↔ -x ∈ A) :
    pieces (sigmaP A (symInterval c)) ≤ pieces A := by
  classical

  suffices H :
      ∀ n : ℕ,
        ∀ S : Finset ℤ,
          S.card = n →
          (∀ x, x ∈ S ↔ -x ∈ S) →
          pieces (sigmaP S (symInterval c)) ≤ pieces S
    from H _ A rfl hA

  intro n

  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hcard hS

    let B := symInterval c

    have hB : ∀ x, x ∈ B ↔ -x ∈ B :=
      symInterval_symm c

    by_cases hEmpty : S = ∅
    · subst S
      simp [sigmaP, R, pieces]

    have hNonempty : S.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hEmpty

    let m : ℤ := S.max' hNonempty

    have hm : m ∈ S :=
      Finset.max'_mem S hNonempty

    have hMax : ∀ x ∈ S, x ≤ m := by
      intro x hx
      exact Finset.le_max' S x hx

    have hMin : ∀ x ∈ S, -m ≤ x := by
      intro x hx
      have hnx : -x ∈ S := (hS x).mp hx
      have h := hMax (-x) hnx
      omega

    have hmNonneg : 0 ≤ m := by
      have hnm : -m ∈ S := (hS m).mp hm
      have h := hMax (-m) hnm
      omega

    let E : Finset ℤ :=
      S.filter (fun a =>
        ∀ x : ℤ, a ≤ x → x ≤ m → x ∈ S)

    have hENonempty : E.Nonempty := by
      refine ⟨m, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
      intro x hx hxm
      have heq : x = m := by omega
      simpa [heq] using hm

    let l : ℤ := E.min' hENonempty

    have hlE : l ∈ E :=
      Finset.min'_mem E hENonempty

    have hlS : l ∈ S :=
      (Finset.mem_filter.mp hlE).1

    have hRun :
        ∀ x : ℤ, l ≤ x → x ≤ m → x ∈ S :=
      (Finset.mem_filter.mp hlE).2

    have hlm : l ≤ m :=
      hMax l hlS

    have hGap : l - 1 ∉ S := by
      intro hprev
      have hprevE : l - 1 ∈ E := by
        apply Finset.mem_filter.mpr
        refine ⟨hprev, ?_⟩
        intro x hx hxm
        by_cases heq : x = l - 1
        · simpa [heq] using hprev
        · exact hRun x (by omega) hxm
      have hle := Finset.min'_le E (l - 1) hprevE
      omega

    have hLeftmost : -m - 1 ∉ S := by
      intro hx
      have hmx : m + 1 ∈ S := by
        have h := (hS (-m - 1)).mp hx
        convert h using 1 <;> omega
      have hbound := hMax (m + 1) hmx
      omega

    by_cases hCentral : l ≤ 0

    · have hFull : S = Finset.Icc (-m) m := by
        ext x
        simp only [Finset.mem_Icc]
        constructor
        · intro hx
          exact ⟨hMin x hx, hMax x hx⟩
        · intro hx
          by_cases hxl : l ≤ x
          · exact hRun x hxl hx.2
          · have hnx : -x ∈ S :=
              hRun (-x) (by omega) (by omega)
            have h := (hS (-x)).mp hnx
            simpa only [neg_neg] using h

      have hConvT : IntConvex (R S B) := by
        rw [hFull]
        exact T_convex (-m) m c

      have hSigma :
          sigmaP S B = R S B ∪ negSet (R S B) :=
        sigma_eq_R S B hS hB

      have hPiecesPos : 1 ≤ pieces S := by
        unfold pieces
        apply Finset.one_le_card.mpr
        refine ⟨-m, Finset.mem_filter.mpr ⟨?_, hLeftmost⟩⟩
        exact (hS m).mp hm

      by_cases hTEmpty : R S B = ∅
      · rw [hSigma, hTEmpty]
        simp [negSet, pieces]

      have hZero : (0 : ℤ) ∈ R S B := by
        rw [hFull]
        apply T_central_zero m c hmNonneg
        simpa only [hFull] using hTEmpty

      have hZeroNeg : (0 : ℤ) ∈ negSet (R S B) :=
        (mem_negSet (R S B) 0).mpr
          (by simpa using hZero)

      have hConvSigma :
          IntConvex (R S B ∪ negSet (R S B)) :=
        convex_union_common
          (R S B) (negSet (R S B))
          hConvT (convex_neg (R S B) hConvT)
          ⟨0, hZero, hZeroNeg⟩

      have hBound :
          pieces (sigmaP S B) ≤ 1 := by
        rw [hSigma]
        exact pieces_convex_le_one _ hConvSigma

      change pieces (sigmaP S B) ≤ pieces S
      omega

    · have hlPositive : 1 ≤ l := by omega

      let Sprime : Finset ℤ :=
        S.filter (fun x => -l < x ∧ x < l)

      have hPrimeSub : Sprime ⊆ S := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1

      have hPrimeSym :
          ∀ x, x ∈ Sprime ↔ -x ∈ Sprime := by
        intro x
        dsimp [Sprime]
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx, ⟨hlo, hhi⟩⟩
          exact ⟨(hS x).mp hx, ⟨by omega, by omega⟩⟩
        · rintro ⟨hx, ⟨hlo, hhi⟩⟩
          refine ⟨?_, ⟨by omega, by omega⟩⟩
          have h := (hS (-x)).mp hx
          simpa only [neg_neg] using h

      have hmNotPrime : m ∉ Sprime := by
        intro hx
        have hbounds := (Finset.mem_filter.mp hx).2
        omega

      have hStrict : Sprime ⊂ S := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hPrimeSub, ?_⟩
        intro heq
        apply hmNotPrime
        rw [heq]
        exact hm

      have hCardStrict : Sprime.card < n := by
        have hlt : Sprime.card < S.card :=
          Finset.card_lt_card hStrict
        omega

      have hIH :
          pieces (sigmaP Sprime B) ≤ pieces Sprime :=
        ih Sprime.card hCardStrict Sprime rfl hPrimeSym

      have hGapNeg : -l + 1 ∉ S := by
        intro hx
        have ht : l - 1 ∈ S := by
          have h := (hS (-l + 1)).mp hx
          convert h using 1 <;> omega
        exact hGap ht

      let Pos : Finset ℤ := Finset.Icc l m
      let Neg : Finset ℤ := Finset.Icc (-m) (-l)

      have hDecomp :
          S = (Sprime ∪ Pos) ∪ Neg := by
        ext x
        simp only [Finset.mem_union]
        constructor
        · intro hx
          by_cases hxl : x < l
          · by_cases hxn : -l < x
            · exact Or.inl (Or.inl
                (Finset.mem_filter.mpr
                  ⟨hx, ⟨hxn, hxl⟩⟩))
            · exact Or.inr
                (Finset.mem_Icc.mpr
                  ⟨hMin x hx, by omega⟩)
          · exact Or.inl (Or.inr
              (Finset.mem_Icc.mpr
                ⟨by omega, hMax x hx⟩))
        · rintro ((hx | hx) | hx)
          · exact hPrimeSub hx
          · exact hRun x
              (Finset.mem_Icc.mp hx).1
              (Finset.mem_Icc.mp hx).2
          · have hnx : -x ∈ S :=
              hRun (-x)
                (by have := (Finset.mem_Icc.mp hx).2; omega)
                (by have := (Finset.mem_Icc.mp hx).1; omega)
            have h := (hS (-x)).mp hnx
            simpa only [neg_neg] using h

      have hStarts :
          (S.filter (fun x => x - 1 ∉ S)) =
          (Sprime.filter (fun x => x - 1 ∉ Sprime)) ∪
            ({l, -m} : Finset ℤ) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_filter,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hprev⟩
          by_cases hxl : x < l
          · by_cases hxn : -l < x
            · left
              refine ⟨Finset.mem_filter.mpr
                ⟨hx, ⟨hxn, hxl⟩⟩, ?_⟩
              intro hp
              exact hprev (hPrimeSub hp)
            · right
              right
              have hlow := hMin x hx
              by_contra hneq
              have hgt : -m < x := by omega
              have hmirror : 1 - x ∈ S :=
                hRun (1 - x) (by omega) (by omega)
              have hpr : x - 1 ∈ S := by
                have h := (hS (1 - x)).mp hmirror
                convert h using 1 <;> omega
              exact hprev hpr
          · right
            left
            by_contra hneq
            have hgt : l < x := by omega
            have hpr : x - 1 ∈ S :=
              hRun (x - 1) (by omega)
                (by have := hMax x hx; omega)
            exact hprev hpr

        · rintro (⟨hxPrime, hpPrime⟩ | (heq | heq))
          · have hx := (Finset.mem_filter.mp hxPrime).1
            have hbounds := (Finset.mem_filter.mp hxPrime).2
            refine ⟨hx, ?_⟩
            intro hp
            have hneq : x ≠ -l + 1 := by
              intro heq
              apply hGapNeg
              simpa [heq] using hx
            have hlow : -l < x - 1 := by omega
            have hup : x - 1 < l := by omega
            have hp' : x - 1 ∈ Sprime :=
              Finset.mem_filter.mpr
                ⟨hp, ⟨hlow, hup⟩⟩
            exact hpPrime hp'
          · subst x
            exact ⟨hlS, hGap⟩
          · subst x
            exact ⟨(hS m).mp hm, hLeftmost⟩

      have hStartsDisjoint :
          Disjoint
            (Sprime.filter (fun x => x - 1 ∉ Sprime))
            ({l, -m} : Finset ℤ) := by
        apply Finset.disjoint_left.mpr
        intro x hx htwo
        have hxPrime := (Finset.mem_filter.mp hx).1
        have hbounds := (Finset.mem_filter.mp hxPrime).2
        simp only [Finset.mem_insert,
          Finset.mem_singleton] at htwo
        rcases htwo with heq | heq <;> omega

      have hTwo :
          ({l, -m} : Finset ℤ).card = 2 := by
        have hne : l ≠ -m := by omega
        simp [hne]

      have hPiecesDecomp :
          pieces S = pieces Sprime + 2 := by
        unfold pieces
        rw [hStarts]
        rw [Finset.card_union_of_disjoint hStartsDisjoint]
        rw [hTwo]

      have hRDecomp :
          R S B =
            (R Sprime B ∪ R Pos B) ∪ R Neg B := by
        rw [hDecomp]
        rw [R_union]
        rw [R_union]

      let H : Finset ℤ :=
        R Pos B ∪ negSet (R Neg B)

      have hHConvex : IntConvex H := by
        dsimp [H, Pos, Neg]
        exact T_pair_convex l m c hlPositive hlm

      have hHNegConvex : IntConvex (negSet H) :=
        convex_neg H hHConvex

      have hHBound : pieces H ≤ 1 :=
        pieces_convex_le_one H hHConvex

      have hHNegBound : pieces (negSet H) ≤ 1 :=
        pieces_convex_le_one (negSet H) hHNegConvex

      have hSigmaDecomp :
          sigmaP S B =
            (sigmaP Sprime B ∪ H) ∪ negSet H := by
        rw [sigma_eq_R S B hS hB,
            sigma_eq_R Sprime B hPrimeSym hB,
            hRDecomp]
        exact union_rearrange _ _ _

      rw [hSigmaDecomp]
      calc
        pieces ((sigmaP Sprime B ∪ H) ∪ negSet H)
            ≤ pieces (sigmaP Sprime B ∪ H) +
                pieces (negSet H) :=
              pieces_union_le _ _
        _ ≤ (pieces (sigmaP Sprime B) + pieces H) +
                pieces (negSet H) := by
              have h := pieces_union_le (sigmaP Sprime B) H
              omega
        _ ≤ pieces Sprime + 2 := by omega
        _ = pieces S := hPiecesDecomp.symm

#print axioms key_lemma

end KeyLemma

/-!
# RectilinearSP — Tappe 1 e 2

Semantica combinatoria delle regole di
Didimo–Kaufmann–Liotta–Ortali, arXiv:2208.12558.

Lean v4.35.0 + Mathlib.

Le spiralità del modello SPQ* sono raddoppiate.

Si utilizza Set ℤ per la semantica ricorsiva.
La finitezza viene provata in T2_0.

Correzione geometrica:
se almeno un coefficiente raddoppiato di un polo
è uguale a 1, entrambe le variabili angolari
di quel polo devono essere uguali a 1.
-/

namespace RectilinearSP

/-! ## 1. Alberi -/

inductive SPTree where
  | Q (len : ℕ)
  | S (children : List SPTree)
  | P2 (kl_u kl_v kr_u kr_v : ℤ)
       (l r : SPTree)
  | P3 (l c r : SPTree)

/-! ## 2. Intervalli -/

def Band (n : ℕ) : Set ℤ :=
  {z | ∃ s : ℤ,
    -(n : ℤ) ≤ s ∧
    s ≤ (n : ℤ) ∧
    z = 2 * s}

/-! ## 3. Somma di Minkowski -/

def Mink (A B : Set ℤ) : Set ℤ :=
  {z | ∃ a : ℤ, a ∈ A ∧
       ∃ b : ℤ, b ∈ B ∧
       z = a + b}

/-! ## 4. Variabili angolari -/

def Alpha (lu ru lv rv : ℤ) : Prop :=
  (lu = 0 ∨ lu = 1) ∧
  (ru = 0 ∨ ru = 1) ∧
  (lv = 0 ∨ lv = 1) ∧
  (rv = 0 ∨ rv = 1) ∧
  1 ≤ lu + ru ∧
  lu + ru ≤ 2 ∧
  1 ≤ lv + rv ∧
  lv + rv ≤ 2

private theorem alpha_swap
    {lu ru lv rv : ℤ}
    (h : Alpha lu ru lv rv) :
    Alpha ru lu rv lv := by
  rcases h with
    ⟨hlu, hru, hlv, hrv, hu1, hu2, hv1, hv2⟩
  exact ⟨
    hru, hlu, hrv, hlv,
    by omega,
    by omega,
    by omega,
    by omega
  ⟩

/-! ## 5. Correzione geometrica dei poli di grado 4 -/

def Degree4Angles
    (kl_u kl_v kr_u kr_v : ℤ)
    (lu ru lv rv : ℤ) : Prop :=
  ((kl_u = 1 ∨ kr_u = 1) → lu = 1 ∧ ru = 1) ∧
  ((kl_v = 1 ∨ kr_v = 1) → lv = 1 ∧ rv = 1)

private theorem degree4_swap
    {kl_u kl_v kr_u kr_v lu ru lv rv : ℤ}
    (h :
      Degree4Angles kl_u kl_v kr_u kr_v
        lu ru lv rv) :
    Degree4Angles kr_u kr_v kl_u kl_v
      ru lu rv lv := by
  rcases h with ⟨hu, hv⟩
  constructor
  · intro h
    have hh : kl_u = 1 ∨ kr_u = 1 := by
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases hu hh with ⟨hl, hr⟩
    exact ⟨hr, hl⟩
  · intro h
    have hh : kl_v = 1 ∨ kr_v = 1 := by
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases hv hh with ⟨hl, hr⟩
    exact ⟨hr, hl⟩

/-! ## 6. Relazione P2 corretta -/

def P2Rel
    (kl_u kl_v kr_u kr_v : ℤ)
    (A B : Set ℤ)
    (z : ℤ) : Prop :=
  ∃ a : ℤ, a ∈ A ∧
  ∃ b : ℤ, b ∈ B ∧
  ∃ lu ru lv rv : ℤ,
    Alpha lu ru lv rv ∧
    Degree4Angles kl_u kl_v kr_u kr_v
      lu ru lv rv ∧
    z = a - kl_u * lu - kl_v * lv ∧
    z = b + kr_u * ru + kr_v * rv

def P2Set
    (kl_u kl_v kr_u kr_v : ℤ)
    (A B : Set ℤ) : Set ℤ :=
  {z |
    P2Rel kl_u kl_v kr_u kr_v A B z ∨
    P2Rel kr_u kr_v kl_u kl_v B A z}

/-! ## 7. Relazione P3 -/

def P3Rel
    (A B C : Set ℤ)
    (z : ℤ) : Prop :=
  ∃ a : ℤ, a ∈ A ∧
  ∃ b : ℤ, b ∈ B ∧
  ∃ d : ℤ, d ∈ C ∧
    z = a - 4 ∧
    z = b ∧
    z = d + 4

def P3Set
    (A B C : Set ℤ) : Set ℤ :=
  {z |
    P3Rel A B C z ∨
    P3Rel A C B z ∨
    P3Rel B A C z ∨
    P3Rel B C A z ∨
    P3Rel C A B z ∨
    P3Rel C B A z}

/-! ## 8. Semantica Sigma -/

mutual

def Sigma : SPTree → Set ℤ
  | .Q len =>
      Band (len - 1)
  | .S children =>
      SigmaList children
  | .P2 kl_u kl_v kr_u kr_v l r =>
      P2Set kl_u kl_v kr_u kr_v
        (Sigma l) (Sigma r)
  | .P3 l c r =>
      P3Set (Sigma l) (Sigma c) (Sigma r)

def SigmaList : List SPTree → Set ℤ
  | [] =>
      {0}
  | t :: ts =>
      Mink (Sigma t) (SigmaList ts)

end

/-! ## 9. Alberi leggeri -/

mutual

def Light : SPTree → Prop
  | .Q _ =>
      True
  | .S children =>
      LightList children
  | .P2 kl_u kl_v kr_u kr_v l r =>
      kl_u = 2 ∧
      kl_v = 2 ∧
      kr_u = 2 ∧
      kr_v = 2 ∧
      Light l ∧
      Light r
  | .P3 _ _ _ =>
      False

def LightList : List SPTree → Prop
  | [] =>
      True
  | t :: ts =>
      Light t ∧ LightList ts

end

/-! ## 10. Simmetria -/

private theorem band_neg
    {n : ℕ} {z : ℤ}
    (h : z ∈ Band n) :
    -z ∈ Band n := by
  rcases h with ⟨s, hlo, hhi, hz⟩
  refine ⟨-s, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

private theorem p2_swap
    {A B : Set ℤ}
    {kl_u kl_v kr_u kr_v z : ℤ}
    (hA : ∀ x, x ∈ A → -x ∈ A)
    (hB : ∀ x, x ∈ B → -x ∈ B)
    (h : P2Rel kl_u kl_v kr_u kr_v A B z) :
    P2Rel kr_u kr_v kl_u kl_v B A (-z) := by
  rcases h with
    ⟨a, ha, b, hb, lu, ru, lv, rv,
      halpha, hdegree, hleft, hright⟩

  refine ⟨
    -b, hB b hb,
    -a, hA a ha,
    ru, lu, rv, lv,
    alpha_swap halpha,
    degree4_swap hdegree,
    ?_, ?_
  ⟩

  · linear_combination -hright
  · linear_combination -hleft

private theorem p3_reverse
    {A B C : Set ℤ}
    {z : ℤ}
    (hA : ∀ x, x ∈ A → -x ∈ A)
    (hB : ∀ x, x ∈ B → -x ∈ B)
    (hC : ∀ x, x ∈ C → -x ∈ C)
    (h : P3Rel A B C z) :
    P3Rel C B A (-z) := by

  rcases h with
    ⟨a, ha, b, hb, d, hd, h1, h2, h3⟩

  refine ⟨
    -d, hC d hd,
    -b, hB b hb,
    -a, hA a ha,
    ?_, ?_, ?_
  ⟩

  · omega
  · omega
  · omega

mutual

private theorem sigma_neg
    (t : SPTree)
    (z : ℤ) :
    z ∈ Sigma t → -z ∈ Sigma t := by

  cases t with

  | Q len =>
      exact band_neg

  | S children =>
      exact sigmaList_neg children z

  | P2 kl_u kl_v kr_u kr_v l r =>
      intro hz

      change
        P2Rel kl_u kl_v kr_u kr_v
          (Sigma l) (Sigma r) z ∨
        P2Rel kr_u kr_v kl_u kl_v
          (Sigma r) (Sigma l) z
        at hz

      change
        P2Rel kl_u kl_v kr_u kr_v
          (Sigma l) (Sigma r) (-z) ∨
        P2Rel kr_u kr_v kl_u kl_v
          (Sigma r) (Sigma l) (-z)

      rcases hz with h | h

      · right
        exact p2_swap
          (fun x hx => sigma_neg l x hx)
          (fun x hx => sigma_neg r x hx)
          h

      · left
        exact p2_swap
          (fun x hx => sigma_neg r x hx)
          (fun x hx => sigma_neg l x hx)
          h

  | P3 l c r =>
      intro hz

      change
        P3Rel (Sigma l) (Sigma c) (Sigma r) z ∨
        P3Rel (Sigma l) (Sigma r) (Sigma c) z ∨
        P3Rel (Sigma c) (Sigma l) (Sigma r) z ∨
        P3Rel (Sigma c) (Sigma r) (Sigma l) z ∨
        P3Rel (Sigma r) (Sigma l) (Sigma c) z ∨
        P3Rel (Sigma r) (Sigma c) (Sigma l) z
        at hz

      change
        P3Rel (Sigma l) (Sigma c) (Sigma r) (-z) ∨
        P3Rel (Sigma l) (Sigma r) (Sigma c) (-z) ∨
        P3Rel (Sigma c) (Sigma l) (Sigma r) (-z) ∨
        P3Rel (Sigma c) (Sigma r) (Sigma l) (-z) ∨
        P3Rel (Sigma r) (Sigma l) (Sigma c) (-z) ∨
        P3Rel (Sigma r) (Sigma c) (Sigma l) (-z)

      have hL :
          ∀ x, x ∈ Sigma l → -x ∈ Sigma l :=
        sigma_neg l

      have hC :
          ∀ x, x ∈ Sigma c → -x ∈ Sigma c :=
        sigma_neg c

      have hR :
          ∀ x, x ∈ Sigma r → -x ∈ Sigma r :=
        sigma_neg r

      rcases hz with h | h | h | h | h | h

      · exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (p3_reverse hL hC hR h)))))

      · exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inl
                (p3_reverse hL hR hC h))))

      · exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inl
                  (p3_reverse hC hL hR h)))))

      · exact Or.inr
          (Or.inl
            (p3_reverse hC hR hL h))

      · exact Or.inr
          (Or.inr
            (Or.inl
              (p3_reverse hR hL hC h)))

      · exact Or.inl
          (p3_reverse hR hC hL h)

private theorem sigmaList_neg
    (ts : List SPTree)
    (z : ℤ) :
    z ∈ SigmaList ts → -z ∈ SigmaList ts := by

  cases ts with

  | nil =>
      intro hz
      simp only [SigmaList, Set.mem_singleton_iff] at hz ⊢
      omega

  | cons t ts =>
      intro hz

      change
        z ∈ Mink (Sigma t) (SigmaList ts)
        at hz

      rcases hz with ⟨a, ha, b, hb, heq⟩

      change
        -z ∈ Mink (Sigma t) (SigmaList ts)

      refine ⟨
        -a, sigma_neg t a ha,
        -b, sigmaList_neg ts b hb,
        ?_
      ⟩

      omega

end

/-- T1.1: simmetria per ogni albero. -/
theorem T1_1
    (t : SPTree)
    (z : ℤ) :
    z ∈ Sigma t ↔ -z ∈ Sigma t := by
  constructor
  · exact sigma_neg t z
  · intro hz
    have h := sigma_neg t (-z) hz
    simpa only [neg_neg] using h

/-! ## 11. Intervalli Band -/

private theorem band_zero :
    Band 0 = ({0} : Set ℤ) := by

  ext z
  constructor

  · intro hz
    rcases hz with ⟨s, hlo, hhi, heq⟩
    have hs : s = 0 := by omega
    subst s
    simp at heq
    exact heq

  · intro hz
    have hzero : z = 0 := by
      simpa using hz
    subst z
    exact ⟨0, by omega, by omega, by norm_num⟩

private theorem mink_band
    (m n : ℕ) :
    Mink (Band m) (Band n) = Band (m + n) := by

  ext z
  constructor

  · intro hz

    rcases hz with ⟨a, ha, b, hb, heq⟩
    rcases ha with ⟨s, hslo, hshi, haeq⟩
    rcases hb with ⟨t, htlo, hthi, hbeq⟩

    refine ⟨s + t, ?_, ?_, ?_⟩

    · omega
    · omega
    · omega

  · intro hz

    rcases hz with ⟨s, hslo, hshi, heq⟩

    let a : ℤ :=
      max (-(m : ℤ)) (s - (n : ℤ))

    have ha1 : -(m : ℤ) ≤ a := by
      dsimp [a]
      exact le_max_left _ _

    have ha2 : a ≤ (m : ℤ) := by
      dsimp [a]
      apply max_le
      · omega
      · omega

    have ha3 : s - (n : ℤ) ≤ a := by
      dsimp [a]
      exact le_max_right _ _

    have ha4 : a ≤ s + (n : ℤ) := by
      dsimp [a]
      apply max_le
      · omega
      · omega

    refine ⟨
      2 * a,
      ⟨a, ha1, ha2, rfl⟩,
      2 * (s - a),
      ⟨s - a, ?_, ?_, rfl⟩,
      ?_
    ⟩

    · omega
    · omega
    · omega

/-! ## 12. P2 leggeri -/

private def cap (m n : ℕ) : ℕ :=
  min (max m n) (min (m + 2) (n + 2))

private theorem cap_le_max (m n : ℕ) :
    cap m n ≤ max m n := by
  unfold cap
  exact min_le_left _ _

private theorem cap_le_left (m n : ℕ) :
    cap m n ≤ m + 2 := by
  unfold cap
  exact le_trans (min_le_right _ _) (min_le_left _ _)

private theorem cap_le_right (m n : ℕ) :
    cap m n ≤ n + 2 := by
  unfold cap
  exact le_trans (min_le_right _ _) (min_le_right _ _)

private theorem cap_spec
    (m n : ℕ)
    (s : ℤ) :
    (-(cap m n : ℤ) ≤ s ∧ s ≤ (cap m n : ℤ)) ↔
    (-(max m n : ℤ) ≤ s ∧
     s ≤ (max m n : ℤ) ∧
     -(m : ℤ) - 2 ≤ s ∧
     s ≤ (m : ℤ) + 2 ∧
     -(n : ℤ) - 2 ≤ s ∧
     s ≤ (n : ℤ) + 2) := by

  rcases le_total m n with hmn | hnm

  · dsimp [cap]

    rw [
      max_eq_right hmn,
      min_eq_left (show m + 2 ≤ n + 2 by omega)
    ]

    rcases le_total n (m + 2) with h | h

    · rw [min_eq_left h]
      constructor <;> intro hs <;> omega

    · rw [min_eq_right h]
      constructor <;> intro hs <;> omega

  · dsimp [cap]

    rw [
      max_eq_left hnm,
      min_eq_right (show n + 2 ≤ m + 2 by omega)
    ]

    rcases le_total m (n + 2) with h | h

    · rw [min_eq_left h]
      constructor <;> intro hs <;> omega

    · rw [min_eq_right h]
      constructor <;> intro hs <;> omega

private theorem p2rel_bounds
    {m n : ℕ}
    {z : ℤ}
    (h : P2Rel 2 2 2 2 (Band m) (Band n) z) :
    ∃ s : ℤ,
      z = 2 * s ∧
      (2 : ℤ) ≤ (m : ℤ) + (n : ℤ) ∧
      -(m : ℤ) - 2 ≤ s ∧
      s ≤ (m : ℤ) ∧
      -(n : ℤ) ≤ s ∧
      s ≤ (n : ℤ) + 2 := by

  rcases h with
    ⟨a, ha, b, hb, lu, ru, lv, rv,
      halpha, hdegree, hleft, hright⟩

  rcases ha with ⟨x, hxlo, hxhi, hxa⟩
  rcases hb with ⟨y, hylo, hyhi, hyb⟩

  rcases halpha with
    ⟨hlu, hru, hlv, hrv, hu1, hu2, hv1, hv2⟩

  have hlu0 : 0 ≤ lu ∧ lu ≤ 1 := by
    rcases hlu with h | h <;> omega

  have hru0 : 0 ≤ ru ∧ ru ≤ 1 := by
    rcases hru with h | h <;> omega

  have hlv0 : 0 ≤ lv ∧ lv ≤ 1 := by
    rcases hlv with h | h <;> omega

  have hrv0 : 0 ≤ rv ∧ rv ≤ 1 := by
    rcases hrv with h | h <;> omega

  refine ⟨x - lu - lv, ?_, ?_, ?_, ?_, ?_, ?_⟩

  all_goals omega

private theorem p2set_bounds
    {m n : ℕ}
    {z : ℤ}
    (h : z ∈ P2Set 2 2 2 2 (Band m) (Band n)) :
    ∃ s : ℤ,
      z = 2 * s ∧
      (2 : ℤ) ≤ (m : ℤ) + (n : ℤ) ∧
      -(cap m n : ℤ) ≤ s ∧
      s ≤ (cap m n : ℤ) := by

  change
    P2Rel 2 2 2 2 (Band m) (Band n) z ∨
    P2Rel 2 2 2 2 (Band n) (Band m) z
    at h

  have hmmax :
      (m : ℤ) ≤ (max m n : ℤ) := by
    exact_mod_cast le_max_left m n

  have hnmax :
      (n : ℤ) ≤ (max m n : ℤ) := by
    exact_mod_cast le_max_right m n

  rcases h with h | h

  · rcases p2rel_bounds h with
      ⟨s, hz, hsum, hml, hmu, hnl, hnu⟩

    have hcap :
        -(cap m n : ℤ) ≤ s ∧
        s ≤ (cap m n : ℤ) :=
      (cap_spec m n s).mpr
        ⟨
          by omega,
          by omega,
          by omega,
          by omega,
          by omega,
          by omega
        ⟩

    exact ⟨s, hz, hsum, hcap.1, hcap.2⟩

  · rcases p2rel_bounds h with
      ⟨s, hz, hsum, hnl, hnu, hml, hmu⟩

    have hcap :
        -(cap m n : ℤ) ≤ s ∧
        s ≤ (cap m n : ℤ) :=
      (cap_spec m n s).mpr
        ⟨
          by omega,
          by omega,
          by omega,
          by omega,
          by omega,
          by omega
        ⟩

    refine ⟨s, hz, ?_, hcap.1, hcap.2⟩
    omega

private theorem p2_build
    (m n : ℕ)
    (s lu ru lv rv : ℤ)
    (halpha : Alpha lu ru lv rv)
    (ha1 : -(m : ℤ) ≤ s + lu + lv)
    (ha2 : s + lu + lv ≤ (m : ℤ))
    (hb1 : -(n : ℤ) ≤ s - ru - rv)
    (hb2 : s - ru - rv ≤ (n : ℤ)) :
    P2Rel 2 2 2 2 (Band m) (Band n) (2 * s) := by

  refine ⟨
    2 * (s + lu + lv),
    ⟨s + lu + lv, ha1, ha2, rfl⟩,
    2 * (s - ru - rv),
    ⟨s - ru - rv, hb1, hb2, rfl⟩,
    lu, ru, lv, rv,
    halpha,
    ?_, ?_, ?_
  ⟩

  · constructor <;> intro h <;> omega
  · ring
  · ring

private theorem p2_order_nonneg
    (m n : ℕ)
    (s : ℤ)
    (hmn : n ≤ m)
    (hs : 0 ≤ s)
    (hm : s ≤ (m : ℤ))
    (hn : s ≤ (n : ℤ) + 2)
    (hsum : (2 : ℤ) ≤ (m : ℤ) + (n : ℤ)) :
    P2Rel 2 2 2 2 (Band m) (Band n) (2 * s) := by

  by_cases h2 : 2 ≤ s + (n : ℤ)

  · exact p2_build m n s 0 1 0 1
      (by norm_num [Alpha])
      (by omega)
      (by omega)
      (by omega)
      (by omega)

  · by_cases h1 : 1 ≤ s + (n : ℤ)

    · exact p2_build m n s 1 0 0 1
        (by norm_num [Alpha])
        (by omega)
        (by omega)
        (by omega)
        (by omega)

    · exact p2_build m n s 1 0 1 0
        (by norm_num [Alpha])
        (by omega)
        (by omega)
        (by omega)
        (by omega)

private theorem p2set_nonneg
    (m n : ℕ)
    (s : ℤ)
    (hsum : (2 : ℤ) ≤ (m : ℤ) + (n : ℤ))
    (hs : 0 ≤ s)
    (hcap : s ≤ (cap m n : ℤ)) :
    (2 * s) ∈ P2Set 2 2 2 2 (Band m) (Band n) := by

  have hmax := cap_le_max m n
  have hleft := cap_le_left m n
  have hright := cap_le_right m n

  change
    P2Rel 2 2 2 2 (Band m) (Band n) (2 * s) ∨
    P2Rel 2 2 2 2 (Band n) (Band m) (2 * s)

  rcases le_total n m with hnm | hmn

  · left

    have hmaxeq : max m n = m :=
      max_eq_left hnm

    apply p2_order_nonneg m n s hnm hs

    · omega
    · omega
    · exact hsum

  · right

    have hmaxeq : max m n = n :=
      max_eq_right hmn

    apply p2_order_nonneg n m s hmn hs

    · omega
    · omega
    · omega

private theorem p2set_neg
    {m n : ℕ}
    {z : ℤ}
    (h : z ∈ P2Set 2 2 2 2 (Band m) (Band n)) :
    -z ∈ P2Set 2 2 2 2 (Band m) (Band n) := by

  change
    P2Rel 2 2 2 2 (Band m) (Band n) z ∨
    P2Rel 2 2 2 2 (Band n) (Band m) z
    at h

  change
    P2Rel 2 2 2 2 (Band m) (Band n) (-z) ∨
    P2Rel 2 2 2 2 (Band n) (Band m) (-z)

  rcases h with h | h

  · right
    exact p2_swap
      (fun x hx => band_neg hx)
      (fun x hx => band_neg hx)
      h

  · left
    exact p2_swap
      (fun x hx => band_neg hx)
      (fun x hx => band_neg hx)
      h

private theorem p2_band_shape
    (m n : ℕ) :
    P2Set 2 2 2 2 (Band m) (Band n) = ∅ ∨
    ∃ c : ℕ,
      P2Set 2 2 2 2 (Band m) (Band n) = Band c := by

  by_cases hsum :
      (2 : ℤ) ≤ (m : ℤ) + (n : ℤ)

  · right

    refine ⟨cap m n, ?_⟩

    ext z
    constructor

    · intro hz

      rcases p2set_bounds hz with
        ⟨s, heq, _, hlo, hhi⟩

      exact ⟨s, hlo, hhi, heq⟩

    · intro hz

      rcases hz with ⟨s, hlo, hhi, heq⟩

      subst z

      by_cases hs : 0 ≤ s

      · exact p2set_nonneg m n s hsum hs hhi

      · have hsneg : 0 ≤ -s := by
          omega

        have hnegcap : -s ≤ (cap m n : ℤ) := by
          omega

        have hpos :=
          p2set_nonneg m n (-s)
            hsum hsneg hnegcap

        have hneg := p2set_neg hpos

        convert hneg using 1 <;> ring

  · left

    ext z
    constructor

    · intro hz

      rcases p2set_bounds hz with
        ⟨s, heq, hnecessary, hlo, hhi⟩

      omega

    · intro hz
      simp at hz

/-! ## 13. T1.3 — Forma degli insiemi leggeri -/

mutual

theorem T1_3
    (t : SPTree)
    (hlight : Light t) :
    Sigma t = ∅ ∨
    ∃ c : ℕ, Sigma t = Band c := by

  cases t with

  | Q len =>
      right
      exact ⟨len - 1, rfl⟩

  | S children =>
      exact sigmaList_shape children hlight

  | P3 l c r =>
      exact False.elim hlight

  | P2 kl_u kl_v kr_u kr_v l r =>

      rcases hlight with
        ⟨hku, hkv, hru, hrv, hl, hr⟩

      rcases T1_3 l hl with
        hemptyL | ⟨m, hbandL⟩

      · left
        ext z
        simp [Sigma, P2Set, P2Rel, hemptyL]

      · rcases T1_3 r hr with
          hemptyR | ⟨n, hbandR⟩

        · left
          ext z
          simp [Sigma, P2Set, P2Rel, hemptyR]

        · simpa [
            Sigma,
            hku, hkv, hru, hrv,
            hbandL, hbandR
          ] using p2_band_shape m n

theorem sigmaList_shape
    (ts : List SPTree)
    (hlight : LightList ts) :
    SigmaList ts = ∅ ∨
    ∃ c : ℕ, SigmaList ts = Band c := by

  cases ts with

  | nil =>
      right
      refine ⟨0, ?_⟩
      simp [SigmaList, band_zero]

  | cons t ts =>

      rcases hlight with ⟨ht, hts⟩

      rcases T1_3 t ht with
        hemptyT | ⟨m, hbandT⟩

      · left
        ext z
        simp [SigmaList, Mink, hemptyT]

      · rcases sigmaList_shape ts hts with
          hemptyTs | ⟨n, hbandTs⟩

        · left
          ext z
          simp [SigmaList, Mink, hemptyTs]

        · right
          refine ⟨m + n, ?_⟩

          simpa [
            SigmaList,
            hbandT,
            hbandTs
          ] using mink_band m n

end

/-! ## 14. T1.2 — Parità -/

theorem T1_2
    (t : SPTree)
    (hlight : Light t)
    (z : ℤ)
    (hz : z ∈ Sigma t) :
    Even z := by

  rcases T1_3 t hlight with
    hempty | ⟨c, hband⟩

  · rw [hempty] at hz
    simp at hz

  · rw [hband] at hz

    rcases hz with ⟨s, hlo, hhi, heq⟩

    refine ⟨s, ?_⟩
    omega

/-! ## 15. T2.0 — Finitezza -/

private theorem finite_Band (n : ℕ) :
    (Band n).Finite := by
  apply
    (Set.finite_Icc
      (-(2 * (n : ℤ)))
      (2 * (n : ℤ))).subset
  intro z hz
  rcases hz with ⟨s, hlo, hhi, heq⟩
  change
    -(2 * (n : ℤ)) ≤ z ∧
    z ≤ 2 * (n : ℤ)
  omega

private theorem finite_Mink
    {A B : Set ℤ}
    (hA : A.Finite)
    (hB : B.Finite) :
    (Mink A B).Finite := by

  have hprod : (A ×ˢ B).Finite :=
    hA.prod hB

  have himage :
      ((fun p : ℤ × ℤ => p.1 + p.2) '' (A ×ˢ B)).Finite :=
    hprod.image _

  apply himage.subset

  intro z hz

  rcases hz with ⟨a, ha, b, hb, heq⟩

  exact ⟨(a, b), ⟨ha, hb⟩, heq.symm⟩

private theorem finite_P2Rel
    {A B : Set ℤ}
    (kl_u kl_v kr_u kr_v : ℤ)
    (hA : A.Finite) :
    {z : ℤ |
      P2Rel kl_u kl_v kr_u kr_v A B z}.Finite := by

  let D : Set ℤ := {0, 1}

  have hD : D.Finite := by
    dsimp [D]
    simp

  have hprod :
      ((A ×ˢ D) ×ˢ D).Finite :=
    (hA.prod hD).prod hD

  have himage :
      ((fun p : (ℤ × ℤ) × ℤ =>
        p.1.1 - kl_u * p.1.2 - kl_v * p.2) ''
          ((A ×ˢ D) ×ˢ D)).Finite :=
    hprod.image _

  apply himage.subset

  intro z hz

  rcases hz with
    ⟨a, ha, b, hb, lu, ru, lv, rv,
      halpha, hdegree, hleft, hright⟩

  rcases halpha with
    ⟨hlu, hru, hlv, hrv, hu1, hu2, hv1, hv2⟩

  have hluD : lu ∈ D := by
    dsimp [D]
    simpa using hlu

  have hlvD : lv ∈ D := by
    dsimp [D]
    simpa using hlv

  refine ⟨((a, lu), lv), ?_, ?_⟩

  · exact ⟨⟨ha, hluD⟩, hlvD⟩

  · exact hleft.symm

private theorem finite_P2Set
    {A B : Set ℤ}
    (kl_u kl_v kr_u kr_v : ℤ)
    (hA : A.Finite)
    (hB : B.Finite) :
    (P2Set kl_u kl_v kr_u kr_v A B).Finite := by

  have hleft :
      {z : ℤ |
        P2Rel kl_u kl_v kr_u kr_v A B z}.Finite :=
    finite_P2Rel
      (A := A) (B := B)
      kl_u kl_v kr_u kr_v hA

  have hright :
      {z : ℤ |
        P2Rel kr_u kr_v kl_u kl_v B A z}.Finite :=
    finite_P2Rel
      (A := B) (B := A)
      kr_u kr_v kl_u kl_v hB

  have hu :
      ({z : ℤ |
        P2Rel kl_u kl_v kr_u kr_v A B z} ∪
       {z : ℤ |
        P2Rel kr_u kr_v kl_u kl_v B A z}).Finite :=
    hleft.union hright

  change
    ({z : ℤ |
      P2Rel kl_u kl_v kr_u kr_v A B z ∨
      P2Rel kr_u kr_v kl_u kl_v B A z}).Finite

  exact hu

private theorem finite_P3Rel
    {A B C : Set ℤ}
    (hA : A.Finite) :
    {z : ℤ | P3Rel A B C z}.Finite := by

  have hi :
      ((fun a : ℤ => a - 4) '' A).Finite :=
    hA.image _

  apply hi.subset

  intro z hz

  rcases hz with
    ⟨a, ha, b, hb, d, hd, h1, h2, h3⟩

  exact ⟨a, ha, h1.symm⟩

private theorem finite_P3Set
    {A B C : Set ℤ}
    (hA : A.Finite)
    (hB : B.Finite)
    (hC : C.Finite) :
    (P3Set A B C).Finite := by

  have h1 := finite_P3Rel (B := B) (C := C) hA
  have h2 := finite_P3Rel (B := C) (C := B) hA
  have h3 := finite_P3Rel (B := A) (C := C) hB
  have h4 := finite_P3Rel (B := C) (C := A) hB
  have h5 := finite_P3Rel (B := A) (C := B) hC
  have h6 := finite_P3Rel (B := B) (C := A) hC

  have hu :=
    h1.union
      (h2.union
        (h3.union
          (h4.union
            (h5.union h6))))

  change
    ({z : ℤ |
      P3Rel A B C z ∨
      P3Rel A C B z ∨
      P3Rel B A C z ∨
      P3Rel B C A z ∨
      P3Rel C A B z ∨
      P3Rel C B A z}).Finite

  exact hu

mutual

/-- T2.0: Sigma è finito per ogni albero. -/
theorem T2_0
    (t : SPTree) :
    (Sigma t).Finite := by

  cases t with

  | Q len =>
      exact finite_Band (len - 1)

  | S children =>
      exact sigmaList_finite children

  | P2 kl_u kl_v kr_u kr_v l r =>
      exact finite_P2Set
        kl_u kl_v kr_u kr_v
        (T2_0 l)
        (T2_0 r)

  | P3 l c r =>
      exact finite_P3Set
        (T2_0 l)
        (T2_0 c)
        (T2_0 r)

theorem sigmaList_finite
    (ts : List SPTree) :
    (SigmaList ts).Finite := by

  cases ts with

  | nil =>
      change ({0} : Set ℤ).Finite
      simp

  | cons t ts =>
      exact finite_Mink
        (T2_0 t)
        (sigmaList_finite ts)

end

/-! ## 16. Numero di componenti con passo 2 -/

/--
pieces2 conta gli inizi delle componenti massimali
con passo 2 di un insieme di interi.
-/
noncomputable def pieces2 (S : Set ℤ) : ℕ :=
  Set.ncard {x | x ∈ S ∧ x - 2 ∉ S}

/-! ## 17. Trasporto Finset–Set -/

/--
Insieme delle spiralità raddoppiate
corrispondenti a un Finset di spiralità intere.
-/
def doubleSet (A : Finset ℤ) : Set ℤ :=
  {z | ∃ a : ℤ, a ∈ A ∧ z = 2 * a}

private theorem doubleSet_neg
    (A : Finset ℤ)
    (hA : ∀ x, x ∈ A ↔ -x ∈ A)
    (z : ℤ)
    (hz : z ∈ doubleSet A) :
    -z ∈ doubleSet A := by

  rcases hz with ⟨a, ha, heq⟩

  refine ⟨-a, (hA a).mp ha, ?_⟩

  omega

private theorem band_eq_doubleSet
    (c : ℕ) :
    Band c =
      doubleSet (KeyLemma.symInterval c) := by

  ext z
  constructor

  · rintro ⟨s, hlo, hhi, heq⟩
    refine ⟨s, ?_, heq⟩
    exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩

  · rintro ⟨s, hs, heq⟩

    have hb := Finset.mem_Icc.mp hs

    exact ⟨s, hb.1, hb.2, heq⟩

private theorem alpha_pairs_iff
    (lu ru lv rv : ℤ) :
    Alpha lu ru lv rv ↔
      (lu, ru) ∈ KeyLemma.alphaPairs ∧
      (lv, rv) ∈ KeyLemma.alphaPairs := by

  simp only [
    Alpha,
    KeyLemma.alphaPairs,
    Finset.mem_insert,
    Finset.mem_singleton,
    Prod.mk.injEq
  ]

  omega

/-! ## 18. Trasporto della relazione P2Rel -/

private theorem p2rel_scaled
    (A B : Finset ℤ)
    (s : ℤ) :
    P2Rel 2 2 2 2
      (doubleSet A)
      (doubleSet B)
      (2 * s) ↔
    s ∈ KeyLemma.R A B := by

  classical

  constructor

  · intro h

    rcases h with
      ⟨aa, haa, bb, hbb,
        lu, ru, lv, rv,
        halpha, hdegree, hleft, hright⟩

    rcases haa with ⟨a, ha, haeq⟩
    rcases hbb with ⟨b, hb, hbeq⟩

    have hpairs :
        (lu, ru) ∈ KeyLemma.alphaPairs ∧
        (lv, rv) ∈ KeyLemma.alphaPairs :=
      (alpha_pairs_iff lu ru lv rv).mp halpha

    simp only [
      KeyLemma.R,
      Finset.mem_biUnion,
      Finset.mem_product,
      Finset.mem_image,
      Finset.mem_filter
    ]

    refine ⟨
      (a, b),
      ⟨ha, hb⟩,
      ((lu, ru), (lv, rv)),
      ?_,
      ?_
    ⟩

    · refine ⟨hpairs, ?_⟩
      dsimp
      omega

    · dsimp
      omega

  · intro h

    simp only [
      KeyLemma.R,
      Finset.mem_biUnion,
      Finset.mem_product,
      Finset.mem_image,
      Finset.mem_filter
    ] at h

    rcases h with
      ⟨⟨a, b⟩, ⟨ha, hb⟩,
        ⟨⟨lu, ru⟩, ⟨lv, rv⟩⟩,
        ⟨⟨hp, hq⟩, heq⟩,
        hval⟩

    have halpha :
        Alpha lu ru lv rv :=
      (alpha_pairs_iff lu ru lv rv).mpr ⟨hp, hq⟩

    change
      a - lu - lv = b + ru + rv
      at heq

    change
      a - lu - lv = s
      at hval

    refine ⟨
      2 * a,
      ⟨a, ha, rfl⟩,
      2 * b,
      ⟨b, hb, rfl⟩,
      lu, ru, lv, rv,
      halpha,
      ?_, ?_, ?_
    ⟩

    · constructor <;> intro h <;> omega
    · omega
    · omega

/-! ## 19. Simmetria generica di P2Set -/

private theorem p2set_neg_general
    {A B : Set ℤ}
    {kl_u kl_v kr_u kr_v z : ℤ}
    (hA : ∀ x, x ∈ A → -x ∈ A)
    (hB : ∀ x, x ∈ B → -x ∈ B)
    (h :
      z ∈ P2Set kl_u kl_v kr_u kr_v A B) :
    -z ∈ P2Set kl_u kl_v kr_u kr_v A B := by

  change
    P2Rel kl_u kl_v kr_u kr_v A B z ∨
    P2Rel kr_u kr_v kl_u kl_v B A z
    at h

  change
    P2Rel kl_u kl_v kr_u kr_v A B (-z) ∨
    P2Rel kr_u kr_v kl_u kl_v B A (-z)

  rcases h with h | h

  · right
    exact p2_swap hA hB h

  · left
    exact p2_swap hB hA h

/-! ## 20. Trasporto della semantica P2 -/

private theorem p2set_scaled
    (A B : Finset ℤ)
    (hA : ∀ x, x ∈ A ↔ -x ∈ A)
    (hB : ∀ x, x ∈ B ↔ -x ∈ B)
    (s : ℤ) :
    (2 * s) ∈
      P2Set 2 2 2 2
        (doubleSet A)
        (doubleSet B) ↔
    s ∈ KeyLemma.sigmaP A B := by

  classical

  let F : Finset ℤ :=
    KeyLemma.R A B ∪ KeyLemma.R B A

  have hcore :
      ∀ t : ℤ,
        t ∈ F ↔
        (2 * t) ∈
          P2Set 2 2 2 2
            (doubleSet A)
            (doubleSet B) := by

    intro t

    simp only [
      F,
      Finset.mem_union,
      P2Set,
      Set.mem_setOf_eq
    ]

    constructor

    · intro h
      rcases h with h | h
      · left
        exact (p2rel_scaled A B t).mpr h
      · right
        exact (p2rel_scaled B A t).mpr h

    · intro h
      rcases h with h | h
      · left
        exact (p2rel_scaled A B t).mp h
      · right
        exact (p2rel_scaled B A t).mp h

  have hnegA :
      ∀ x, x ∈ doubleSet A → -x ∈ doubleSet A :=
    doubleSet_neg A hA

  have hnegB :
      ∀ x, x ∈ doubleSet B → -x ∈ doubleSet B :=
    doubleSet_neg B hB

  constructor

  · intro h

    have hf : s ∈ F :=
      (hcore s).mpr h

    change
      s ∈ F ∪ F.image (fun x => -x)

    exact Finset.mem_union.mpr (Or.inl hf)

  · intro h

    change
      s ∈ F ∪ F.image (fun x => -x)
      at h

    rcases Finset.mem_union.mp h with hf | hf

    · exact (hcore s).mp hf

    · obtain ⟨t, ht, heq⟩ :=
        Finset.mem_image.mp hf

      have hp :
          (2 * t) ∈
            P2Set 2 2 2 2
              (doubleSet A)
              (doubleSet B) :=
        (hcore t).mp ht

      have hn :=
        p2set_neg_general hnegA hnegB hp

      have heq2 :
          -(2 * t) = 2 * s := by
        omega

      rw [heq2] at hn

      exact hn

/-! ## 21. Trasporto del numero di componenti -/

private theorem pieces2_doubleSet
    (A : Finset ℤ) :
    pieces2 (doubleSet A) =
      KeyLemma.pieces A := by

  classical

  have hstarts :
      {z : ℤ |
        z ∈ doubleSet A ∧
        z - 2 ∉ doubleSet A} =
      (↑((A.filter (fun x => x - 1 ∉ A)).image
        (fun x : ℤ => 2 * x)) : Set ℤ) := by

    ext z

    constructor

    · rintro ⟨⟨a, ha, heq⟩, hprev⟩

      subst z

      change
        2 * a ∈
          (A.filter (fun x => x - 1 ∉ A)).image
            (fun x : ℤ => 2 * x)

      apply Finset.mem_image.mpr

      refine ⟨a, ?_, rfl⟩

      apply Finset.mem_filter.mpr

      refine ⟨ha, ?_⟩

      intro h

      apply hprev

      refine ⟨a - 1, h, ?_⟩

      ring

    · intro hz

      change
        z ∈
          (A.filter (fun x => x - 1 ∉ A)).image
            (fun x : ℤ => 2 * x)
        at hz

      obtain ⟨a, ha, heq⟩ :=
        Finset.mem_image.mp hz

      obtain ⟨haa, hnot⟩ :=
        Finset.mem_filter.mp ha

      have hz2 : z = 2 * a := heq.symm

      subst z

      constructor

      · exact ⟨a, haa, rfl⟩

      · rintro ⟨b, hb, hbeq⟩

        have hbval : b = a - 1 := by
          omega

        apply hnot

        simpa [hbval] using hb

  unfold pieces2

  rw [hstarts]

  rw [Set.ncard_coe_finset]

  unfold KeyLemma.pieces

  exact
    Finset.card_image_of_injective
      (A.filter (fun x => x - 1 ∉ A))
      (by
        intro x y h
        have hdouble : (2 : ℤ) * x = 2 * y := h
        omega)

/-! ## 22. Dimezzamento di un insieme finito pari -/

private theorem halfFinset_spec
    (S : Set ℤ)
    (hfin : S.Finite)
    (heven : ∀ z, z ∈ S → Even z)
    (s : ℤ) :
    s ∈
      hfin.toFinset.image
        (fun z : ℤ => z / 2) ↔
    2 * s ∈ S := by

  classical

  constructor

  · intro hs

    obtain ⟨z, hz, heq⟩ :=
      Finset.mem_image.mp hs

    have hzS : z ∈ S :=
      hfin.mem_toFinset.mp hz

    obtain ⟨q, hq⟩ :=
      heven z hzS

    have hzdouble :
        z = 2 * (z / 2) := by
      omega

    have hsdouble :
        2 * s = z := by
      omega

    rw [hsdouble]

    exact hzS

  · intro hs

    apply Finset.mem_image.mpr

    refine ⟨
      2 * s,
      hfin.mem_toFinset.mpr hs,
      ?_
    ⟩

    omega

private theorem halfFinset_doubleSet
    (S : Set ℤ)
    (hfin : S.Finite)
    (heven : ∀ z, z ∈ S → Even z) :
    S =
      doubleSet
        (hfin.toFinset.image
          (fun z : ℤ => z / 2)) := by

  classical

  ext z

  constructor

  · intro hz

    obtain ⟨s, hs⟩ :=
      heven z hz

    have heq : z = 2 * s := by
      omega

    refine ⟨s, ?_, heq⟩

    apply
      (halfFinset_spec S hfin heven s).mpr

    rw [← heq]

    exact hz

  · rintro ⟨s, hs, heq⟩

    have hsS :=
      (halfFinset_spec S hfin heven s).mp hs

    rw [heq]

    exact hsS

/-! ## 23. Parità di un P2 con due figli pari -/

private theorem p2_even
    (A B : Set ℤ)
    (hA : ∀ z, z ∈ A → Even z)
    (hB : ∀ z, z ∈ B → Even z)
    (z : ℤ)
    (hz : z ∈ P2Set 2 2 2 2 A B) :
    Even z := by

  change
    P2Rel 2 2 2 2 A B z ∨
    P2Rel 2 2 2 2 B A z
    at hz

  rcases hz with h | h

  · rcases h with
      ⟨a, ha, b, hb, lu, ru, lv, rv,
        halpha, hdegree, hleft, hright⟩

    obtain ⟨s, hs⟩ :=
      hA a ha

    refine ⟨s - lu - lv, ?_⟩

    omega

  · rcases h with
      ⟨a, ha, b, hb, lu, ru, lv, rv,
        halpha, hdegree, hleft, hright⟩

    obtain ⟨s, hs⟩ :=
      hB a ha

    refine ⟨s - lu - lv, ?_⟩

    omega

/-! ## 24. T2.1 — P2 leggero con un figlio leggero -/

/--
T2.1.

Se il figlio destro è leggero e le spiralità
del figlio sinistro sono tutte pari, il numero
di componenti con passo 2 non aumenta
attraverso il nodo P2 con quattro k uguali a 2.
-/
theorem T2_1
    (l r : SPTree)
    (hr : Light r)
    (heven :
      ∀ z, z ∈ Sigma l → Even z) :
    pieces2 (Sigma (.P2 2 2 2 2 l r)) ≤
      pieces2 (Sigma l) := by

  classical

  rcases T1_3 r hr with
    hempty | ⟨c, hband⟩

  · have hresult :
        Sigma (.P2 2 2 2 2 l r) = ∅ := by

      ext z

      simp [
        Sigma,
        P2Set,
        P2Rel,
        hempty
      ]

    rw [hresult]

    simp [pieces2]

  · let A : Finset ℤ :=
      (T2_0 l).toFinset.image
        (fun z : ℤ => z / 2)

    let B : Finset ℤ :=
      KeyLemma.symInterval c

    have hA_spec :
        ∀ s : ℤ,
          s ∈ A ↔ 2 * s ∈ Sigma l := by

      intro s

      exact
        halfFinset_spec
          (Sigma l)
          (T2_0 l)
          heven
          s

    have hA_sym :
        ∀ s : ℤ,
          s ∈ A ↔ -s ∈ A := by

      intro s

      have h1 := hA_spec s
      have h2 := hA_spec (-s)
      have hsym := T1_1 l (2 * s)

      constructor

      · intro hs

        have hp := h1.mp hs

        have hn := hsym.mp hp

        apply h2.mpr

        convert hn using 1 <;> ring

      · intro hs

        have hp := h2.mp hs

        have hn :
            -(2 * s) ∈ Sigma l := by
          convert hp using 1 <;> ring

        exact h1.mpr (hsym.mpr hn)

    have hB_sym :
        ∀ s : ℤ,
          s ∈ B ↔ -s ∈ B := by

      intro s

      dsimp [B, KeyLemma.symInterval]

      simp only [Finset.mem_Icc]

      constructor <;> intro h <;> omega

    have hleft :
        Sigma l = doubleSet A := by

      exact
        halfFinset_doubleSet
          (Sigma l)
          (T2_0 l)
          heven

    have hright :
        Sigma r = doubleSet B := by

      rw [hband]

      exact band_eq_doubleSet c

    have hevenR :
        ∀ z, z ∈ Sigma r → Even z := by

      intro z hz

      exact T1_2 r hr z hz

    have hevenP :
        ∀ z,
          z ∈ Sigma (.P2 2 2 2 2 l r) →
          Even z := by

      intro z hz

      exact
        p2_even
          (Sigma l)
          (Sigma r)
          heven
          hevenR
          z hz

    have hresult :
        Sigma (.P2 2 2 2 2 l r) =
          doubleSet (KeyLemma.sigmaP A B) := by

      ext z

      constructor

      · intro hz

        obtain ⟨s, hs⟩ :=
          hevenP z hz

        have heq : z = 2 * s := by
          omega

        refine ⟨s, ?_, heq⟩

        have hp :
            (2 * s) ∈
              P2Set 2 2 2 2
                (doubleSet A)
                (doubleSet B) := by

          have hz' := hz

          rw [heq] at hz'

          change
            (2 * s) ∈
              P2Set 2 2 2 2
                (Sigma l)
                (Sigma r)
            at hz'

          rw [hleft, hright] at hz'

          exact hz'

        exact
          (p2set_scaled A B hA_sym hB_sym s).mp hp

      · rintro ⟨s, hs, heq⟩

        have hp :=
          (p2set_scaled A B hA_sym hB_sym s).mpr hs

        rw [heq]

        change
          (2 * s) ∈
            P2Set 2 2 2 2
              (Sigma l)
              (Sigma r)

        rw [hleft, hright]

        exact hp

    calc
      pieces2 (Sigma (.P2 2 2 2 2 l r))
          =
        KeyLemma.pieces (KeyLemma.sigmaP A B) := by

            rw [hresult]

            exact
              pieces2_doubleSet
                (KeyLemma.sigmaP A B)

      _ ≤ KeyLemma.pieces A := by

            change
              KeyLemma.pieces
                (KeyLemma.sigmaP A
                  (KeyLemma.symInterval c)) ≤
              KeyLemma.pieces A

            exact
              KeyLemma.key_lemma A c hA_sym

      _ = pieces2 (Sigma l) := by

            rw [hleft]

            exact (pieces2_doubleSet A).symm

/-!
## Tappa 3 — Bound combinatori sul numero di pezzi

T3.1: nodi S generali, bound moltiplicativo.
T3.2: nodi S con un figlio Band, bound non crescente.
T3.3: nodi P2, bound con costante 18.
T3.4: nodi P3, bound con costante 6.

Per T3.3 usiamo la costante 18, non 6.

Motivazione:
- Alpha ammette tre configurazioni per ciascun polo;
- ci sono quindi al massimo 3 * 3 = 9 configurazioni
  per ciascun ordine dei due figli;
- P2Set comprende due ordini;
- ogni configurazione contribuisce al massimo
  pieces2 A + pieces2 B pezzi.

Otteniamo quindi 2 * 9 = 18.

Per T3.4 usiamo la costante 6:
- P3Set comprende sei permutazioni;
- ogni permutazione contribuisce al massimo
  pieces2 A + pieces2 B + pieces2 C pezzi.

La condizione Degree4Angles viene mantenuta esattamente.
Non viene rimossa né indebolita.

Tutti gli enunciati assumono esplicitamente la finitezza
degli insiemi coinvolti.

Nessun nuovo assioma.
-/

/-! ## 26. Inizi delle componenti con passo 2 -/

private def starts2 (S : Set ℤ) : Set ℤ :=
  {x | x ∈ S ∧ x - 2 ∉ S}

private theorem starts2_finite
    {S : Set ℤ}
    (hS : S.Finite) :
    (starts2 S).Finite := by

  apply hS.subset

  intro x hx

  exact hx.1

/-! ## 27. Bound per l'unione -/

private theorem starts2_union_subset
    (S T : Set ℤ) :
    starts2 (S ∪ T) ⊆
      starts2 S ∪ starts2 T := by

  intro x hx

  rcases hx with ⟨hmem, hprev⟩

  rcases hmem with hS | hT

  · left

    constructor

    · exact hS

    · intro hp

      apply hprev

      exact Or.inl hp

  · right

    constructor

    · exact hT

    · intro hp

      apply hprev

      exact Or.inr hp

private theorem pieces2_union_le
    (S T : Set ℤ)
    (hS : S.Finite)
    (hT : T.Finite) :
    pieces2 (S ∪ T) ≤
      pieces2 S + pieces2 T := by

  have hfin :
      (starts2 S ∪ starts2 T).Finite :=
    (starts2_finite hS).union
      (starts2_finite hT)

  change
    (starts2 (S ∪ T)).ncard ≤
      (starts2 S).ncard +
      (starts2 T).ncard

  calc
    (starts2 (S ∪ T)).ncard
        ≤ (starts2 S ∪ starts2 T).ncard :=
          Set.ncard_le_ncard
            (starts2_union_subset S T)
            hfin

    _ ≤ (starts2 S).ncard +
          (starts2 T).ncard :=
          Set.ncard_union_le _ _

/-! ## 28. Bound per l'intersezione -/

private theorem starts2_inter_subset
    (S T : Set ℤ) :
    starts2 (S ∩ T) ⊆
      starts2 S ∪ starts2 T := by

  intro x hx

  rcases hx with
    ⟨⟨hxS, hxT⟩, hprev⟩

  by_cases hpS : x - 2 ∈ S

  · right

    constructor

    · exact hxT

    · intro hpT

      apply hprev

      exact ⟨hpS, hpT⟩

  · left

    exact ⟨hxS, hpS⟩

private theorem pieces2_inter_le
    (S T : Set ℤ)
    (hS : S.Finite)
    (hT : T.Finite) :
    pieces2 (S ∩ T) ≤
      pieces2 S + pieces2 T := by

  have hfin :
      (starts2 S ∪ starts2 T).Finite :=
    (starts2_finite hS).union
      (starts2_finite hT)

  change
    (starts2 (S ∩ T)).ncard ≤
      (starts2 S).ncard +
      (starts2 T).ncard

  calc
    (starts2 (S ∩ T)).ncard
        ≤ (starts2 S ∪ starts2 T).ncard :=
          Set.ncard_le_ncard
            (starts2_inter_subset S T)
            hfin

    _ ≤ (starts2 S).ncard +
          (starts2 T).ncard :=
          Set.ncard_union_le _ _

/-! ## 29. Invarianza per traslazione -/

/--
shiftSet S d rappresenta la traslazione S + d.
-/
private def shiftSet
    (S : Set ℤ)
    (d : ℤ) : Set ℤ :=
  {z | z - d ∈ S}

private theorem shiftSet_image
    (S : Set ℤ)
    (d : ℤ) :
    shiftSet S d =
      (fun x : ℤ => x + d) '' S := by

  ext z

  constructor

  · intro hz

    refine ⟨z - d, hz, ?_⟩

    change (z - d) + d = z

    omega

  · rintro ⟨x, hx, rfl⟩

    change x + d - d ∈ S

    have heq : x + d - d = x := by
      omega

    rw [heq]

    exact hx

private theorem finite_shiftSet
    {S : Set ℤ}
    (hS : S.Finite)
    (d : ℤ) :
    (shiftSet S d).Finite := by

  rw [shiftSet_image]

  exact hS.image _

private theorem starts2_shiftSet
    (S : Set ℤ)
    (d : ℤ) :
    starts2 (shiftSet S d) =
      shiftSet (starts2 S) d := by

  ext z

  change
    (z - d ∈ S ∧ z - 2 - d ∉ S) ↔
    (z - d ∈ S ∧ (z - d) - 2 ∉ S)

  have heq :
      z - 2 - d = (z - d) - 2 := by
    omega

  rw [heq]

private theorem pieces2_shiftSet
    (S : Set ℤ)
    (d : ℤ) :
    pieces2 (shiftSet S d) =
      pieces2 S := by

  have hinj :
      Function.Injective
        (fun x : ℤ => x + d) := by

    intro x y h

    change x + d = y + d at h

    omega

  calc
    pieces2 (shiftSet S d)
        = (starts2 (shiftSet S d)).ncard := rfl

    _ = (shiftSet (starts2 S) d).ncard := by
          rw [starts2_shiftSet]

    _ =
        ((fun x : ℤ => x + d) ''
          starts2 S).ncard := by
          rw [shiftSet_image]

    _ = (starts2 S).ncard :=
          Set.ncard_image_of_injective
            (starts2 S) hinj

    _ = pieces2 S := rfl

/-! ## 30. T3.1 — Somma di Minkowski -/

/--
T3.1.

Ogni inizio di componente della somma di Minkowski
ammette una rappresentazione a + b nella quale
a e b sono entrambi inizi di componente.

Di conseguenza il numero di pezzi della somma
non supera il prodotto dei numeri di pezzi.
-/
theorem T3_1
    (A B : Set ℤ)
    (hA : A.Finite)
    (hB : B.Finite) :
    pieces2 (Mink A B) ≤
      pieces2 A * pieces2 B := by

  let F : ℤ × ℤ → ℤ :=
    fun p => p.1 + p.2

  have hprod :
      (starts2 A ×ˢ starts2 B).Finite :=
    (starts2_finite hA).prod
      (starts2_finite hB)

  have hsubset :
      starts2 (Mink A B) ⊆
        F '' (starts2 A ×ˢ starts2 B) := by

    intro z hz

    rcases hz with
      ⟨⟨a, ha, b, hb, heq⟩, hprev⟩

    have hstartA : a ∈ starts2 A := by

      constructor

      · exact ha

      · intro hp

        apply hprev

        refine ⟨a - 2, hp, b, hb, ?_⟩

        omega

    have hstartB : b ∈ starts2 B := by

      constructor

      · exact hb

      · intro hp

        apply hprev

        refine ⟨a, ha, b - 2, hp, ?_⟩

        omega

    refine ⟨(a, b), ?_, ?_⟩

    · exact ⟨hstartA, hstartB⟩

    · exact heq.symm

  change
    (starts2 (Mink A B)).ncard ≤
      (starts2 A).ncard *
      (starts2 B).ncard

  calc
    (starts2 (Mink A B)).ncard
        ≤
      (F '' (starts2 A ×ˢ starts2 B)).ncard :=
        Set.ncard_le_ncard
          hsubset
          (hprod.image F)

    _ ≤ (starts2 A ×ˢ starts2 B).ncard :=
          Set.ncard_image_le hprod

    _ =
      (starts2 A).ncard *
        (starts2 B).ncard := by
          rw [Set.ncard_prod]

/-! ## 31. Numero di pezzi di Band -/

private theorem starts2_Band
    (c : ℕ) :
    starts2 (Band c) =
      {-(2 * (c : ℤ))} := by

  ext z

  constructor

  · intro hz

    rcases hz with
      ⟨⟨s, hlo, hhi, heq⟩, hprev⟩

    have hsmin :
        s = -(c : ℤ) := by

      by_contra hne

      have hlo' :
          -(c : ℤ) ≤ s - 1 := by
        omega

      have hhi' :
          s - 1 ≤ (c : ℤ) := by
        omega

      apply hprev

      refine ⟨s - 1, hlo', hhi', ?_⟩

      omega

    change z = -(2 * (c : ℤ))

    omega

  · intro hz

    have heq :
        z = -(2 * (c : ℤ)) := by
      simpa using hz

    rw [heq]

    constructor

    · refine ⟨
        -(c : ℤ),
        by omega,
        by omega,
        ?_
      ⟩

      ring

    · rintro ⟨s, hlo, hhi, hval⟩

      omega

private theorem pieces2_Band
    (c : ℕ) :
    pieces2 (Band c) = 1 := by

  change
    (starts2 (Band c)).ncard = 1

  rw [starts2_Band]

  simp

/-! ## 32. T3.2 — Somma con un intervallo leggero -/

/--
T3.2.

Band c contiene un solo pezzo con passo 2.

Il bound segue da T3.1.
-/
theorem T3_2
    (A : Set ℤ)
    (c : ℕ)
    (hA : A.Finite) :
    pieces2 (Mink A (Band c)) ≤
      pieces2 A := by

  have h :=
    T3_1 A (Band c) hA (finite_Band c)

  rw [pieces2_Band] at h

  simpa using h

/-! ## 33. Unioni finite indicizzate -/

/--
Unione di una famiglia di insiemi indicizzata
da un Finset.
-/
private def t3Union
    {ι : Type*}
    (u : Finset ι)
    (f : ι → Set ℤ) : Set ℤ :=
  {z | ∃ i ∈ u, z ∈ f i}

private theorem t3Union_empty
    {ι : Type*}
    (f : ι → Set ℤ) :
    t3Union ∅ f = ∅ := by

  ext z

  simp [t3Union]

private theorem t3Union_insert
    {ι : Type*}
    [DecidableEq ι]
    (a : ι)
    (u : Finset ι)
    (f : ι → Set ℤ) :
    t3Union (insert a u) f =
      f a ∪ t3Union u f := by

  ext z

  constructor

  · rintro ⟨i, hi, hz⟩

    rcases Finset.mem_insert.mp hi with
      rfl | hi

    · exact Or.inl hz

    · exact Or.inr ⟨i, hi, hz⟩

  · intro hz

    rcases hz with hz | hz

    · refine ⟨a, ?_, hz⟩

      simp

    · rcases hz with ⟨i, hi, hzi⟩

      refine ⟨i, ?_, hzi⟩

      exact Finset.mem_insert_of_mem hi

private theorem t3Union_finite
    {ι : Type*}
    (u : Finset ι)
    (f : ι → Set ℤ)
    (hf : ∀ i ∈ u, (f i).Finite) :
    (t3Union u f).Finite := by

  classical

  induction u using Finset.induction_on with

  | empty =>

      rw [t3Union_empty]

      exact Set.finite_empty

  | @insert a u ha ih =>

      have hfa :
          (f a).Finite :=
        hf a (Finset.mem_insert_self a u)

      have hfu :
          ∀ i ∈ u, (f i).Finite := by

        intro i hi

        exact hf i (Finset.mem_insert_of_mem hi)

      rw [t3Union_insert]

      exact hfa.union (ih hfu)

/--
Bound uniforme per un'unione di al più n insiemi.

Se ogni insieme ha al più K pezzi,
l'unione ne ha al più n*K.
-/
private theorem t3Union_bound
    {ι : Type*}
    (u : Finset ι)
    (f : ι → Set ℤ)
    (K : ℕ)
    (hf : ∀ i ∈ u, (f i).Finite)
    (hb : ∀ i ∈ u, pieces2 (f i) ≤ K) :
    pieces2 (t3Union u f) ≤
      u.card * K := by

  classical

  induction u using Finset.induction_on with

  | empty =>

      rw [t3Union_empty]

      simp [pieces2]

  | @insert a u ha ih =>

      have hfa :
          (f a).Finite :=
        hf a (Finset.mem_insert_self a u)

      have hfu :
          ∀ i ∈ u, (f i).Finite := by

        intro i hi

        exact hf i (Finset.mem_insert_of_mem hi)

      have hba :
          pieces2 (f a) ≤ K :=
        hb a (Finset.mem_insert_self a u)

      have hbu :
          ∀ i ∈ u, pieces2 (f i) ≤ K := by

        intro i hi

        exact hb i (Finset.mem_insert_of_mem hi)

      have hfinU :
          (t3Union u f).Finite :=
        t3Union_finite u f hfu

      have hIH :
          pieces2 (t3Union u f) ≤
            u.card * K :=
        ih hfu hbu

      rw [t3Union_insert]

      have hstep :=
        pieces2_union_le
          (f a)
          (t3Union u f)
          hfa
          hfinU

      calc
        pieces2 (f a ∪ t3Union u f)
            ≤ pieces2 (f a) +
                pieces2 (t3Union u f) :=
              hstep

        _ ≤ K + u.card * K := by
              omega

        _ = (insert a u).card * K := by
              rw [Finset.card_insert_of_notMem ha]
              ring

/-! ## 34. Configurazioni angolari P2 -/

/--
Le configurazioni di Alpha sono rappresentate da
due coppie (lu,ru) e (lv,rv).

Il numero complessivo è 3*3=9.
-/
private def t3AnglePairs :
    Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  KeyLemma.alphaPairs ×ˢ KeyLemma.alphaPairs

private theorem t3AnglePairs_card :
    t3AnglePairs.card = 9 := by

  decide

/--
Insieme prodotto dalla configurazione angolare uv.

La condizione Degree4Angles viene applicata esattamente.

Se la configurazione non è ammessa, il risultato è vuoto.

Se è ammessa, il risultato è l'intersezione
di due traslazioni degli insiemi dei figli.
-/
private noncomputable def t3P2Config
    (kl_u kl_v kr_u kr_v : ℤ)
    (A B : Set ℤ)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) : Set ℤ := by

  classical

  exact
    if Degree4Angles
        kl_u kl_v kr_u kr_v
        uv.1.1 uv.1.2 uv.2.1 uv.2.2 then

      shiftSet A
        (-(kl_u * uv.1.1 + kl_v * uv.2.1)) ∩

      shiftSet B
        (kr_u * uv.1.2 + kr_v * uv.2.2)

    else ∅

private theorem t3P2Config_finite
    (kl_u kl_v kr_u kr_v : ℤ)
    {A B : Set ℤ}
    (hA : A.Finite)
    (hB : B.Finite)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) :
    (t3P2Config
      kl_u kl_v kr_u kr_v A B uv).Finite := by

  by_cases hd :
      Degree4Angles
        kl_u kl_v kr_u kr_v
        uv.1.1 uv.1.2 uv.2.1 uv.2.2

  · rw [t3P2Config, if_pos hd]

    exact (finite_shiftSet hA _).inter_of_left _

  · rw [t3P2Config, if_neg hd]

    exact Set.finite_empty

private theorem t3P2Config_bound
    (kl_u kl_v kr_u kr_v : ℤ)
    (A B : Set ℤ)
    (hA : A.Finite)
    (hB : B.Finite)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) :
    pieces2
      (t3P2Config
        kl_u kl_v kr_u kr_v A B uv) ≤
      pieces2 A + pieces2 B := by

  by_cases hd :
      Degree4Angles
        kl_u kl_v kr_u kr_v
        uv.1.1 uv.1.2 uv.2.1 uv.2.2

  · rw [t3P2Config, if_pos hd]

    calc
      pieces2
        (shiftSet A
          (-(kl_u * uv.1.1 + kl_v * uv.2.1)) ∩
         shiftSet B
          (kr_u * uv.1.2 + kr_v * uv.2.2))

          ≤
        pieces2
          (shiftSet A
            (-(kl_u * uv.1.1 + kl_v * uv.2.1))) +
        pieces2
          (shiftSet B
            (kr_u * uv.1.2 + kr_v * uv.2.2)) :=

            pieces2_inter_le
              _ _
              (finite_shiftSet hA _)
              (finite_shiftSet hB _)

      _ = pieces2 A + pieces2 B := by
            rw [pieces2_shiftSet]
            rw [pieces2_shiftSet]

  · rw [t3P2Config, if_neg hd]

    simp [pieces2]

/-! ## 35. Decomposizione di P2Rel -/

/--
Un P2Rel è esattamente l'unione delle configurazioni
angolari ammesse.

La decomposizione è valida per coefficienti k arbitrari.
-/
private theorem t3P2Rel_eq
    (kl_u kl_v kr_u kr_v : ℤ)
    (A B : Set ℤ) :
    {z : ℤ |
      P2Rel kl_u kl_v kr_u kr_v A B z} =
    t3Union t3AnglePairs
      (t3P2Config kl_u kl_v kr_u kr_v A B) := by

  ext z

  constructor

  · intro hz

    rcases hz with
      ⟨a, ha, b, hb,
        lu, ru, lv, rv,
        halpha, hdegree,
        hleft, hright⟩

    have hpairs :
        (lu, ru) ∈ KeyLemma.alphaPairs ∧
        (lv, rv) ∈ KeyLemma.alphaPairs :=
      (alpha_pairs_iff lu ru lv rv).mp halpha

    refine ⟨((lu, ru), (lv, rv)), ?_, ?_⟩

    · exact Finset.mem_product.mpr hpairs

    · have hcfg :
          z ∈
            shiftSet A
              (-(kl_u * lu + kl_v * lv)) ∩
            shiftSet B
              (kr_u * ru + kr_v * rv) := by

        constructor

        · change
            z - (-(kl_u * lu + kl_v * lv)) ∈ A

          have heq :
              z - (-(kl_u * lu + kl_v * lv)) =
                a := by
            omega

          rw [heq]

          exact ha

        · change
            z - (kr_u * ru + kr_v * rv) ∈ B

          have heq :
              z - (kr_u * ru + kr_v * rv) =
                b := by
            omega

          rw [heq]

          exact hb

      simpa only [
        t3P2Config,
        if_pos hdegree
      ] using hcfg

  · intro hz

    rcases hz with
      ⟨⟨⟨lu, ru⟩, ⟨lv, rv⟩⟩,
        hpairs, hcfg⟩

    have hp :
        (lu, ru) ∈ KeyLemma.alphaPairs ∧
        (lv, rv) ∈ KeyLemma.alphaPairs :=
      Finset.mem_product.mp hpairs

    have halpha :
        Alpha lu ru lv rv :=
      (alpha_pairs_iff lu ru lv rv).mpr hp

    by_cases hd :
        Degree4Angles
          kl_u kl_v kr_u kr_v
          lu ru lv rv

    · have hh :
          z ∈
            shiftSet A
              (-(kl_u * lu + kl_v * lv)) ∩
            shiftSet B
              (kr_u * ru + kr_v * rv) := by

        simpa only [
          t3P2Config,
          if_pos hd
        ] using hcfg

      rcases hh with ⟨ha, hb⟩

      have ha' :
          z + kl_u * lu + kl_v * lv ∈ A := by

        have heq :
            z + kl_u * lu + kl_v * lv =
              z - (-(kl_u * lu + kl_v * lv)) := by
          ring

        rw [heq]

        exact ha

      have hb' :
          z - kr_u * ru - kr_v * rv ∈ B := by

        have heq :
            z - kr_u * ru - kr_v * rv =
              z - (kr_u * ru + kr_v * rv) := by
          ring

        rw [heq]

        exact hb

      refine ⟨
        z + kl_u * lu + kl_v * lv,
        ha',
        z - kr_u * ru - kr_v * rv,
        hb',
        lu, ru, lv, rv,
        halpha,
        hd,
        ?_, ?_
      ⟩

      · ring

      · ring

    · have hempty :
          z ∈ (∅ : Set ℤ) := by

        simpa [
          t3P2Config,
          hd
        ] using hcfg

      exact False.elim
        ((Set.notMem_empty z) hempty)

/-! ## 36. Bound per un ordine fissato di P2 -/

private theorem t3P2Rel_bound
    (kl_u kl_v kr_u kr_v : ℤ)
    (A B : Set ℤ)
    (hA : A.Finite)
    (hB : B.Finite) :
    pieces2
      {z : ℤ |
        P2Rel kl_u kl_v kr_u kr_v A B z} ≤
      9 * (pieces2 A + pieces2 B) := by

  rw [t3P2Rel_eq]

  have hfin :
      ∀ uv ∈ t3AnglePairs,
        (t3P2Config
          kl_u kl_v kr_u kr_v A B uv).Finite := by

    intro uv huv

    exact
      t3P2Config_finite
        kl_u kl_v kr_u kr_v
        hA hB uv

  have hbound :
      ∀ uv ∈ t3AnglePairs,
        pieces2
          (t3P2Config
            kl_u kl_v kr_u kr_v A B uv) ≤
          pieces2 A + pieces2 B := by

    intro uv huv

    exact
      t3P2Config_bound
        kl_u kl_v kr_u kr_v
        A B hA hB uv

  have h :=
    t3Union_bound
      t3AnglePairs
      (t3P2Config
        kl_u kl_v kr_u kr_v A B)
      (pieces2 A + pieces2 B)
      hfin
      hbound

  rw [t3AnglePairs_card] at h

  exact h

/-! ## 37. T3.3 — Nodo P2 generale -/

/--
T3.3 — Bound con costante 18.

La costante 18 deriva dalle nove configurazioni
angolari possibili per ciascuno dei due ordini.

La dimostrazione vale anche senza le ipotesi
sui coefficienti k; le manteniamo nell'enunciato
per rispecchiare il modello geometrico.
-/
theorem T3_3
    (A B : Set ℤ)
    (kl_u kl_v kr_u kr_v : ℤ)
    (hA : A.Finite)
    (hB : B.Finite)
    (hklu : kl_u = 1 ∨ kl_u = 2)
    (hklv : kl_v = 1 ∨ kl_v = 2)
    (hkru : kr_u = 1 ∨ kr_u = 2)
    (hkrv : kr_v = 1 ∨ kr_v = 2) :
    pieces2
      (P2Set kl_u kl_v kr_u kr_v A B) ≤
      18 * (pieces2 A + pieces2 B) := by

  let L : Set ℤ :=
    {z | P2Rel kl_u kl_v kr_u kr_v A B z}

  let R : Set ℤ :=
    {z | P2Rel kr_u kr_v kl_u kl_v B A z}

  have hLfinite : L.Finite :=
    finite_P2Rel
      (A := A) (B := B)
      kl_u kl_v kr_u kr_v hA

  have hRfinite : R.Finite :=
    finite_P2Rel
      (A := B) (B := A)
      kr_u kr_v kl_u kl_v hB

  have hLbound :
      pieces2 L ≤
        9 * (pieces2 A + pieces2 B) :=

    t3P2Rel_bound
      kl_u kl_v kr_u kr_v A B hA hB

  have hRbound :
      pieces2 R ≤
        9 * (pieces2 B + pieces2 A) :=

    t3P2Rel_bound
      kr_u kr_v kl_u kl_v B A hB hA

  have hset :
      P2Set kl_u kl_v kr_u kr_v A B =
        L ∪ R := by

    ext z

    simp only [
      P2Set,
      L,
      R,
      Set.mem_setOf_eq,
      Set.mem_union
    ]

  rw [hset]

  have hunion :=
    pieces2_union_le
      L R hLfinite hRfinite

  omega

/-! ## 38. Forma di P3Rel come intersezione -/

/--
P3Rel A B C è l'intersezione di tre insiemi:
A traslato di -4, B e C traslato di +4.
-/
private theorem t3P3Rel_eq
    (A B C : Set ℤ) :
    {z : ℤ | P3Rel A B C z} =
      (shiftSet A (-4) ∩ B) ∩
        shiftSet C 4 := by

  ext z

  constructor

  · intro hz

    rcases hz with
      ⟨a, ha, b, hb, d, hd,
        h1, h2, h3⟩

    constructor

    · constructor

      · change z - (-4) ∈ A

        have heq :
            z - (-4) = a := by
          omega

        rw [heq]

        exact ha

      · have heq : z = b := h2

        rw [heq]

        exact hb

    · change z - 4 ∈ C

      have heq :
          z - 4 = d := by
        omega

      rw [heq]

      exact hd

  · intro hz

    rcases hz with
      ⟨⟨ha, hb⟩, hc⟩

    have ha' :
        z + 4 ∈ A := by

      have heq :
          z + 4 = z - (-4) := by
        omega

      rw [heq]

      exact ha

    have hc' :
        z - 4 ∈ C := hc

    refine ⟨
      z + 4,
      ha',
      z,
      hb,
      z - 4,
      hc',
      ?_, ?_, ?_
    ⟩

    · omega

    · rfl

    · omega

/-! ## 39. Bound per una permutazione di P3 -/

private theorem t3P3Rel_bound
    (A B C : Set ℤ)
    (hA : A.Finite)
    (hB : B.Finite)
    (hC : C.Finite) :
    pieces2
      {z : ℤ | P3Rel A B C z} ≤
      pieces2 A + pieces2 B + pieces2 C := by

  rw [t3P3Rel_eq]

  have hAsh :
      (shiftSet A (-4)).Finite :=
    finite_shiftSet hA (-4)

  have hCsh :
      (shiftSet C 4).Finite :=
    finite_shiftSet hC 4

  have hAB :
      (shiftSet A (-4) ∩ B).Finite :=
    hAsh.inter_of_left _

  have hfirst :=
    pieces2_inter_le
      (shiftSet A (-4))
      B
      hAsh
      hB

  have hsecond :=
    pieces2_inter_le
      (shiftSet A (-4) ∩ B)
      (shiftSet C 4)
      hAB
      hCsh

  rw [pieces2_shiftSet] at hfirst

  rw [pieces2_shiftSet] at hsecond

  omega

/-! ## 40. T3.4 — Nodo P3 -/

/--
T3.4 — Bound con costante 6.

P3Set è l'unione delle sei permutazioni.

Ogni permutazione è un'intersezione di tre
insiemi traslati e contribuisce al massimo
pieces2 A + pieces2 B + pieces2 C pezzi.
-/
theorem T3_4
    (A B C : Set ℤ)
    (hA : A.Finite)
    (hB : B.Finite)
    (hC : C.Finite) :
    pieces2 (P3Set A B C) ≤
      6 * (pieces2 A + pieces2 B + pieces2 C) := by

  let X1 : Set ℤ :=
    {z | P3Rel A B C z}

  let X2 : Set ℤ :=
    {z | P3Rel A C B z}

  let X3 : Set ℤ :=
    {z | P3Rel B A C z}

  let X4 : Set ℤ :=
    {z | P3Rel B C A z}

  let X5 : Set ℤ :=
    {z | P3Rel C A B z}

  let X6 : Set ℤ :=
    {z | P3Rel C B A z}

  have hF1 : X1.Finite :=
    finite_P3Rel
      (A := A) (B := B) (C := C) hA

  have hF2 : X2.Finite :=
    finite_P3Rel
      (A := A) (B := C) (C := B) hA

  have hF3 : X3.Finite :=
    finite_P3Rel
      (A := B) (B := A) (C := C) hB

  have hF4 : X4.Finite :=
    finite_P3Rel
      (A := B) (B := C) (C := A) hB

  have hF5 : X5.Finite :=
    finite_P3Rel
      (A := C) (B := A) (C := B) hC

  have hF6 : X6.Finite :=
    finite_P3Rel
      (A := C) (B := B) (C := A) hC

  have hB1 :
      pieces2 X1 ≤
        pieces2 A + pieces2 B + pieces2 C :=
    t3P3Rel_bound A B C hA hB hC

  have hB2 :
      pieces2 X2 ≤
        pieces2 A + pieces2 C + pieces2 B :=
    t3P3Rel_bound A C B hA hC hB

  have hB3 :
      pieces2 X3 ≤
        pieces2 B + pieces2 A + pieces2 C :=
    t3P3Rel_bound B A C hB hA hC

  have hB4 :
      pieces2 X4 ≤
        pieces2 B + pieces2 C + pieces2 A :=
    t3P3Rel_bound B C A hB hC hA

  have hB5 :
      pieces2 X5 ≤
        pieces2 C + pieces2 A + pieces2 B :=
    t3P3Rel_bound C A B hC hA hB

  have hB6 :
      pieces2 X6 ≤
        pieces2 C + pieces2 B + pieces2 A :=
    t3P3Rel_bound C B A hC hB hA

  have hset :
      P3Set A B C =
        (((((X1 ∪ X2) ∪ X3) ∪ X4) ∪ X5) ∪ X6) := by

    ext z

    simp only [
      P3Set,
      X1, X2, X3, X4, X5, X6,
      Set.mem_setOf_eq,
      Set.mem_union,
      or_assoc
    ]

  have hF12 :
      (X1 ∪ X2).Finite :=
    hF1.union hF2

  have hF123 :
      ((X1 ∪ X2) ∪ X3).Finite :=
    hF12.union hF3

  have hF1234 :
      (((X1 ∪ X2) ∪ X3) ∪ X4).Finite :=
    hF123.union hF4

  have hF12345 :
      ((((X1 ∪ X2) ∪ X3) ∪ X4) ∪ X5).Finite :=
    hF1234.union hF5

  have h12 :=
    pieces2_union_le
      X1 X2 hF1 hF2

  have h123 :=
    pieces2_union_le
      (X1 ∪ X2) X3 hF12 hF3

  have h1234 :=
    pieces2_union_le
      ((X1 ∪ X2) ∪ X3)
      X4 hF123 hF4

  have h12345 :=
    pieces2_union_le
      (((X1 ∪ X2) ∪ X3) ∪ X4)
      X5 hF1234 hF5

  have h123456 :=
    pieces2_union_le
      ((((X1 ∪ X2) ∪ X3) ∪ X4) ∪ X5)
      X6 hF12345 hF6

  rw [hset]

  omega

/-! ## 41. Controllo degli assiomi della tappa 3 -/

#print axioms T3_1
#print axioms T3_2
#print axioms T3_3
#print axioms T3_4

            

/-!
## Tappa 4 — Bound globale sull'albero SPQ*

T4.0: Light t → bnd t = 1 e 1 ≤ bnd t.
T4.1: WF t → pieces2 (Sigma t) ≤ bnd t.
T4.2: bnd t ≤ 36 ^ costly t.
T4.3: WF t → pieces2 (Sigma t) ≤ 36 ^ costly t.

Le definizioni precedenti rimangono invariate.

Per P2 si usa la costante 18 della tappa 3.
Per P3 si usa la costante 6 della tappa 3.

La dimostrazione di T4.1 usa il bound per P2Rel
con coefficienti arbitrari, già dimostrato nella tappa 3.
Questo è necessario perché SPTree ammette coefficienti
interi arbitrari, mentre T3_3 enuncia esplicitamente
l'ipotesi k ∈ {1,2}.

Non vengono introdotti nuovi assiomi.
-/

open scoped Classical

/-! ## 42. Predicati ausiliari -/

private def AllKTwo
    (kl_u kl_v kr_u kr_v : ℤ) : Prop :=
  kl_u = 2 ∧
  kl_v = 2 ∧
  kr_u = 2 ∧
  kr_v = 2

private def CheapP2
    (kl_u kl_v kr_u kr_v : ℤ)
    (l r : SPTree) : Prop :=
  AllKTwo kl_u kl_v kr_u kr_v ∧
    (Light l ∨ Light r)

/--
Un nodo S è costoso se contiene almeno due
occorrenze di figli non leggeri.

Usiamo List.filter, quindi due occorrenze identiche
sono contate separatamente.
-/
private noncomputable def HasTwoHeavy
    (cs : List SPTree) : Prop := by
  classical
  exact
    2 ≤
      (cs.filter
        (fun t => decide (¬ Light t))).length

/-! ## 43. Buona formazione -/

/-
WF è un'ipotesi strutturale del modello.

Per ogni nodo P2 con tutti i coefficienti uguali a 2,
le spiralità di entrambi i figli devono essere pari.

La proprietà è richiesta ricorsivamente per tutti
i sottoalberi.
-/
mutual

def WF : SPTree → Prop
  | .Q _ =>
      True

  | .S children =>
      WFList children

  | .P2 kl_u kl_v kr_u kr_v l r =>
      WF l ∧
      WF r ∧
      (AllKTwo kl_u kl_v kr_u kr_v →
        (∀ z, z ∈ Sigma l → Even z) ∧
        (∀ z, z ∈ Sigma r → Even z))

  | .P3 l c r =>
      WF l ∧ WF c ∧ WF r

def WFList : List SPTree → Prop
  | [] =>
      True

  | t :: ts =>
      WF t ∧ WFList ts

end

/-! ## 44. Funzione di bound -/

/-
bnd è il bound ricorsivo richiesto.

Nei P2 si privilegia il figlio leggero destro.
Se non esiste, si considera il figlio leggero sinistro.
Negli altri casi si applica il bound con costante 18.
-/
mutual

noncomputable def bnd : SPTree → ℕ
  | .Q _ =>
      1

  | .S children =>
      bndList children

  | .P2 kl_u kl_v kr_u kr_v l r =>
      by
        classical
        exact
          if AllKTwo kl_u kl_v kr_u kr_v ∧ Light r then
            bnd l
          else if AllKTwo kl_u kl_v kr_u kr_v ∧ Light l then
            bnd r
          else
            18 * (bnd l + bnd r)

  | .P3 l c r =>
      6 * (bnd l + bnd c + bnd r)

noncomputable def bndList : List SPTree → ℕ
  | [] =>
      1

  | t :: ts =>
      bnd t * bndList ts

end

/-! ## 45. Numero di nodi costosi -/

/-
costly conta:
- ogni nodo P3;
- ogni P2 che non rientra nei due casi leggeri;
- ogni S con almeno due figli non leggeri.

Il costo dei sottoalberi viene sempre sommato.
-/
mutual

noncomputable def costly : SPTree → ℕ
  | .Q _ =>
      0

  | .S children =>
      by
        classical
        exact
          costlyList children +
            (if HasTwoHeavy children then 1 else 0)

  | .P2 kl_u kl_v kr_u kr_v l r =>
      by
        classical
        exact
          costly l + costly r +
            (if CheapP2 kl_u kl_v kr_u kr_v l r
             then 0
             else 1)

  | .P3 l c r =>
      costly l + costly c + costly r + 1

noncomputable def costlyList : List SPTree → ℕ
  | [] =>
      0

  | t :: ts =>
      costly t + costlyList ts

end

/-! ## 46. T4.0 — Proprietà elementari di bnd -/

/-
T4.0 comprende entrambe le proprietà:

1. se t è leggero, bnd t = 1;
2. per ogni t, bnd t ≥ 1.

La dimostrazione è simultanea sugli alberi
e sulle liste di figli.
-/
mutual

theorem T4_0
    (t : SPTree) :
    (Light t → bnd t = 1) ∧
    1 ≤ bnd t := by

  cases t with

  | Q len =>

      constructor

      · intro _
        rfl

      · norm_num [bnd]

  | S children =>

      exact t4_bndList_basic children

  | P2 kl_u kl_v kr_u kr_v l r =>

      have ihL := T4_0 l
      have ihR := T4_0 r

      constructor

      · intro hlight

        rcases hlight with
          ⟨hku, hkv, hru, hrv, hl, hr⟩

        have hall :
            AllKTwo kl_u kl_v kr_u kr_v := by

          exact ⟨hku, hkv, hru, hrv⟩

        have hcheap :
            AllKTwo kl_u kl_v kr_u kr_v ∧
              Light r :=
          ⟨hall, hr⟩

        change
          (if AllKTwo kl_u kl_v kr_u kr_v ∧ Light r
           then bnd l
           else if AllKTwo kl_u kl_v kr_u kr_v ∧ Light l
           then bnd r
           else 18 * (bnd l + bnd r)) = 1

        rw [if_pos hcheap]

        exact ihL.1 hl

      · change
          1 ≤
            (if AllKTwo kl_u kl_v kr_u kr_v ∧ Light r
             then bnd l
             else if AllKTwo kl_u kl_v kr_u kr_v ∧ Light l
             then bnd r
             else 18 * (bnd l + bnd r))

        split_ifs

        · exact ihL.2

        · exact ihR.2

        · omega

  | P3 l c r =>

      constructor

      · intro hlight

        exact False.elim hlight

      · have hl := (T4_0 l).2
        have hc := (T4_0 c).2
        have hr := (T4_0 r).2

        change
          1 ≤ 6 * (bnd l + bnd c + bnd r)

        omega

private theorem t4_bndList_basic
    (ts : List SPTree) :
    (LightList ts → bndList ts = 1) ∧
    1 ≤ bndList ts := by

  cases ts with

  | nil =>

      constructor

      · intro _
        rfl

      · norm_num [bndList]

  | cons t ts =>

      have ihT := T4_0 t
      have ihTs := t4_bndList_basic ts

      constructor

      · intro hlight

        rcases hlight with ⟨ht, hts⟩

        change
          bnd t * bndList ts = 1

        rw [ihT.1 ht, ihTs.1 hts]

  

      · change
          1 ≤ bnd t * bndList ts

        have h1 := ihT.2
        have h2 := ihTs.2

        nlinarith

end

/-! ## 47. Simmetria dei P2 con quattro k uguali a 2 -/

private theorem t4_P2Set_comm
    (A B : Set ℤ) :
    P2Set 2 2 2 2 A B =
      P2Set 2 2 2 2 B A := by

  ext z

  change
    (P2Rel 2 2 2 2 A B z ∨
     P2Rel 2 2 2 2 B A z) ↔
    (P2Rel 2 2 2 2 B A z ∨
     P2Rel 2 2 2 2 A B z)

  exact or_comm

/-! ## 48. Bound P2 con coefficienti arbitrari -/

/--
Versione del bound P2 con costante 18 senza restrizioni
sui coefficienti.

Deriva direttamente dal lemma t3P2Rel_bound,
che è valido per coefficienti interi arbitrari.

Questo lemma non modifica T3_3.
-/
private theorem t4_P2_general
    (A B : Set ℤ)
    (kl_u kl_v kr_u kr_v : ℤ)
    (hA : A.Finite)
    (hB : B.Finite) :
    pieces2
      (P2Set kl_u kl_v kr_u kr_v A B) ≤
      18 * (pieces2 A + pieces2 B) := by

  let L : Set ℤ :=
    {z | P2Rel kl_u kl_v kr_u kr_v A B z}

  let R : Set ℤ :=
    {z | P2Rel kr_u kr_v kl_u kl_v B A z}

  have hLF : L.Finite :=
    finite_P2Rel
      (A := A) (B := B)
      kl_u kl_v kr_u kr_v hA

  have hRF : R.Finite :=
    finite_P2Rel
      (A := B) (B := A)
      kr_u kr_v kl_u kl_v hB

  have hLB :
      pieces2 L ≤
        9 * (pieces2 A + pieces2 B) :=
    t3P2Rel_bound
      kl_u kl_v kr_u kr_v A B hA hB

  have hRB :
      pieces2 R ≤
        9 * (pieces2 B + pieces2 A) :=
    t3P2Rel_bound
      kr_u kr_v kl_u kl_v B A hB hA

  have hset :
      P2Set kl_u kl_v kr_u kr_v A B =
        L ∪ R := by

    ext z

    simp only [
      P2Set,
      L,
      R,
      Set.mem_setOf_eq,
      Set.mem_union
    ]

  rw [hset]

  have hu :=
    pieces2_union_le L R hLF hRF

  omega

/-! ## 49. T4.1 — Bound strutturale -/

/-
T4.1.

La prova procede per induzione simultanea
sugli alberi e sulle liste di figli.

Per i P2 con un figlio leggero si usa T2_1.
Per gli altri P2 si usa t4_P2_general.
Per i P3 si usa T3_4.
Per i nodi S si usa T3_1.
-/
mutual

theorem T4_1
    (t : SPTree)
    (hwf : WF t) :
    pieces2 (Sigma t) ≤ bnd t := by

  cases t with

  | Q len =>

      change
        pieces2 (Band (len - 1)) ≤ 1

      rw [pieces2_Band]

  | S children =>

      exact t4_bndList_sound children hwf

  | P2 kl_u kl_v kr_u kr_v l r =>

      rcases hwf with
        ⟨hwfL, hwfR, hparity⟩

      have ihL :
          pieces2 (Sigma l) ≤ bnd l :=
        T4_1 l hwfL

      have ihR :
          pieces2 (Sigma r) ≤ bnd r :=
        T4_1 r hwfR

      by_cases hcheapR :
          AllKTwo kl_u kl_v kr_u kr_v ∧
            Light r

      · rcases hcheapR with ⟨hall, hlightR⟩

        have hevenL :
            ∀ z, z ∈ Sigma l → Even z :=
          (hparity hall).1

        have hku : kl_u = 2 := hall.1
        have hkv : kl_v = 2 := hall.2.1
        have hru : kr_u = 2 := hall.2.2.1
        have hrv : kr_v = 2 := hall.2.2.2

        have hstep :
            pieces2
              (Sigma (.P2 2 2 2 2 l r)) ≤
              pieces2 (Sigma l) :=
          T2_1 l r hlightR hevenL

        have hresult :
            pieces2
              (Sigma (.P2 kl_u kl_v kr_u kr_v l r)) ≤
              bnd l := by

          rw [hku, hkv, hru, hrv]

          exact hstep.trans ihL

        change
          pieces2
            (Sigma (.P2 kl_u kl_v kr_u kr_v l r)) ≤
          (if AllKTwo kl_u kl_v kr_u kr_v ∧ Light r
           then bnd l
           else if AllKTwo kl_u kl_v kr_u kr_v ∧ Light l
           then bnd r
           else 18 * (bnd l + bnd r))

        rw [if_pos ⟨hall, hlightR⟩]

        exact hresult

      · by_cases hcheapL :
            AllKTwo kl_u kl_v kr_u kr_v ∧
              Light l

        · rcases hcheapL with ⟨hall, hlightL⟩

          have hevenR :
              ∀ z, z ∈ Sigma r → Even z :=
            (hparity hall).2

          have hku : kl_u = 2 := hall.1
          have hkv : kl_v = 2 := hall.2.1
          have hru : kr_u = 2 := hall.2.2.1
          have hrv : kr_v = 2 := hall.2.2.2

          have hstep :
              pieces2
                (Sigma (.P2 2 2 2 2 r l)) ≤
                pieces2 (Sigma r) :=
            T2_1 r l hlightL hevenR

          have hcomm :
              Sigma (.P2 2 2 2 2 l r) =
                Sigma (.P2 2 2 2 2 r l) := by

            change
              P2Set 2 2 2 2
                (Sigma l) (Sigma r) =
              P2Set 2 2 2 2
                (Sigma r) (Sigma l)

            exact
              t4_P2Set_comm (Sigma l) (Sigma r)

          have hresult :
              pieces2
                (Sigma (.P2 kl_u kl_v kr_u kr_v l r)) ≤
                bnd r := by

            rw [hku, hkv, hru, hrv]

            rw [hcomm]

            exact hstep.trans ihR

          change
            pieces2
              (Sigma (.P2 kl_u kl_v kr_u kr_v l r)) ≤
            (if AllKTwo kl_u kl_v kr_u kr_v ∧ Light r
             then bnd l
             else if AllKTwo kl_u kl_v kr_u kr_v ∧ Light l
             then bnd r
             else 18 * (bnd l + bnd r))

          rw [
            if_neg hcheapR,
            if_pos ⟨hall, hlightL⟩
          ]

          exact hresult

        · have hstep :
              pieces2
                (P2Set kl_u kl_v kr_u kr_v
                  (Sigma l) (Sigma r)) ≤
              18 *
                (pieces2 (Sigma l) +
                 pieces2 (Sigma r)) :=

            t4_P2_general
              (Sigma l)
              (Sigma r)
              kl_u kl_v kr_u kr_v
              (T2_0 l)
              (T2_0 r)

          have hbound :
              pieces2
                (P2Set kl_u kl_v kr_u kr_v
                  (Sigma l) (Sigma r)) ≤
              18 * (bnd l + bnd r) := by

            calc
              pieces2
                  (P2Set kl_u kl_v kr_u kr_v
                    (Sigma l) (Sigma r))
                  ≤
                18 *
                  (pieces2 (Sigma l) +
                   pieces2 (Sigma r)) :=
                    hstep

              _ ≤ 18 * (bnd l + bnd r) := by
                    omega

          change
            pieces2
              (P2Set kl_u kl_v kr_u kr_v
                (Sigma l) (Sigma r)) ≤
            (if AllKTwo kl_u kl_v kr_u kr_v ∧ Light r
             then bnd l
             else if AllKTwo kl_u kl_v kr_u kr_v ∧ Light l
             then bnd r
             else 18 * (bnd l + bnd r))

          rw [
            if_neg hcheapR,
            if_neg hcheapL
          ]

          exact hbound

  | P3 l c r =>

      rcases hwf with ⟨hwfL, hwfC, hwfR⟩

      have ihL :
          pieces2 (Sigma l) ≤ bnd l :=
        T4_1 l hwfL

      have ihC :
          pieces2 (Sigma c) ≤ bnd c :=
        T4_1 c hwfC

      have ihR :
          pieces2 (Sigma r) ≤ bnd r :=
        T4_1 r hwfR

      change
        pieces2
          (P3Set (Sigma l) (Sigma c) (Sigma r)) ≤
        6 * (bnd l + bnd c + bnd r)

      calc
        pieces2
            (P3Set (Sigma l) (Sigma c) (Sigma r))
            ≤
          6 *
            (pieces2 (Sigma l) +
             pieces2 (Sigma c) +
             pieces2 (Sigma r)) :=

              T3_4
                (Sigma l)
                (Sigma c)
                (Sigma r)
                (T2_0 l)
                (T2_0 c)
                (T2_0 r)

        _ ≤ 6 * (bnd l + bnd c + bnd r) := by
              omega

private theorem t4_bndList_sound
    (ts : List SPTree)
    (hwf : WFList ts) :
    pieces2 (SigmaList ts) ≤ bndList ts := by

  cases ts with

  | nil =>

      change
        pieces2 ({0} : Set ℤ) ≤ 1

      have hband :
          ({0} : Set ℤ) = Band 0 :=
        band_zero.symm

      rw [hband, pieces2_Band]

  | cons t ts =>

      rcases hwf with ⟨hwfT, hwfTs⟩

      have ihT :
          pieces2 (Sigma t) ≤ bnd t :=
        T4_1 t hwfT

      have ihTs :
          pieces2 (SigmaList ts) ≤ bndList ts :=
        t4_bndList_sound ts hwfTs

      change
        pieces2
          (Mink (Sigma t) (SigmaList ts)) ≤
        bnd t * bndList ts

      calc
        pieces2
            (Mink (Sigma t) (SigmaList ts))
            ≤
          pieces2 (Sigma t) *
            pieces2 (SigmaList ts) :=

              T3_1
                (Sigma t)
                (SigmaList ts)
                (T2_0 t)
                (sigmaList_finite ts)

        _ ≤ bnd t * bndList ts := by
              exact Nat.mul_le_mul ihT ihTs

end

/-! ## 50. Lemmi aritmetici -/

/--
La potenza di 36 è sempre almeno 1.
-/
private theorem t4_pow_pos
    (n : ℕ) :
    1 ≤ (36 : ℕ) ^ n := by

    exact Nat.one_le_pow _ _ (by norm_num)

/--
Se y ≥ 1, allora x ≤ xy.
-/
private theorem t4_le_mul
    (x y : ℕ)
    (hy : 1 ≤ y) :
    x ≤ x * y := by

  calc
    x = x * 1 := by simp

    _ ≤ x * y :=
      Nat.mul_le_mul_left x hy

/--
Bound aritmetico per i P2 costosi.
-/
private theorem t4_P2_arith
    (x y : ℕ)
    (hx : 1 ≤ x)
    (hy : 1 ≤ y) :
    18 * (x + y) ≤
      36 * (x * y) := by

  have h1 :
      x ≤ x * y :=
    t4_le_mul x y hy

  have h2 :
      y ≤ x * y := by

    calc
      y ≤ y * x :=
        t4_le_mul y x hx

      _ = x * y :=
        Nat.mul_comm y x

  omega

/--
Bound aritmetico per i P3.
-/
private theorem t4_P3_arith
    (x y z : ℕ)
    (hx : 1 ≤ x)
    (hy : 1 ≤ y)
    (hz : 1 ≤ z) :
    6 * (x + y + z) ≤
      36 * (x * y * z) := by

  have hxy :
      1 ≤ x * y := by

    nlinarith

  have hx1 :
      x ≤ x * y :=
    t4_le_mul x y hy

  have hx2 :
      x * y ≤ x * y * z :=
    t4_le_mul (x * y) z hz

  have hX :
      x ≤ x * y * z :=
    hx1.trans hx2

  have hy1 :
      y ≤ y * x :=
    t4_le_mul y x hx

  have hy2 :
      y ≤ x * y := by

    calc
      y ≤ y * x := hy1

      _ = x * y := Nat.mul_comm y x

  have hY :
      y ≤ x * y * z :=
    hy2.trans hx2

  have hz1 :
      z ≤ z * (x * y) :=
    t4_le_mul z (x * y) hxy

  have hZ :
      z ≤ x * y * z := by

    calc
      z ≤ z * (x * y) := hz1

      _ = x * y * z := by ring

  omega

/--
Monotonia della moltiplicazione rispetto
ai due fattori.
-/
private theorem t4_mul_mono
    {a b c d : ℕ}
    (hac : a ≤ c)
    (hbd : b ≤ d) :
    a * b ≤ c * d := by

  calc
    a * b ≤ c * b :=
      Nat.mul_le_mul_right b hac

    _ ≤ c * d :=
      Nat.mul_le_mul_left c hbd

/--
Una potenza di 36 non diminuisce aggiungendo
un esponente non negativo.
-/
private theorem t4_pow_add_le
    (a b : ℕ) :
    (36 : ℕ) ^ a ≤
      36 ^ (a + b) := by

  rw [pow_add]

  exact
    t4_le_mul
      (36 ^ a)
      (36 ^ b)
      (t4_pow_pos b)

/-! ## 51. T4.2 — Bound esponenziale -/

/-
T4.2.

Il bound ricorsivo è dominato da 36 elevato
al numero dei nodi costosi.

La dimostrazione simultanea sulle liste sfrutta
la moltiplicatività delle potenze.

Nei nodi S il costo aggiuntivo è non negativo:
non è necessario utilizzarlo per ottenere
la disuguaglianza, perché bndList è già
controllato dal prodotto dei bound dei figli.
-/
mutual

theorem T4_2
    (t : SPTree) :
    bnd t ≤ 36 ^ (costly t) := by

  cases t with

  | Q len =>

      norm_num [bnd, costly]

  | S children =>

      have ih :
          bndList children ≤
            36 ^ (costlyList children) :=
        t4_bndList_exp children

      change
        bndList children ≤
          36 ^
            (costlyList children +
              (if HasTwoHeavy children then 1 else 0))

      by_cases hh : HasTwoHeavy children

      · rw [if_pos hh]

        calc
          bndList children
              ≤ 36 ^ (costlyList children) :=
                ih

          _ ≤ 36 ^ (costlyList children + 1) :=
                t4_pow_add_le
                  (costlyList children) 1

      · rw [if_neg hh]

        simpa using ih

  | P2 kl_u kl_v kr_u kr_v l r =>

      have ihL :
          bnd l ≤ 36 ^ (costly l) :=
        T4_2 l

      have ihR :
          bnd r ≤ 36 ^ (costly r) :=
        T4_2 r

      have hpL :
          1 ≤ bnd l :=
        (T4_0 l).2

      have hpR :
          1 ≤ bnd r :=
        (T4_0 r).2

      change
        (if AllKTwo kl_u kl_v kr_u kr_v ∧ Light r
         then bnd l
         else if AllKTwo kl_u kl_v kr_u kr_v ∧ Light l
         then bnd r
         else 18 * (bnd l + bnd r))
          ≤
        36 ^
          (costly l + costly r +
            (if CheapP2 kl_u kl_v kr_u kr_v l r
             then 0
             else 1))

      by_cases hcheapR :
          AllKTwo kl_u kl_v kr_u kr_v ∧ Light r

      · have hcheap :
            CheapP2 kl_u kl_v kr_u kr_v l r := by

          exact
            ⟨hcheapR.1, Or.inr hcheapR.2⟩

        rw [
          if_pos hcheapR,
          if_pos hcheap
        ]

        simp only [add_zero]

        calc
          bnd l ≤ 36 ^ (costly l) :=
            ihL

          _ ≤ 36 ^ (costly l + costly r) :=
            t4_pow_add_le
              (costly l)
              (costly r)

      · by_cases hcheapL :
            AllKTwo kl_u kl_v kr_u kr_v ∧ Light l

        · have hcheap :
              CheapP2 kl_u kl_v kr_u kr_v l r := by

            exact
              ⟨hcheapL.1, Or.inl hcheapL.2⟩

          rw [
            if_neg hcheapR,
            if_pos hcheapL,
            if_pos hcheap
          ]

          simp only [add_zero]

          calc
            bnd r ≤ 36 ^ (costly r) :=
              ihR

            _ ≤ 36 ^ (costly r + costly l) :=
              t4_pow_add_le
                (costly r)
                (costly l)

            _ = 36 ^ (costly l + costly r) := by
                  rw [Nat.add_comm (costly r) (costly l)]

        · have hnotCheap :
              ¬ CheapP2
                  kl_u kl_v kr_u kr_v l r := by

            intro hcheap

            rcases hcheap with
              ⟨hall, hlight⟩

            rcases hlight with hl | hr

            · exact hcheapL ⟨hall, hl⟩

            · exact hcheapR ⟨hall, hr⟩

          rw [
            if_neg hcheapR,
            if_neg hcheapL,
            if_neg hnotCheap
          ]

          have hmul :
              bnd l * bnd r ≤
                36 ^ (costly l) *
                36 ^ (costly r) :=
            t4_mul_mono ihL ihR

          calc
            18 * (bnd l + bnd r)
                ≤
              36 * (bnd l * bnd r) :=
                t4_P2_arith
                  (bnd l)
                  (bnd r)
                  hpL
                  hpR

            _ ≤
              36 *
                (36 ^ (costly l) *
                 36 ^ (costly r)) := by

                  exact
                    Nat.mul_le_mul_left 36 hmul

            _ =
              36 ^ (costly l + costly r + 1) := by

                  rw [pow_add, pow_succ]

                  ring

  | P3 l c r =>

      have ihL :
          bnd l ≤ 36 ^ (costly l) :=
        T4_2 l

      have ihC :
          bnd c ≤ 36 ^ (costly c) :=
        T4_2 c

      have ihR :
          bnd r ≤ 36 ^ (costly r) :=
        T4_2 r

      have hpL :
          1 ≤ bnd l :=
        (T4_0 l).2

      have hpC :
          1 ≤ bnd c :=
        (T4_0 c).2

      have hpR :
          1 ≤ bnd r :=
        (T4_0 r).2

      have hmulLC :
          bnd l * bnd c ≤
            36 ^ (costly l) *
            36 ^ (costly c) :=
        t4_mul_mono ihL ihC

      have hmul :
          bnd l * bnd c * bnd r ≤
            36 ^ (costly l) *
              36 ^ (costly c) *
              36 ^ (costly r) :=
        t4_mul_mono hmulLC ihR

      change
        6 * (bnd l + bnd c + bnd r) ≤
          36 ^ (costly l + costly c + costly r + 1)

      calc
        6 * (bnd l + bnd c + bnd r)
            ≤
          36 * (bnd l * bnd c * bnd r) :=
            t4_P3_arith
              (bnd l)
              (bnd c)
              (bnd r)
              hpL
              hpC
              hpR

        _ ≤
          36 *
            (36 ^ (costly l) *
             36 ^ (costly c) *
             36 ^ (costly r)) := by

              exact
                Nat.mul_le_mul_left 36 hmul

        _ =
          36 ^ (costly l + costly c + costly r + 1) := by

              rw [pow_add, pow_add, pow_succ]

              ring

private theorem t4_bndList_exp
    (ts : List SPTree) :
    bndList ts ≤ 36 ^ (costlyList ts) := by

  cases ts with

  | nil =>

      norm_num [bndList, costlyList]

  | cons t ts =>

      have ihT :
          bnd t ≤ 36 ^ (costly t) :=
        T4_2 t

      have ihTs :
          bndList ts ≤
            36 ^ (costlyList ts) :=
        t4_bndList_exp ts

      change
        bnd t * bndList ts ≤
          36 ^ (costly t + costlyList ts)

      calc
        bnd t * bndList ts
            ≤
          36 ^ (costly t) *
            36 ^ (costlyList ts) :=
              t4_mul_mono ihT ihTs

        _ = 36 ^ (costly t + costlyList ts) := by
              rw [pow_add]

end

/-! ## 52. T4.3 — Corollario globale -/

/--
T4.3.

Il numero di componenti con passo 2
della semantica di un albero ben formato
è al massimo esponenziale nel numero
dei suoi nodi costosi.
-/
theorem T4_3
    (t : SPTree)
    (hwf : WF t) :
    pieces2 (Sigma t) ≤
      36 ^ (costly t) := by

  exact
    (T4_1 t hwf).trans
      (T4_2 t)

/-! ## 53. Controllo degli assiomi della tappa 4 -/

#print axioms T4_0
#print axioms T4_1
#print axioms T4_2
#print axioms T4_3

/-!
## Tappa 5 — Numero di P-nodi pesanti

T5.0: Light t → costly t = 0 ∧ heavyP t = 0.
T5.1: costly t ≤ 2 * heavyP t.
T5.2: WF t → pieces2 (Sigma t) ≤ 36 ^ (2 * heavyP t).

La dimostrazione di T5.1 utilizza la proprietà più forte:

  ¬ Light t → costly t + 1 ≤ 2 * heavyP t.

Per le liste si dimostra:

  costlyList ts + heavyCount ts ≤ 2 * heavyPList ts,

dove heavyCount conta le occorrenze di figli non leggeri.

Non vengono introdotti nuovi assiomi.
-/

/-! ## 54. Numero di P-nodi pesanti -/

mutual

noncomputable def heavyP : SPTree → ℕ
  | .Q _ =>
      0

  | .S children =>
      heavyPList children

  | .P2 kl_u kl_v kr_u kr_v l r =>
      by
        classical
        exact
          heavyP l + heavyP r +
            (if AllKTwo kl_u kl_v kr_u kr_v
             then 0
             else 1)

  | .P3 l c r =>
      heavyP l + heavyP c + heavyP r + 1

noncomputable def heavyPList : List SPTree → ℕ
  | [] =>
      0

  | t :: ts =>
      heavyP t + heavyPList ts

end

/-! ## 55. Numero di figli non leggeri -/

/--
heavyCount conta le occorrenze di sottoalberi
non leggeri in una lista.

La definizione coincide con il filtro utilizzato
da HasTwoHeavy nella tappa 4.
-/
private noncomputable def heavyCount
    (ts : List SPTree) : ℕ := by
  classical
  exact
    (ts.filter
      (fun t => decide (¬ Light t))).length

private theorem heavyCount_nil :
    heavyCount [] = 0 := by
  simp [heavyCount]

private theorem heavyCount_cons
    (t : SPTree)
    (ts : List SPTree) :
    heavyCount (t :: ts) =
      (if Light t then 0 else 1) +
        heavyCount ts := by

  classical

  by_cases ht : Light t

  · simp [heavyCount, ht]

  · simp [heavyCount, ht]
    omega

/--
HasTwoHeavy equivale ad avere almeno due
occorrenze di figli non leggeri.
-/
private theorem t5_HasTwoHeavy_iff
    (ts : List SPTree) :
    HasTwoHeavy ts ↔
      2 ≤ heavyCount ts := by

  classical

  unfold HasTwoHeavy heavyCount

  rfl

/--
Una lista è leggera se e solo se non contiene
alcun figlio non leggero.
-/
private theorem t5_LightList_iff_count_zero
    (ts : List SPTree) :
    LightList ts ↔
      heavyCount ts = 0 := by

  induction ts with

  | nil =>

      simp [LightList, heavyCount]

  | cons t ts ih =>

      change
        (Light t ∧ LightList ts) ↔
          heavyCount (t :: ts) = 0

      rw [heavyCount_cons]

      by_cases ht : Light t

      · simpa [ht] using ih

      · simp [ht]

/--
Se una lista non è leggera, contiene almeno
un figlio non leggero.
-/
private theorem t5_count_pos
    (ts : List SPTree)
    (h : ¬ LightList ts) :
    1 ≤ heavyCount ts := by

  by_contra hn

  have hz :
      heavyCount ts = 0 := by
    omega

  exact
    h ((t5_LightList_iff_count_zero ts).mpr hz)

/-! ## 56. T5.0 — Costo nullo degli alberi leggeri -/

/-
La dimostrazione è simultanea sugli alberi
e sulle liste di figli.
-/
mutual

theorem T5_0
    (t : SPTree)
    (hlight : Light t) :
    costly t = 0 ∧ heavyP t = 0 := by

  cases t with

  | Q len =>

      exact ⟨rfl, rfl⟩

  | S children =>

      have hs :=
        t5_lightList_zero children hlight

      have hcount :
          heavyCount children = 0 :=
        (t5_LightList_iff_count_zero children).mp
          hlight

      have hnot :
          ¬ HasTwoHeavy children := by

        intro hh

        have htwo :
            2 ≤ heavyCount children :=
          (t5_HasTwoHeavy_iff children).mp hh

        omega

      change
        (costlyList children +
          (if HasTwoHeavy children then 1 else 0) = 0) ∧
        heavyPList children = 0

      rw [if_neg hnot]

      simpa using hs

  | P2 kl_u kl_v kr_u kr_v l r =>

      rcases hlight with
        ⟨hku, hkv, hru, hrv, hl, hr⟩

      have ihL := T5_0 l hl
      have ihR := T5_0 r hr

      have hall :
          AllKTwo kl_u kl_v kr_u kr_v :=
        ⟨hku, hkv, hru, hrv⟩

      have hcheap :
          CheapP2 kl_u kl_v kr_u kr_v l r :=
        ⟨hall, Or.inl hl⟩

      change
        (costly l + costly r +
          (if CheapP2 kl_u kl_v kr_u kr_v l r
           then 0
           else 1) = 0) ∧
        (heavyP l + heavyP r +
          (if AllKTwo kl_u kl_v kr_u kr_v
           then 0
           else 1) = 0)

      simp [
        hcheap,
        hall,
        ihL.1,
        ihL.2,
        ihR.1,
        ihR.2
      ]

  | P3 l c r =>

      exact False.elim hlight

private theorem t5_lightList_zero
    (ts : List SPTree)
    (hlight : LightList ts) :
    costlyList ts = 0 ∧
      heavyPList ts = 0 := by

  cases ts with

  | nil =>

      exact ⟨rfl, rfl⟩

  | cons t ts =>

      rcases hlight with ⟨ht, hts⟩

      have ihT := T5_0 t ht

      have ihTs :=
        t5_lightList_zero ts hts

      change
        (costly t + costlyList ts = 0) ∧
        (heavyP t + heavyPList ts = 0)

      omega

end

/-! ## 57. Lemma strutturale per i P2 -/

/--
Se tutti i coefficienti sono 2 e i due figli
sono leggeri, anche il P2 è leggero.
-/
private theorem t5_P2_light
    (kl_u kl_v kr_u kr_v : ℤ)
    (l r : SPTree)
    (hall :
      AllKTwo kl_u kl_v kr_u kr_v)
    (hl : Light l)
    (hr : Light r) :
    Light (.P2 kl_u kl_v kr_u kr_v l r) := by

  rcases hall with
    ⟨hku, hkv, hru, hrv⟩

  exact ⟨hku, hkv, hru, hrv, hl, hr⟩

/-! ## 58. Lemma forte per T5.1 -/

/-
Dimostrazione simultanea delle proprietà:

Alberi:
  costly t ≤ 2 * heavyP t
  ¬ Light t → costly t + 1 ≤ 2 * heavyP t

Liste:
  costlyList ts + heavyCount ts ≤
    2 * heavyPList ts

La seconda proprietà degli alberi fornisce
un'unità di margine per ogni sottoalbero
non leggero.

Nei nodi S, un costo aggiuntivo richiede
almeno due figli non leggeri.

Nei P2 con tutti i k uguali a 2, un costo
aggiuntivo richiede due figli non leggeri.

I P2 con qualche k diverso da 2 e i P3
incrementano direttamente heavyP.
-/
mutual

private theorem t5_tree_budget
    (t : SPTree) :
    (costly t ≤ 2 * heavyP t) ∧
    (¬ Light t →
      costly t + 1 ≤ 2 * heavyP t) := by

  cases t with

  | Q len =>

      constructor

      · norm_num [costly, heavyP]

      · intro hn

        exfalso

        apply hn

        trivial

  | S children =>

      have hlist :
          costlyList children +
            heavyCount children ≤
          2 * heavyPList children :=
        t5_list_budget children

      constructor

      · change
          costlyList children +
            (if HasTwoHeavy children then 1 else 0) ≤
          2 * heavyPList children

        by_cases hh : HasTwoHeavy children

        · have htwo :
              2 ≤ heavyCount children :=
            (t5_HasTwoHeavy_iff children).mp hh

          rw [if_pos hh]

          omega

        · rw [if_neg hh]

          omega

      · intro hn

        have hnot :
            ¬ LightList children := hn

        have hcount :
            1 ≤ heavyCount children :=
          t5_count_pos children hnot

        change
          costlyList children +
            (if HasTwoHeavy children then 1 else 0) +
            1 ≤
          2 * heavyPList children

        by_cases hh : HasTwoHeavy children

        · have htwo :
              2 ≤ heavyCount children :=
            (t5_HasTwoHeavy_iff children).mp hh

          rw [if_pos hh]

          omega

        · rw [if_neg hh]

          omega

  | P2 kl_u kl_v kr_u kr_v l r =>

      have ihL := t5_tree_budget l
      have ihR := t5_tree_budget r

      have hweakL :
          costly l ≤ 2 * heavyP l :=
        ihL.1

      have hweakR :
          costly r ≤ 2 * heavyP r :=
        ihR.1

      have hcost :
          costly (.P2 kl_u kl_v kr_u kr_v l r) =
            costly l + costly r +
              (if CheapP2 kl_u kl_v kr_u kr_v l r
               then 0
               else 1) := rfl

      have hheavy :
          heavyP (.P2 kl_u kl_v kr_u kr_v l r) =
            heavyP l + heavyP r +
              (if AllKTwo kl_u kl_v kr_u kr_v
               then 0
               else 1) := rfl

      constructor

      · rw [hcost, hheavy]

        by_cases hcheap :
            CheapP2 kl_u kl_v kr_u kr_v l r

        · have hall :
              AllKTwo kl_u kl_v kr_u kr_v :=
            hcheap.1

          rw [
            if_pos hcheap,
            if_pos hall
          ]

          omega

        · by_cases hall :
              AllKTwo kl_u kl_v kr_u kr_v

          · have hnotL :
                ¬ Light l := by

              intro hl

              apply hcheap

              exact ⟨hall, Or.inl hl⟩

            have hnotR :
                ¬ Light r := by

              intro hr

              apply hcheap

              exact ⟨hall, Or.inr hr⟩

            have hstrongL :=
              ihL.2 hnotL

            have hstrongR :=
              ihR.2 hnotR

            rw [
              if_neg hcheap,
              if_pos hall
            ]

            omega

          · rw [
              if_neg hcheap,
              if_neg hall
            ]

            omega

      · intro hn

        rw [hcost, hheavy]

        by_cases hcheap :
            CheapP2 kl_u kl_v kr_u kr_v l r

        · have hall :
              AllKTwo kl_u kl_v kr_u kr_v :=
            hcheap.1

          rw [
            if_pos hcheap,
            if_pos hall
          ]

          rcases hcheap.2 with hl | hr

          · have hnotR :
                ¬ Light r := by

              intro hr

              apply hn

              exact
                t5_P2_light
                  kl_u kl_v kr_u kr_v
                  l r hall hl hr

            have hstrongR :=
              ihR.2 hnotR

            omega

          · have hnotL :
                ¬ Light l := by

              intro hl

              apply hn

              exact
                t5_P2_light
                  kl_u kl_v kr_u kr_v
                  l r hall hl hr

            have hstrongL :=
              ihL.2 hnotL

            omega

        · by_cases hall :
              AllKTwo kl_u kl_v kr_u kr_v

          · have hnotL :
                ¬ Light l := by

              intro hl

              apply hcheap

              exact ⟨hall, Or.inl hl⟩

            have hnotR :
                ¬ Light r := by

              intro hr

              apply hcheap

              exact ⟨hall, Or.inr hr⟩

            have hstrongL :=
              ihL.2 hnotL

            have hstrongR :=
              ihR.2 hnotR

            rw [
              if_neg hcheap,
              if_pos hall
            ]

            omega

          · rw [
              if_neg hcheap,
              if_neg hall
            ]

            omega

  | P3 l c r =>

      have ihL := t5_tree_budget l
      have ihC := t5_tree_budget c
      have ihR := t5_tree_budget r

      have hL :
          costly l ≤ 2 * heavyP l :=
        ihL.1

      have hC :
          costly c ≤ 2 * heavyP c :=
        ihC.1

      have hR :
          costly r ≤ 2 * heavyP r :=
        ihR.1

      constructor

      · change
          costly l + costly c + costly r + 1 ≤
            2 * (heavyP l + heavyP c + heavyP r + 1)

        omega

      · intro _

        change
          costly l + costly c + costly r + 1 + 1 ≤
            2 * (heavyP l + heavyP c + heavyP r + 1)

        omega

private theorem t5_list_budget
    (ts : List SPTree) :
    costlyList ts + heavyCount ts ≤
      2 * heavyPList ts := by

  cases ts with

  | nil =>

      simp [
        costlyList,
        heavyPList,
        heavyCount
      ]

  | cons t ts =>

      have ihT := t5_tree_budget t

      have ihTs :
          costlyList ts + heavyCount ts ≤
            2 * heavyPList ts :=
        t5_list_budget ts

      have hweak :
          costly t ≤ 2 * heavyP t :=
        ihT.1

      change
        costly t + costlyList ts +
          heavyCount (t :: ts) ≤
        2 * (heavyP t + heavyPList ts)

      rw [heavyCount_cons]

      by_cases ht : Light t

      · rw [if_pos ht]

        omega

      · rw [if_neg ht]

        have hstrong :
            costly t + 1 ≤ 2 * heavyP t :=
          ihT.2 ht

        omega

end

/-! ## 59. T5.1 — Costo versus P-nodi pesanti -/

/--
T5.1.

Il numero complessivo di nodi costosi
è al massimo il doppio del numero
di P-nodi pesanti.
-/
theorem T5_1
    (t : SPTree) :
    costly t ≤ 2 * heavyP t := by

  exact (t5_tree_budget t).1

/--
Versione forte utilizzata nella dimostrazione
di T5.1.

Ogni albero non leggero lascia almeno
un'unità di margine nel bound.
-/
theorem T5_1_strong
    (t : SPTree)
    (h : ¬ Light t) :
    costly t + 1 ≤ 2 * heavyP t := by

  exact (t5_tree_budget t).2 h

/-! ## 60. Monotonia della potenza di 36 -/

/--
Se a ≤ b, allora 36^a ≤ 36^b.

La dimostrazione utilizza t4_pow_add_le
della tappa 4.
-/
private theorem t5_pow_mono
    (a b : ℕ)
    (hab : a ≤ b) :
    (36 : ℕ) ^ a ≤ 36 ^ b := by

  have heq :
      a + (b - a) = b := by
    omega

  calc
    (36 : ℕ) ^ a
        ≤ 36 ^ (a + (b - a)) :=
          t4_pow_add_le a (b - a)

    _ = 36 ^ b := by
          rw [heq]

/-! ## 61. T5.2 — Bound globale tramite heavyP -/

/--
T5.2.

Per ogni albero ben formato, il numero di pezzi
di Sigma è al massimo 36^(2*heavyP).

La dimostrazione combina:
- T4.3: pieces2 (Sigma t) ≤ 36^(costly t);
- T5.1: costly t ≤ 2*heavyP t;
- monotonia della funzione n ↦ 36^n.
-/
theorem T5_2
    (t : SPTree)
    (hwf : WF t) :
    pieces2 (Sigma t) ≤
      36 ^ (2 * heavyP t) := by

  calc
    pieces2 (Sigma t)
        ≤ 36 ^ (costly t) :=
          T4_3 t hwf

    _ ≤ 36 ^ (2 * heavyP t) :=
          t5_pow_mono
            (costly t)
            (2 * heavyP t)
            (T5_1 t)

/-! ## 62. Controllo degli assiomi della tappa 5 -/

#print axioms T5_0
#print axioms T5_1
#print axioms T5_2

/-!
## Tappa 6a — Algoritmo calcolabile a radice fissata

Correzioni:
- ivCanon_length usa Finset.length_sort con la firma attuale.
- Lemma ausiliario ivCanon_normal per evitare unfolding
  ripetuti e costosi della rappresentazione canonica.
- Le prove di normalità di shift, union, inter e mink
  usano direttamente ivCanon_normal.
- Le prove di correttezza usano denote_canon invece di
  espandere ricorsivamente ivPoints su liste simboliche.
- Configurazioni angolari enumerate tramite liste esplicite.
- Test computabili mediante Bool.
- Nessuna modifica alle definizioni delle tappe precedenti.

Non vengono introdotti nuovi assiomi.
-/

/-! ## 63. Intervalli e loro semantica -/

abbrev IvList := List (ℤ × ℤ)

private def ivRun (a b : ℤ) : Finset ℤ :=
  (Finset.Icc a b).filter
    (fun z => decide ((z - a) % 2 = 0))

private theorem mem_ivRun
    (a b z : ℤ) :
    z ∈ ivRun a b ↔
      a ≤ z ∧ z ≤ b ∧ (z - a) % 2 = 0 := by

  simp only [
    ivRun,
    Finset.mem_filter,
    Finset.mem_Icc,
    decide_eq_true_eq
  ]

  exact and_assoc

private def ivPoints : IvList → Finset ℤ
  | [] => ∅
  | p :: ps =>
      ivRun p.1 p.2 ∪ ivPoints ps

def denote (L : IvList) : Set ℤ :=
  {z | z ∈ ivPoints L}

private theorem ivPoints_mem
    (L : IvList)
    (z : ℤ) :
    z ∈ ivPoints L ↔
      ∃ p ∈ L, z ∈ ivRun p.1 p.2 := by

  induction L with

  | nil =>
      simp [ivPoints]

  | cons p ps ih =>
      constructor

      · intro hz

        change
          z ∈ ivRun p.1 p.2 ∪ ivPoints ps
          at hz

        rcases Finset.mem_union.mp hz with hp | hs

        · exact ⟨p, List.mem_cons_self, hp⟩

        · obtain ⟨q, hq, hzq⟩ := ih.mp hs

          exact
            ⟨q, List.mem_cons_of_mem _ hq, hzq⟩

      · rintro ⟨q, hq, hzq⟩

        rcases List.mem_cons.mp hq with heq | htail

        · subst q

          exact Finset.mem_union.mpr (Or.inl hzq)

        · exact Finset.mem_union.mpr
            (Or.inr (ih.mpr ⟨q, htail, hzq⟩))

/-! ## 64. Continuità di un run -/

private def ivGood
    (F : Finset ℤ)
    (a b : ℤ) : Prop :=
  ∀ z ∈ Finset.Icc a b,
    (z - a) % 2 = 0 → z ∈ F

private def ivGoodB
    (F : Finset ℤ)
    (a b : ℤ) : Bool :=
  decide
    (((Finset.Icc a b).filter
      (fun z => decide ((z - a) % 2 = 0))) ⊆ F)

private theorem ivGoodB_iff
    (F : Finset ℤ)
    (a b : ℤ) :
    ivGoodB F a b = true ↔
      ivGood F a b := by

  simp only [
    ivGoodB,
    decide_eq_true_eq
  ]

  constructor

  · intro h z hz hp

    apply h

    apply Finset.mem_filter.mpr

    exact ⟨hz, by simpa using hp⟩

  · intro h z hz

    obtain ⟨hzI, hzP⟩ :=
      Finset.mem_filter.mp hz

    apply h z hzI

    simpa using hzP

private theorem ivGood_refl
    (F : Finset ℤ)
    (a : ℤ)
    (ha : a ∈ F) :
    ivGood F a a := by

  intro z hz _

  have hbounds := Finset.mem_Icc.mp hz

  have heq : z = a := by
    omega

  simpa [heq] using ha

private theorem ivGood_apply
    (F : Finset ℤ)
    (a b z : ℤ)
    (h : ivGood F a b)
    (hz : z ∈ ivRun a b) :
    z ∈ F := by

  rcases (mem_ivRun a b z).mp hz with
    ⟨hlo, hhi, hpar⟩

  exact
    h z
      (Finset.mem_Icc.mpr ⟨hlo, hhi⟩)
      hpar

/-! ## 65. Estremo destro di un run -/

private def ivRightCandidates
    (F : Finset ℤ)
    (a : ℤ) : Finset ℤ :=
  insert a
    (F.filter
      (fun b =>
        decide (a ≤ b) &&
        decide ((b - a) % 2 = 0) &&
        ivGoodB F a b))

private theorem mem_ivRightCandidates
    (F : Finset ℤ)
    (a b : ℤ) :
    b ∈ ivRightCandidates F a ↔
      b = a ∨
        (b ∈ F ∧
         a ≤ b ∧
         (b - a) % 2 = 0 ∧
         ivGood F a b) := by

  simp only [
    ivRightCandidates,
    Finset.mem_insert,
    Finset.mem_filter,
    Bool.and_eq_true,
    decide_eq_true_eq,
    ivGoodB_iff,
    and_assoc
  ]

private def ivEnd
    (F : Finset ℤ)
    (a : ℤ) : ℤ :=
  (ivRightCandidates F a).max'
    ⟨a, Finset.mem_insert_self a _⟩

private theorem ivEnd_spec
    (F : Finset ℤ)
    (a : ℤ)
    (ha : a ∈ F) :
    a ≤ ivEnd F a ∧
    (ivEnd F a - a) % 2 = 0 ∧
    ivGood F a (ivEnd F a) := by

  have hm :
      ivEnd F a ∈ ivRightCandidates F a :=
    Finset.max'_mem _ _

  rcases
      (mem_ivRightCandidates F a (ivEnd F a)).mp hm
    with heq | hf

  · rw [heq]

    exact ⟨
      le_refl a,
      by norm_num,
      ivGood_refl F a ha
    ⟩

  · exact ⟨hf.2.1, hf.2.2.1, hf.2.2.2⟩

private theorem ivEnd_le
    (F : Finset ℤ)
    (a b : ℤ)
    (hb : b ∈ ivRightCandidates F a) :
    b ≤ ivEnd F a := by

  exact Finset.le_max' _ b hb

/-! ## 66. Inizi dei run -/

private def ivStarts (F : Finset ℤ) : Finset ℤ :=
  F.filter
    (fun a => !(decide (a - 2 ∈ F)))

private theorem mem_ivStarts
    (F : Finset ℤ)
    (a : ℤ) :
    a ∈ ivStarts F ↔
      a ∈ F ∧ a - 2 ∉ F := by

  simp [ivStarts]

/-! ## 67. Costruzione canonica -/

private def ivCanon
    (F : Finset ℤ) : IvList :=
  ((ivStarts F).sort
    (fun x y => decide (x ≤ y))).map
      (fun a => (a, ivEnd F a))

private theorem ivCanon_length
    (F : Finset ℤ) :
    (ivCanon F).length =
      (ivStarts F).card := by

  unfold ivCanon

  rw [List.length_map]

  exact Finset.length_sort _

/-! ## 68. Ricerca dell'inizio -/

private def ivLeftCandidates
    (F : Finset ℤ)
    (z : ℤ) : Finset ℤ :=
  insert z
    (F.filter
      (fun a =>
        decide (a ≤ z) &&
        decide ((z - a) % 2 = 0) &&
        ivGoodB F a z))

private theorem mem_ivLeftCandidates
    (F : Finset ℤ)
    (z a : ℤ) :
    a ∈ ivLeftCandidates F z ↔
      a = z ∨
        (a ∈ F ∧
         a ≤ z ∧
         (z - a) % 2 = 0 ∧
         ivGood F a z) := by

  simp only [
    ivLeftCandidates,
    Finset.mem_insert,
    Finset.mem_filter,
    Bool.and_eq_true,
    decide_eq_true_eq,
    ivGoodB_iff,
    and_assoc
  ]

private def ivLeft
    (F : Finset ℤ)
    (z : ℤ) : ℤ :=
  (ivLeftCandidates F z).min'
    ⟨z, Finset.mem_insert_self z _⟩

private theorem ivLeft_spec
    (F : Finset ℤ)
    (z : ℤ)
    (hz : z ∈ F) :
    ivLeft F z ∈ F ∧
    ivLeft F z ≤ z ∧
    (z - ivLeft F z) % 2 = 0 ∧
    ivGood F (ivLeft F z) z := by

  have hm :
      ivLeft F z ∈ ivLeftCandidates F z :=
    Finset.min'_mem _ _

  rcases
      (mem_ivLeftCandidates F z (ivLeft F z)).mp hm
    with heq | hf

  · rw [heq]

    exact ⟨
      hz,
      le_refl z,
      by norm_num,
      ivGood_refl F z hz
    ⟩

  · exact hf

private theorem ivGood_extend_left
    (F : Finset ℤ)
    (a z : ℤ)
    (hgood : ivGood F a z)
    (hpar : (z - a) % 2 = 0)
    (ha : a - 2 ∈ F) :
    ivGood F (a - 2) z := by

  intro x hx hxpar

  have hbounds := Finset.mem_Icc.mp hx

  by_cases heq : x = a - 2

  · simpa [heq] using ha

  · have hxa : a ≤ x := by
      omega

    have hxz : x ≤ z := hbounds.2

    have hpar' :
        (x - a) % 2 = 0 := by
      omega

    exact
      hgood x
        (Finset.mem_Icc.mpr ⟨hxa, hxz⟩)
        hpar'

private theorem ivLeft_start
    (F : Finset ℤ)
    (z : ℤ)
    (hz : z ∈ F) :
    ivLeft F z ∈ ivStarts F := by

  let a := ivLeft F z

  obtain ⟨ha, haz, hpar, hgood⟩ :=
    ivLeft_spec F z hz

  apply (mem_ivStarts F a).mpr

  constructor

  · exact ha

  · intro hprev

    have hgood' :
        ivGood F (a - 2) z :=
      ivGood_extend_left
        F a z hgood hpar hprev

    have hpar' :
        (z - (a - 2)) % 2 = 0 := by
      omega

    have hc :
        a - 2 ∈ ivLeftCandidates F z := by

      apply
        (mem_ivLeftCandidates F z (a - 2)).mpr

      right

      exact ⟨
        hprev,
        by omega,
        hpar',
        hgood'
      ⟩

    have hmin :
        a ≤ a - 2 := by

      exact
        Finset.min'_le
          (ivLeftCandidates F z)
          (a - 2)
          hc

    omega

private theorem ivLeft_le_end
    (F : Finset ℤ)
    (z : ℤ)
    (hz : z ∈ F) :
    z ≤ ivEnd F (ivLeft F z) := by

  obtain ⟨ha, haz, hpar, hgood⟩ :=
    ivLeft_spec F z hz

  have hc :
      z ∈ ivRightCandidates F (ivLeft F z) := by

    apply
      (mem_ivRightCandidates F (ivLeft F z) z).mpr

    right

    exact ⟨
      hz,
      haz,
      hpar,
      hgood
    ⟩

  exact
    ivEnd_le F (ivLeft F z) z hc

/-! ## 69. Correttezza della costruzione canonica -/

private theorem ivCanon_mem
    (F : Finset ℤ)
    (a : ℤ)
    (ha : a ∈ ivStarts F) :
    (a, ivEnd F a) ∈ ivCanon F := by

  unfold ivCanon

  apply List.mem_map.mpr

  refine ⟨a, ?_, rfl⟩

  simpa only [Finset.mem_sort] using ha

private theorem ivCanon_subset
    (F : Finset ℤ)
    (z : ℤ)
    (hz : z ∈ ivPoints (ivCanon F)) :
    z ∈ F := by

  obtain ⟨p, hp, hzp⟩ :=
    (ivPoints_mem (ivCanon F) z).mp hz

  unfold ivCanon at hp

  obtain ⟨a, ha, heq⟩ :=
    List.mem_map.mp hp

  have haF :
      a ∈ F := by

    have has :
        a ∈ ivStarts F := by
      simpa only [Finset.mem_sort] using ha

    exact (mem_ivStarts F a).mp has |>.1

  have hpEq :
      p = (a, ivEnd F a) :=
    heq.symm

  rw [hpEq] at hzp

  have hgood :=
    (ivEnd_spec F a haF).2.2

  exact
    ivGood_apply F a (ivEnd F a) z
      hgood hzp

private theorem ivCanon_superset
    (F : Finset ℤ)
    (z : ℤ)
    (hz : z ∈ F) :
    z ∈ ivPoints (ivCanon F) := by

  let a := ivLeft F z

  have ha :
      a ∈ ivStarts F :=
    ivLeft_start F z hz

  have haz :
      a ≤ z :=
    (ivLeft_spec F z hz).2.1

  have hpar :
      (z - a) % 2 = 0 :=
    (ivLeft_spec F z hz).2.2.1

  have hze :
      z ≤ ivEnd F a :=
    ivLeft_le_end F z hz

  apply (ivPoints_mem (ivCanon F) z).mpr

  refine ⟨
    (a, ivEnd F a),
    ivCanon_mem F a ha,
    ?_
  ⟩

  apply (mem_ivRun a (ivEnd F a) z).mpr

  exact ⟨haz, hze, hpar⟩

private theorem ivPoints_canon
    (F : Finset ℤ) :
    ivPoints (ivCanon F) = F := by

  ext z

  constructor

  · exact ivCanon_subset F z

  · exact ivCanon_superset F z

private theorem denote_canon
    (F : Finset ℤ) :
    denote (ivCanon F) = (↑F : Set ℤ) := by

  ext z

  change
    z ∈ ivPoints (ivCanon F) ↔
      z ∈ F

  rw [ivPoints_canon]

/-! ## 70. Normalizzazione -/

def Normal (L : IvList) : Prop :=
  L = ivCanon (ivPoints L)

/--
Lemma ausiliario: ogni lista prodotta da ivCanon
è normale.

La prova opera sul Finset simbolico F, senza
espandere ivCanon su espressioni complesse.
-/
private theorem ivCanon_normal
    (F : Finset ℤ) :
    Normal (ivCanon F) := by

  unfold Normal

  rw [ivPoints_canon]

def normalize (L : IvList) : IvList :=
  ivCanon (ivPoints L)

private theorem normalize_correct
    (L : IvList) :
    denote (normalize L) = denote L := by

  unfold normalize

  rw [denote_canon]

  rfl

private theorem normalize_normal
    (L : IvList) :
    Normal (normalize L) := by

  unfold normalize

  exact ivCanon_normal (ivPoints L)

/-! ## 71. Lunghezza e numero di pezzi -/

private theorem pieces2_finset
    (F : Finset ℤ) :
    pieces2 (↑F : Set ℤ) =
      (ivStarts F).card := by

  have hset :
      {z : ℤ |
        z ∈ (↑F : Set ℤ) ∧
        z - 2 ∉ (↑F : Set ℤ)} =
      (↑(ivStarts F) : Set ℤ) := by

    ext z

    simp [ivStarts]

  unfold pieces2

  rw [hset]

  exact Set.ncard_coe_finset _

private theorem canon_length_pieces
    (F : Finset ℤ) :
    (ivCanon F).length =
      pieces2 (denote (ivCanon F)) := by

  rw [ivCanon_length]

  rw [denote_canon]

  exact (pieces2_finset F).symm

private theorem Normal_length_pieces
    (L : IvList)
    (hL : Normal L) :
    L.length = pieces2 (denote L) := by

  have heq :
      L = ivCanon (ivPoints L) := hL

  calc
    L.length
        = (ivCanon (ivPoints L)).length :=
          congrArg List.length heq

    _ = (ivStarts (ivPoints L)).card :=
          ivCanon_length (ivPoints L)

    _ = pieces2 (denote L) := by
          change
            (ivStarts (ivPoints L)).card =
              pieces2 (↑(ivPoints L) : Set ℤ)

          exact
            (pieces2_finset (ivPoints L)).symm

/-! ## 72. Operazione shift -/

def shift (L : IvList) (d : ℤ) : IvList :=
  ivCanon
    ((ivPoints L).image (fun x => x + d))

private theorem shift_correct
    (L : IvList)
    (d : ℤ) :
    denote (shift L d) =
      shiftSet (denote L) d := by

  unfold shift

  rw [denote_canon]

  ext z

  constructor

  · intro hz

    obtain ⟨x, hx, heq⟩ :=
      Finset.mem_image.mp hz

    have h :
        z - d = x := by
      omega

    change z - d ∈ ivPoints L

    rw [h]

    exact hx

  · intro hz

    apply Finset.mem_image.mpr

    refine ⟨z - d, hz, ?_⟩

    omega

private theorem shift_normal
    (L : IvList)
    (d : ℤ) :
    Normal (shift L d) := by

  unfold shift

  exact ivCanon_normal _

/-! ## 73. Operazione union -/

def union (L R : IvList) : IvList :=
  ivCanon (ivPoints L ∪ ivPoints R)

private theorem union_correct
    (L R : IvList) :
    denote (union L R) =
      denote L ∪ denote R := by

  unfold union

  rw [denote_canon]

  ext z

  simp only [
    Finset.mem_coe,
    Finset.mem_union,
    Set.mem_union,
    denote,
    Set.mem_setOf_eq
  ]

private theorem union_normal
    (L R : IvList) :
    Normal (union L R) := by

  unfold union

  exact ivCanon_normal _

/-! ## 74. Operazione inter -/

def inter (L R : IvList) : IvList :=
  ivCanon (ivPoints L ∩ ivPoints R)

private theorem inter_correct
    (L R : IvList) :
    denote (inter L R) =
      denote L ∩ denote R := by

  unfold inter

  rw [denote_canon]

  ext z

  simp only [
    Finset.mem_coe,
    Finset.mem_inter,
    Set.mem_inter_iff,
    denote,
    Set.mem_setOf_eq
  ]

private theorem inter_normal
    (L R : IvList) :
    Normal (inter L R) := by

  unfold inter

  exact ivCanon_normal _

/-! ## 75. Operazione mink -/

def mink (L R : IvList) : IvList :=
  ivCanon
    (((ivPoints L) ×ˢ (ivPoints R)).image
      (fun p => p.1 + p.2))

private theorem mink_correct
    (L R : IvList) :
    denote (mink L R) =
      Mink (denote L) (denote R) := by

  unfold mink

  rw [denote_canon]

  ext z

  constructor

  · intro hz

    obtain ⟨p, hp, heq⟩ :=
      Finset.mem_image.mp hz

    rcases p with ⟨a, b⟩

    have hab :=
      Finset.mem_product.mp hp

    exact ⟨a, hab.1, b, hab.2, heq.symm⟩

  · intro hz

    rcases hz with
      ⟨a, ha, b, hb, heq⟩

    apply Finset.mem_image.mpr

    exact
      ⟨(a, b),
        Finset.mem_product.mpr ⟨ha, hb⟩,
        heq.symm⟩

private theorem mink_normal
    (L R : IvList) :
    Normal (mink L R) := by

  unfold mink

  exact ivCanon_normal _

/-! ## 76. Unione di una lista di rappresentazioni -/

private def ivUnionMany : List IvList → IvList
  | [] => normalize []
  | L :: ls => union L (ivUnionMany ls)

private theorem ivUnionMany_correct
    (ls : List IvList)
    (z : ℤ) :
    z ∈ denote (ivUnionMany ls) ↔
      ∃ L ∈ ls, z ∈ denote L := by

  induction ls with

  | nil =>

      change
        z ∈ denote (normalize []) ↔
          ∃ L ∈ ([] : List IvList), z ∈ denote L

      rw [normalize_correct]

      constructor

      · intro hz

        have he :
            z ∈ (∅ : Finset ℤ) := hz

        exact False.elim
          ((Finset.notMem_empty z) he)

      · rintro ⟨L, hL, _⟩

        simp at hL

  | cons L ls ih =>

      change
        z ∈ denote
          (union L (ivUnionMany ls)) ↔
        ∃ R ∈ L :: ls, z ∈ denote R

      rw [union_correct]

      constructor

      · intro hz

        rcases hz with hL | hls

        · exact ⟨L, List.mem_cons_self, hL⟩

        · obtain ⟨R, hR, hzR⟩ := ih.mp hls

          exact
            ⟨R, List.mem_cons_of_mem _ hR, hzR⟩

      · rintro ⟨R, hR, hzR⟩

        rcases List.mem_cons.mp hR with heq | htail

        · subst R

          exact Or.inl hzR

        · exact Or.inr
            (ih.mpr ⟨R, htail, hzR⟩)

private theorem ivUnionMany_normal
    (ls : List IvList) :
    Normal (ivUnionMany ls) := by

  cases ls with

  | nil =>
      exact normalize_normal []

  | cons L ls =>
      exact union_normal L (ivUnionMany ls)

/-! ## 77. Semantica Q -/

private theorem ivRun_Band
    (n : ℕ) :
    (↑(ivRun
      (-(2 * (n : ℤ)))
      (2 * (n : ℤ))) : Set ℤ) =
      Band n := by

  ext z

  constructor

  · intro hz

    obtain ⟨hlo, hhi, hpar⟩ :=
      (mem_ivRun
        (-(2 * (n : ℤ)))
        (2 * (n : ℤ))
        z).mp hz

    have hdiv :
        2 ∣ z := by

      apply Int.dvd_of_emod_eq_zero

      omega

    obtain ⟨s, hs⟩ := hdiv

    refine ⟨s, ?_, ?_, ?_⟩

    · omega

    · omega

    · omega

  · intro hz

    rcases hz with
      ⟨s, hlo, hhi, heq⟩

    apply
      (mem_ivRun
        (-(2 * (n : ℤ)))
        (2 * (n : ℤ))
        z).mpr

    constructor

    · omega

    constructor

    · omega

    · omega

private theorem denote_singleton_zero :
    denote [(0, 0)] = ({0} : Set ℤ) := by

  ext z

  constructor

  · intro hz

    change
      z ∈ ivRun 0 0 ∪ (∅ : Finset ℤ)
      at hz

    rcases Finset.mem_union.mp hz with hz0 | he

    · have hbounds :=
        (mem_ivRun 0 0 z).mp hz0

      have heq : z = 0 := by
        omega

      exact heq

    · exact False.elim
        ((Finset.notMem_empty z) he)

  · intro hz

    have heq : z = 0 := by
      simpa using hz

    subst z

    change
      (0 : ℤ) ∈ ivRun 0 0 ∪ (∅ : Finset ℤ)

    apply Finset.mem_union.mpr

    apply Or.inl

    apply (mem_ivRun 0 0 0).mpr

    exact ⟨
      by omega,
      by omega,
      by norm_num
    ⟩

/-! ## 78. Configurazioni angolari computabili -/

def anglePairsL : List (ℤ × ℤ) :=
  [(1, 0), (0, 1), (1, 1)]

def angleConfigsL :
    List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  anglePairsL.flatMap
    (fun p => anglePairsL.map (fun q => (p, q)))

private theorem anglePairsL_mem
    (p : ℤ × ℤ) :
    p ∈ anglePairsL ↔
      p ∈ KeyLemma.alphaPairs := by

  simp only [
    anglePairsL,
    KeyLemma.alphaPairs,
    List.mem_cons,
    List.not_mem_nil,
    or_false,
    Finset.mem_insert,
    Finset.mem_singleton
  ]

private theorem angleConfigsL_mem
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) :
    uv ∈ angleConfigsL ↔
      uv ∈ t3AnglePairs := by

  constructor

  · intro huv

    obtain ⟨p, hp, hmap⟩ :=
      List.mem_flatMap.mp huv

    obtain ⟨q, hq, heq⟩ :=
      List.mem_map.mp hmap

    have hp' :
        p ∈ KeyLemma.alphaPairs :=
      (anglePairsL_mem p).mp hp

    have hq' :
        q ∈ KeyLemma.alphaPairs :=
      (anglePairsL_mem q).mp hq

    have huvEq :
        uv = (p, q) :=
      heq.symm

    rw [huvEq]

    exact Finset.mem_product.mpr ⟨hp', hq'⟩

  · intro huv

    have hp :
        uv.1 ∈ KeyLemma.alphaPairs ∧
        uv.2 ∈ KeyLemma.alphaPairs :=
      Finset.mem_product.mp huv

    unfold angleConfigsL

    apply List.mem_flatMap.mpr

    refine ⟨uv.1, ?_, ?_⟩

    · exact
        (anglePairsL_mem uv.1).mpr hp.1

    · apply List.mem_map.mpr

      refine ⟨uv.2, ?_, ?_⟩

      · exact
          (anglePairsL_mem uv.2).mpr hp.2

      · cases uv
        rfl

/-! ## 79. Condizione Degree4Angles booleana -/

private def degree4AnglesB
    (kl_u kl_v kr_u kr_v : ℤ)
    (lu ru lv rv : ℤ) : Bool :=

  (!(decide (kl_u = 1 ∨ kr_u = 1)) ||
    (decide (lu = 1) && decide (ru = 1))) &&

  (!(decide (kl_v = 1 ∨ kr_v = 1)) ||
    (decide (lv = 1) && decide (rv = 1)))

private theorem degree4AnglesB_iff
    (kl_u kl_v kr_u kr_v : ℤ)
    (lu ru lv rv : ℤ) :
    degree4AnglesB
      kl_u kl_v kr_u kr_v
      lu ru lv rv = true ↔
    Degree4Angles
      kl_u kl_v kr_u kr_v
      lu ru lv rv := by

  have aux :
      ∀ a b x y : ℤ,
        (!(decide (a = 1 ∨ b = 1)) ||
          (decide (x = 1) && decide (y = 1))) = true ↔
        ((a = 1 ∨ b = 1) → x = 1 ∧ y = 1) := by

    intro a b x y

    simp only [
      Bool.or_eq_true,
      Bool.not_eq_true',
      Bool.and_eq_true,
      decide_eq_true_eq,
      decide_eq_false_iff_not
    ]

    constructor

    · intro h hp

      rcases h with hn | hy

      · exact False.elim (hn hp)

      · exact hy

    · intro h

      by_cases hp : a = 1 ∨ b = 1

      · exact Or.inr (h hp)

      · exact Or.inl hp

  unfold degree4AnglesB Degree4Angles

  rw [Bool.and_eq_true]

  rw [
    aux kl_u kr_u lu ru,
    aux kl_v kr_v lv rv
  ]

/-! ## 80. Regola P2 per configurazione -/

private def ivP2Config
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) : IvList :=

  if degree4AnglesB
      kl_u kl_v kr_u kr_v
      uv.1.1 uv.1.2 uv.2.1 uv.2.2 = true then

    inter
      (shift L
        (-(kl_u * uv.1.1 +
           kl_v * uv.2.1)))
      (shift R
        (kr_u * uv.1.2 +
         kr_v * uv.2.2))

  else []

private theorem denote_empty :
    denote [] = (∅ : Set ℤ) := by

  ext z

  simp [denote, ivPoints]

private theorem ivP2Config_correct
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) :
    denote
      (ivP2Config
        kl_u kl_v kr_u kr_v L R uv) =
    t3P2Config
      kl_u kl_v kr_u kr_v
      (denote L) (denote R) uv := by

  by_cases hd :
      Degree4Angles
        kl_u kl_v kr_u kr_v
        uv.1.1 uv.1.2 uv.2.1 uv.2.2

  · have hdB :
        degree4AnglesB
          kl_u kl_v kr_u kr_v
          uv.1.1 uv.1.2 uv.2.1 uv.2.2 = true :=
      (degree4AnglesB_iff
        kl_u kl_v kr_u kr_v
        uv.1.1 uv.1.2 uv.2.1 uv.2.2).mpr hd

    simp only [
      ivP2Config,
      t3P2Config,
      if_pos hdB,
      if_pos hd,
      inter_correct,
      shift_correct
    ]

  · have hdB :
        degree4AnglesB
          kl_u kl_v kr_u kr_v
          uv.1.1 uv.1.2 uv.2.1 uv.2.2 ≠ true := by

      intro h

      exact hd
        ((degree4AnglesB_iff
          kl_u kl_v kr_u kr_v
          uv.1.1 uv.1.2 uv.2.1 uv.2.2).mp h)

    simp only [
      ivP2Config,
      t3P2Config,
      if_neg hdB,
      if_neg hd,
      denote_empty
    ]

/-! ## 81. Regola P2 per un ordine fissato -/

private def ivP2Order
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList) : IvList :=
  ivUnionMany
    (angleConfigsL.map
      (ivP2Config
        kl_u kl_v kr_u kr_v L R))

private theorem ivP2Order_correct
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList) :
    denote
      (ivP2Order kl_u kl_v kr_u kr_v L R) =
    {z : ℤ |
      P2Rel kl_u kl_v kr_u kr_v
        (denote L) (denote R) z} := by

  rw [t3P2Rel_eq]

  ext z

  change
    z ∈ denote
      (ivUnionMany
        (angleConfigsL.map
          (ivP2Config
            kl_u kl_v kr_u kr_v L R))) ↔
    z ∈
      t3Union t3AnglePairs
        (t3P2Config
          kl_u kl_v kr_u kr_v
          (denote L) (denote R))

  rw [ivUnionMany_correct]

  constructor

  · rintro ⟨X, hX, hz⟩

    obtain ⟨uv, huv, heq⟩ :=
      List.mem_map.mp hX

    subst X

    have hcfg :=
      ivP2Config_correct
        kl_u kl_v kr_u kr_v L R uv

    have hz' :
        z ∈
          t3P2Config
            kl_u kl_v kr_u kr_v
            (denote L) (denote R) uv := by

      rw [← hcfg]

      exact hz

    refine ⟨uv, ?_, hz'⟩

    exact (angleConfigsL_mem uv).mp huv

  · rintro ⟨uv, huv, hz⟩

    refine ⟨
      ivP2Config
        kl_u kl_v kr_u kr_v L R uv,
      ?_,
      ?_
    ⟩

    · apply List.mem_map.mpr

      refine ⟨uv, ?_, rfl⟩

      exact (angleConfigsL_mem uv).mpr huv

    · rw [
        ivP2Config_correct
          kl_u kl_v kr_u kr_v L R uv
      ]

      exact hz

private theorem ivP2Order_normal
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList) :
    Normal
      (ivP2Order
        kl_u kl_v kr_u kr_v L R) := by

  exact ivUnionMany_normal _

/-! ## 82. Regola P2 completa -/

private def ivP2
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList) : IvList :=
  union
    (ivP2Order
      kl_u kl_v kr_u kr_v L R)
    (ivP2Order
      kr_u kr_v kl_u kl_v R L)

private theorem ivP2_correct
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList) :
    denote
      (ivP2 kl_u kl_v kr_u kr_v L R) =
    P2Set kl_u kl_v kr_u kr_v
      (denote L) (denote R) := by

  rw [
    ivP2,
    union_correct,
    ivP2Order_correct,
    ivP2Order_correct
  ]

  ext z

  rfl

private theorem ivP2_normal
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList) :
    Normal
      (ivP2 kl_u kl_v kr_u kr_v L R) := by

  exact union_normal _ _

/-! ## 83. Regola P3 per un ordine fissato -/

private def ivP3Order
    (L C R : IvList) : IvList :=
  inter
    (inter
      (shift L (-4))
      C)
    (shift R 4)

private theorem ivP3Order_correct
    (L C R : IvList) :
    denote (ivP3Order L C R) =
      {z : ℤ |
        P3Rel (denote L) (denote C) (denote R) z} := by

  rw [t3P3Rel_eq]

  unfold ivP3Order

  rw [
    inter_correct,
    inter_correct,
    shift_correct,
    shift_correct
  ]

private theorem ivP3Order_normal
    (L C R : IvList) :
    Normal (ivP3Order L C R) := by

  exact inter_normal _ _

/-! ## 84. Regola P3 sulle sei permutazioni -/

private def ivP3
    (L C R : IvList) : IvList :=
  ivUnionMany
    [
      ivP3Order L C R,
      ivP3Order L R C,
      ivP3Order C L R,
      ivP3Order C R L,
      ivP3Order R L C,
      ivP3Order R C L
    ]

private theorem ivP3_correct
    (L C R : IvList) :
    denote (ivP3 L C R) =
      P3Set (denote L) (denote C) (denote R) := by

  ext z

  change
    z ∈ denote
      (ivUnionMany
        [
          ivP3Order L C R,
          ivP3Order L R C,
          ivP3Order C L R,
          ivP3Order C R L,
          ivP3Order R L C,
          ivP3Order R C L
        ]) ↔
    z ∈ P3Set (denote L) (denote C) (denote R)

  rw [ivUnionMany_correct]

  simp only [
    P3Set,
    Set.mem_setOf_eq,
    List.mem_cons,
    List.not_mem_nil,
    or_false
  ]

  constructor

  · rintro ⟨X, hX, hz⟩

    rcases hX with
      rfl | rfl | rfl | rfl | rfl | rfl

    · exact Or.inl
        ((congrArg (fun S : Set ℤ => z ∈ S)
          (ivP3Order_correct L C R)).mp hz)

    · exact Or.inr (Or.inl
        ((congrArg (fun S : Set ℤ => z ∈ S)
          (ivP3Order_correct L R C)).mp hz))

    · exact Or.inr (Or.inr (Or.inl
        ((congrArg (fun S : Set ℤ => z ∈ S)
          (ivP3Order_correct C L R)).mp hz)))

    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((congrArg (fun S : Set ℤ => z ∈ S)
          (ivP3Order_correct C R L)).mp hz))))

    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((congrArg (fun S : Set ℤ => z ∈ S)
          (ivP3Order_correct R L C)).mp hz)))))

    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((congrArg (fun S : Set ℤ => z ∈ S)
          (ivP3Order_correct R C L)).mp hz)))))

  · intro hz

    rcases hz with
      h | h | h | h | h | h

    · refine ⟨ivP3Order L C R, Or.inl rfl, ?_⟩
      rw [ivP3Order_correct]
      exact h

    · refine ⟨ivP3Order L R C, Or.inr (Or.inl rfl), ?_⟩
      rw [ivP3Order_correct]
      exact h

    · refine ⟨ivP3Order C L R,
        Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      rw [ivP3Order_correct]
      exact h

    · refine ⟨ivP3Order C R L,
        Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
      rw [ivP3Order_correct]
      exact h

    · refine ⟨ivP3Order R L C,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), ?_⟩
      rw [ivP3Order_correct]
      exact h

    · refine ⟨ivP3Order R C L,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), ?_⟩
      rw [ivP3Order_correct]
      exact h

private theorem ivP3_normal
    (L C R : IvList) :
    Normal (ivP3 L C R) := by

  exact ivUnionMany_normal _

/-! ## 85. Algoritmo eval -/

mutual

def eval : SPTree → IvList

  | .Q len =>
      normalize
        [
          (
            -(2 * ((len - 1 : ℕ) : ℤ)),
             2 * ((len - 1 : ℕ) : ℤ)
          )
        ]

  | .S children =>
      evalList children

  | .P2 kl_u kl_v kr_u kr_v l r =>
      ivP2 kl_u kl_v kr_u kr_v
        (eval l) (eval r)

  | .P3 l c r =>
      ivP3 (eval l) (eval c) (eval r)

def evalList : List SPTree → IvList

  | [] =>
      normalize [(0, 0)]

  | t :: ts =>
      mink (eval t) (evalList ts)

end

/-! ## 86. T6a_1 — Correttezza semantica -/

mutual

theorem T6a_1
    (t : SPTree) :
    denote (eval t) = Sigma t := by

  cases t with

  | Q len =>

      change
        denote
          (normalize
            [
              (
                -(2 * ((len - 1 : ℕ) : ℤ)),
                 2 * ((len - 1 : ℕ) : ℤ)
              )
            ]) =
        Band (len - 1)

      rw [normalize_correct]

      have h :
          denote
            [
              (
                -(2 * ((len - 1 : ℕ) : ℤ)),
                 2 * ((len - 1 : ℕ) : ℤ)
              )
            ] =
          Band (len - 1) := by

        ext z

        change
          z ∈
            ivRun
              (-(2 * (((len - 1 : ℕ) : ℤ))))
              (2 * (((len - 1 : ℕ) : ℤ))) ∪
              (∅ : Finset ℤ) ↔
          z ∈ Band (len - 1)

        rw [Finset.mem_union]

        simp only [
          Finset.notMem_empty,
          or_false
        ]

        exact
          Set.ext_iff.mp
            (ivRun_Band (len - 1)) z

      exact h

  | S children =>

      exact T6a_1_list children

  | P2 kl_u kl_v kr_u kr_v l r =>

      change
        denote
          (ivP2 kl_u kl_v kr_u kr_v
            (eval l) (eval r)) =
        P2Set kl_u kl_v kr_u kr_v
          (Sigma l) (Sigma r)

      rw [
        ivP2_correct,
        T6a_1 l,
        T6a_1 r
      ]

  | P3 l c r =>

      change
        denote
          (ivP3 (eval l) (eval c) (eval r)) =
        P3Set (Sigma l) (Sigma c) (Sigma r)

      rw [
        ivP3_correct,
        T6a_1 l,
        T6a_1 c,
        T6a_1 r
      ]

private theorem T6a_1_list
    (ts : List SPTree) :
    denote (evalList ts) =
      SigmaList ts := by

  cases ts with

  | nil =>

      change
        denote (normalize [(0, 0)]) =
          ({0} : Set ℤ)

      rw [normalize_correct]

      exact denote_singleton_zero

  | cons t ts =>

      change
        denote
          (mink (eval t) (evalList ts)) =
        Mink (Sigma t) (SigmaList ts)

      rw [
        mink_correct,
        T6a_1 t,
        T6a_1_list ts
      ]

end

/-! ## 87. Normalità del risultato -/

mutual

private theorem eval_normal
    (t : SPTree) :
    Normal (eval t) := by

  cases t with

  | Q len =>

      exact normalize_normal _

  | S children =>

      exact evalList_normal children

  | P2 kl_u kl_v kr_u kr_v l r =>

      exact
        ivP2_normal
          kl_u kl_v kr_u kr_v
          (eval l)
          (eval r)

  | P3 l c r =>

      exact
        ivP3_normal
          (eval l)
          (eval c)
          (eval r)

private theorem evalList_normal
    (ts : List SPTree) :
    Normal (evalList ts) := by

  cases ts with

  | nil =>

      exact normalize_normal [(0, 0)]

  | cons t ts =>

      exact mink_normal (eval t) (evalList ts)

end

/-! ## 88. T6a_2 — Normalità e numero di pezzi -/

theorem T6a_2
    (t : SPTree) :
    Normal (eval t) ∧
    (eval t).length = pieces2 (Sigma t) := by

  constructor

  · exact eval_normal t

  · calc
      (eval t).length
          = pieces2 (denote (eval t)) :=
            Normal_length_pieces
              (eval t)
              (eval_normal t)

      _ = pieces2 (Sigma t) := by
            rw [T6a_1 t]

/-! ## 89. T6a_3 — Bound dell'algoritmo -/

theorem T6a_3
    (t : SPTree)
    (hwf : WF t) :
    (eval t).length ≤
      36 ^ (2 * heavyP t) := by

  calc
    (eval t).length
        = pieces2 (Sigma t) :=
          (T6a_2 t).2

    _ ≤ 36 ^ (2 * heavyP t) :=
          T5_2 t hwf

/-! ## 90. Esecuzione di prova -/

#eval eval
  (.P2 2 2 2 2
    (.Q 3)
    (.Q 2))

/-! ## 91. Controllo degli assiomi -/

#print axioms T6a_1
#print axioms T6a_2
#print axioms T6a_3


/-
TAPPA 6a' — NORMALIZZAZIONE SUGLI ESTREMI

Operazioni calcolabili sugli estremi dei run (senza espandere i punti).
Risultati: normalizeE_eq (sez. 104), T6a'_1, T6a'_2,
T6a'_3 (evalE = eval) e T6a'_4 (sez. 105).
Nessun sorry, admit o nuovo assioma.
-/

/-! ## 92. Validità dei run -/

def ValidRunE (p : ℤ × ℤ) : Prop :=
  p.1 ≤ p.2 ∧ (p.2 - p.1) % 2 = 0

def ValidIvE (L : IvList) : Prop :=
  ∀ p ∈ L, ValidRunE p

/-! ## 93. Test di appartenenza basato sugli estremi -/

/--
Un punto appartiene a un run quando è compreso
fra gli estremi ed è congruente al primo modulo 2.

Il test non costruisce Finset.Icc.
-/
def memRunE (p : ℤ × ℤ) (z : ℤ) : Bool :=
  decide (p.1 ≤ z) &&
  decide (z ≤ p.2) &&
  decide ((z - p.1) % 2 = 0)

/--
Appartenenza all'unione dei run.

La ricerca visita soltanto le coppie della lista.
-/
def containsE (L : IvList) (z : ℤ) : Bool :=
  L.any (fun p => memRunE p z)

private theorem memRunE_iff
    (p : ℤ × ℤ)
    (z : ℤ) :
    memRunE p z = true ↔
      z ∈ ivRun p.1 p.2 := by

  rw [mem_ivRun]

  simp only [
    memRunE,
    Bool.and_eq_true,
    decide_eq_true_eq
  ]

  exact and_assoc

private theorem containsE_iff
    (L : IvList)
    (z : ℤ) :
    containsE L z = true ↔
      z ∈ denote L := by

  change (L.any (fun p => memRunE p z)) = true ↔ z ∈ ivPoints L

  rw [ivPoints_mem]

  simp only [List.any_eq_true]

  constructor

  · rintro ⟨p, hp, hz⟩

    exact ⟨p, hp, (memRunE_iff p z).mp hz⟩

  · rintro ⟨p, hp, hz⟩

    exact ⟨p, hp, (memRunE_iff p z).mpr hz⟩

/-! ## 94. Individuazione degli inizi -/

/--
Un inizio è un estremo sinistro appartenente
all'unione il cui predecessore a passo 2
non appartiene all'unione.
-/
def isStartE (L : IvList) (a : ℤ) : Bool :=
  containsE L a && !(containsE L (a - 2))

private theorem isStartE_iff
    (L : IvList)
    (a : ℤ) :
    isStartE L a = true ↔
      a ∈ denote L ∧ a - 2 ∉ denote L := by

  unfold isStartE

  rw [Bool.and_eq_true]

  constructor

  · rintro ⟨ha, hp⟩

    constructor

    · exact (containsE_iff L a).mp ha

    · intro hprev

      have hh :=
        (containsE_iff L (a - 2)).mpr hprev

      simp [hh] at hp

  · rintro ⟨ha, hp⟩

    constructor

    · exact (containsE_iff L a).mpr ha

    · have hh :
          containsE L (a - 2) = false := by

        cases h :
            containsE L (a - 2) with

        | false =>
            rfl

        | true =>
            exact False.elim
              (hp ((containsE_iff L (a - 2)).mp h))

      simp [hh]

/-! ## 95. Raccolta degli inizi senza duplicati -/

/--
La raccolta conserva soltanto gli inizi effettivi.

L'eliminazione dei duplicati avviene con List.contains,
quindi non richiede conversioni a Finset.
-/
def collectStartsE (L : IvList) : IvList → List ℤ
  | [] => []

  | p :: ps =>
      let rest := collectStartsE L ps

      if isStartE L p.1 then
        if rest.contains p.1 then
          rest
        else
          p.1 :: rest
      else
        rest

/--
Gli inizi sono ordinati numericamente mediante
merge sort. Il confronto è un Bool esplicito.
-/
def startsE (L : IvList) : List ℤ :=
  (collectStartsE L L).mergeSort
    (fun a b => decide (a ≤ b))

/-! ## 96. Individuazione degli estremi destri -/

/--
Un estremo destro candidato per il run che inizia
in a è un estremo destro originale b tale che:

- a ≤ b;
- a e b hanno la stessa parità;
- b + 2 non appartiene all'unione.

Tra questi candidati si sceglie il minimo.

Per un inizio effettivo esiste sempre almeno
un candidato, purché i run iniziali siano validi.
-/
def isEndCandidateE
    (L : IvList)
    (a : ℤ)
    (p : ℤ × ℤ) : Bool :=

  decide (a ≤ p.2) &&
  decide ((p.2 - a) % 2 = 0) &&
  !(containsE L (p.2 + 2))

def endCandidatesE
    (L : IvList)
    (a : ℤ) : List ℤ :=

  (L.filter (isEndCandidateE L a)).map
    (fun p => p.2)

/--
Ricerca dell'estremo destro di un run massimale.

Il valore a è utilizzato soltanto come fallback
nel caso in cui non esistano candidati.
-/
def endE (L : IvList) (a : ℤ) : ℤ :=
  (endCandidatesE L a).min?.getD a

/-! ## 97. Normalizzazione canonica sugli estremi -/

/--
normalizeE non costruisce mai l'insieme dei punti
rappresentati dai run.

Algoritmo:

1. individua gli inizi effettivi;
2. elimina i duplicati;
3. ordina gli inizi con merge sort;
4. determina l'estremo destro massimale di ogni run.

I run risultanti sono ordinati per inizio numerico,
come nella definizione originale ivCanon.
-/
def normalizeE (L : IvList) : IvList :=
  (startsE L).map
    (fun a => (a, endE L a))

/-! ## 98. Traslazione sugli estremi -/

/--
La traslazione preserva validità e massimalità
dei run quando l'input è normalizzato.
-/
def shiftE (L : IvList) (d : ℤ) : IvList :=
  L.map (fun p => (p.1 + d, p.2 + d))

/-! ## 99. Unione sugli estremi -/

/--
L'unione concatena le rappresentazioni e
normalizza direttamente sugli estremi.
-/
def unionE (L R : IvList) : IvList :=
  normalizeE (L ++ R)

/-! ## 100. Intersezione sugli estremi -/

/--
Intersezione di due singoli run.

Se le parità differiscono, l'intersezione è vuota.

Altrimenti gli estremi dell'intersezione sono
max degli inizi e min delle fini.

Non si enumerano i punti dei due run.
-/
def interRunE
    (p q : ℤ × ℤ) : List (ℤ × ℤ) :=

  let a := max p.1 q.1
  let b := min p.2 q.2

  if decide ((p.1 - q.1) % 2 = 0) &&
     decide (a ≤ b) then
    [(a, b)]
  else
    []

/--
Intersezione di due liste.

Si visitano le coppie di run, senza espanderle.
-/
def interRawE (L R : IvList) : IvList :=
  L.flatMap
    (fun p =>
      R.flatMap (fun q => interRunE p q))

def interE (L R : IvList) : IvList :=
  normalizeE (interRawE L R)

/-! ## 101. Somma di Minkowski sugli estremi -/

/--
La somma di due run validi è il run ottenuto
sommando i rispettivi estremi.
-/
def minkRunE
    (p q : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + q.1, p.2 + q.2)

def minkRawE (L R : IvList) : IvList :=
  L.flatMap
    (fun p =>
      R.map (fun q => minkRunE p q))

def minkE (L R : IvList) : IvList :=
  normalizeE (minkRawE L R)

/-! ## 102. Verifica computazionale delle operazioni -/

#eval normalizeE
  ([(0, 4), (2, 8), (12, 16)] : IvList)

#eval normalizeE
  ([(1, 1), (2, 2)] : IvList)

#eval unionE
  ([(0, 4)] : IvList)
  ([(6, 10)] : IvList)

#eval interE
  ([(-4, 4)] : IvList)
  ([(-2, 6)] : IvList)

#eval minkE
  ([(-4, 4)] : IvList)
  ([(-2, 2)] : IvList)

/-
Piano delle sezioni 103–104 (F = ivPoints L, a ∈ ivStarts F):
1. a è l'estremo sinistro di un run di L;
2. endE L a = ivEnd F a;
3. startsE L = (ivStarts F).sort (· ≤ ·).
Da 2 e 3: normalizeE L = ivCanon F (normalizeE_eq).
-/

/-!
## 103. Parte A — Corrispondenza degli inizi

Obiettivo:

  startsE L =
    (ivStarts (ivPoints L)).sort (fun x y => x ≤ y)

La dimostrazione non richiede ValidIvE.

Non vengono modificate definizioni precedenti.
Non vengono introdotti assiomi.
-/

/-! ### 103.1. Ogni inizio è un estremo sinistro -/

private theorem start_is_left
    (L : IvList)
    (a : ℤ)
    (ha : a ∈ ivStarts (ivPoints L)) :
    ∃ p ∈ L, p.1 = a := by

  obtain ⟨haF, hprev⟩ :=
    (mem_ivStarts (ivPoints L) a).mp ha

  obtain ⟨p, hpL, hap⟩ :=
    (ivPoints_mem L a).mp haF

  obtain ⟨hlo, hhi, hpar⟩ :=
    (mem_ivRun p.1 p.2 a).mp hap

  by_cases heq : p.1 = a

  · exact ⟨p, hpL, heq⟩

  · have hleft :
        p.1 ≤ a - 2 := by
      omega

    have hright :
        a - 2 ≤ p.2 := by
      omega

    have hparPrev :
        ((a - 2) - p.1) % 2 = 0 := by
      omega

    have hprevRun :
        a - 2 ∈ ivRun p.1 p.2 := by
      apply (mem_ivRun p.1 p.2 (a - 2)).mpr
      exact ⟨hleft, hright, hparPrev⟩

    have hprevF :
        a - 2 ∈ ivPoints L :=
      (ivPoints_mem L (a - 2)).mpr
        ⟨p, hpL, hprevRun⟩

    exact False.elim (hprev hprevF)

/-! ### 103.2. Appartenenza a collectStartsE -/

/--
Caratterizzazione degli estremi sinistri
presenti in una lista non vuota.
-/
private theorem t6a103_exists_mem_cons
    (p : ℤ × ℤ)
    (ps : IvList)
    (a : ℤ) :
    (∃ q ∈ p :: ps, q.1 = a) ↔
      (a = p.1 ∨ ∃ q ∈ ps, q.1 = a) := by

  constructor

  · rintro ⟨q, hq, hqa⟩

    rcases List.mem_cons.mp hq with heq | htail

    · subst q
      exact Or.inl hqa.symm

    · exact Or.inr ⟨q, htail, hqa⟩

  · intro h

    rcases h with hpa | ⟨q, hq, hqa⟩

    · exact
        ⟨p, List.mem_cons_self, hpa.symm⟩

    · exact
        ⟨q, List.mem_cons_of_mem p hq, hqa⟩

/--
Lemma di un passo per collectStartsE.

L'inserimento della testa p.1 avviene
esattamente quando isStartE è vero.

Il controllo contains elimina i duplicati,
ma non modifica l'insieme degli elementi raccolti.
-/
private theorem t6a103_collect_cons
    (L : IvList)
    (p : ℤ × ℤ)
    (ps : IvList)
    (a : ℤ) :
    a ∈ collectStartsE L (p :: ps) ↔
      ((a = p.1 ∧ isStartE L p.1 = true) ∨
       a ∈ collectStartsE L ps) := by

  by_cases hs : isStartE L p.1 = true

  · by_cases hc :
        (collectStartsE L ps).contains p.1 = true

    · have hmem :
          p.1 ∈ collectStartsE L ps :=
        (List.contains_iff_mem).mp hc

      have hstep :
          collectStartsE L (p :: ps) =
            collectStartsE L ps := by
        simp only [
          collectStartsE,
          if_pos hs,
          if_pos hc
        ]

      rw [hstep]

      constructor

      · intro ha
        exact Or.inr ha

      · intro ha
        rcases ha with ⟨heq, _⟩ | ha

        · rw [heq]
          exact hmem

        · exact ha

    · have hstep :
          collectStartsE L (p :: ps) =
            p.1 :: collectStartsE L ps := by
        simp only [
          collectStartsE,
          if_pos hs,
          if_neg hc
        ]

      rw [hstep]

      simp only [
        List.mem_cons,
        hs,
        and_true
      ]

  · have hstep :
        collectStartsE L (p :: ps) =
          collectStartsE L ps := by
      simp only [
        collectStartsE,
        if_neg hs
      ]

    rw [hstep]

    simp only [
      hs,
      Bool.false_eq_true,
      and_false,
      false_or
    ]

/--
Caratterizzazione completa di collectStartsE.

La dimostrazione è per induzione sulla sottolista M,
mantenendo fissa la lista originale L.

La variabile a viene generalizzata per rendere
l'ipotesi induttiva applicabile a ogni intero.
-/
private theorem mem_collectStartsE
    (L M : IvList)
    (a : ℤ) :
    a ∈ collectStartsE L M ↔
      (∃ p ∈ M, p.1 = a) ∧
      isStartE L a = true := by

  induction M generalizing a with

  | nil =>

      constructor

      · intro h
        have hempty :
            a ∈ ([] : List ℤ) := h
        cases hempty

      · rintro ⟨⟨p, hp, _⟩, _⟩
        cases hp

  | cons p ps ih =>

      rw [
        t6a103_collect_cons,
        t6a103_exists_mem_cons
      ]

      constructor

      · intro h

        rcases h with hhead | htail

        · rcases hhead with ⟨hpa, hs⟩

          constructor

          · exact Or.inl hpa

          · have heq : p.1 = a := hpa.symm
            rw [← heq]
            exact hs

        · have htail' :
              (∃ q ∈ ps, q.1 = a) ∧
                isStartE L a = true :=
            (ih a).mp htail

          obtain ⟨hex, hs⟩ := htail'

          exact ⟨Or.inr hex, hs⟩

      · rintro ⟨hex, hs⟩

        rcases hex with hhead | htail

        · left

          constructor

          · exact hhead

          · have heq : a = p.1 := hhead
            rw [heq] at hs
            exact hs

        · right

          have htail' :
              (∃ q ∈ ps, q.1 = a) ∧
                isStartE L a = true :=
            ⟨htail, hs⟩

          exact (ih a).mpr htail'

/-! ### 103.3. Assenza di duplicati -/

/--
collectStartsE non introduce duplicati.

La dimostrazione usa il controllo contains
e l'ipotesi induttiva sulla coda.
-/
private theorem collectStartsE_nodup
    (L M : IvList) :
    (collectStartsE L M).Nodup := by

  induction M with

  | nil =>

      simp only [
        collectStartsE,
        List.nodup_nil
      ]

  | cons p ps ih =>

      by_cases hs : isStartE L p.1 = true

      · by_cases hc :
            (collectStartsE L ps).contains p.1 = true

        · have hstep :
              collectStartsE L (p :: ps) =
                collectStartsE L ps := by
            simp only [
              collectStartsE,
              if_pos hs,
              if_pos hc
            ]

          rw [hstep]

          exact ih

        · have hstep :
              collectStartsE L (p :: ps) =
                p.1 :: collectStartsE L ps := by
            simp only [
              collectStartsE,
              if_pos hs,
              if_neg hc
            ]

          have hnot :
              p.1 ∉ collectStartsE L ps := by

            intro hmem

            have hcontains :
                (collectStartsE L ps).contains p.1 =
                  true :=
              (List.contains_iff_mem).mpr hmem

            exact hc hcontains

          rw [hstep]

          exact List.Nodup.cons hnot ih

      · have hstep :
            collectStartsE L (p :: ps) =
              collectStartsE L ps := by
          simp only [
            collectStartsE,
            if_neg hs
          ]

        rw [hstep]

        exact ih

/-! ### 103.4. Corrispondenza degli inizi -/

/--
Il test booleano isStartE coincide con
l'appartenenza a ivStarts (ivPoints L).
-/
private theorem t6a103_isStart_iff
    (L : IvList)
    (a : ℤ) :
    isStartE L a = true ↔
      a ∈ ivStarts (ivPoints L) := by

  exact
    (isStartE_iff L a).trans
      ((mem_ivStarts (ivPoints L) a).symm)

/--
La lista startsE contiene esattamente gli inizi
delle componenti di ivPoints L.
-/
private theorem mem_startsE
    (L : IvList)
    (a : ℤ) :
    a ∈ startsE L ↔
      a ∈ ivStarts (ivPoints L) := by

  unfold startsE

  rw [List.mem_mergeSort]

  rw [mem_collectStartsE]

  constructor

  · rintro ⟨_, hs⟩

    exact (t6a103_isStart_iff L a).mp hs

  · intro ha

    constructor

    · exact start_is_left L a ha

    · exact
        (t6a103_isStart_iff L a).mpr ha

/-! ### 103.5. Unicità di liste strettamente ordinate -/

/--
Una lista senza duplicati ordinata debolmente
è strettamente ordinata.

La prova è per induzione sulla lista.
-/
private theorem t6a103_pairwise_lt_of_le_nodup :
    ∀ l : List ℤ,
      l.Pairwise (fun x y => x ≤ y) →
      l.Nodup →
      l.Pairwise (fun x y => x < y) := by

  intro l

  induction l with

  | nil =>

      intro _ _

      exact List.Pairwise.nil

  | cons a as ih =>

      intro hle hnodup

      obtain ⟨hfront, htail⟩ :=
        List.pairwise_cons.mp hle

      obtain ⟨hnot, hnodupTail⟩ :=
        List.nodup_cons.mp hnodup

      apply List.Pairwise.cons

      · intro b hb

        have hab : a ≤ b :=
          hfront b hb

        have hne : a ≠ b := by

          intro heq

          apply hnot

          rw [heq]

          exact hb

        omega

      · exact ih htail hnodupTail

/--
Due liste di interi strettamente ordinate
con gli stessi elementi sono uguali.

La dimostrazione confronta le teste e
procede per induzione sulle code.
-/
private theorem t6a103_eq_of_pairwise_lt_mem :
    ∀ l₁ l₂ : List ℤ,
      l₁.Pairwise (fun x y => x < y) →
      l₂.Pairwise (fun x y => x < y) →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) →
      l₁ = l₂ := by

  intro l₁

  induction l₁ with

  | nil =>

      intro l₂ _ _ hmem

      cases l₂ with

      | nil =>
          rfl

      | cons b bs =>

          have hb :
              b ∈ ([] : List ℤ) :=
            (hmem b).mpr List.mem_cons_self

          cases hb

  | cons a as ih =>

      intro l₂ h₁ h₂ hmem

      cases l₂ with

      | nil =>

          have ha :
              a ∈ ([] : List ℤ) :=
            (hmem a).mp List.mem_cons_self

          cases ha

      | cons b bs =>

          obtain ⟨h₁front, h₁tail⟩ :=
            List.pairwise_cons.mp h₁

          obtain ⟨h₂front, h₂tail⟩ :=
            List.pairwise_cons.mp h₂

          have hab : a ≤ b := by

            have hb :
                b ∈ a :: as :=
              (hmem b).mpr List.mem_cons_self

            rcases List.mem_cons.mp hb with
              heq | htail

            · omega

            · exact le_of_lt (h₁front b htail)

          have hba : b ≤ a := by

            have ha :
                a ∈ b :: bs :=
              (hmem a).mp List.mem_cons_self

            rcases List.mem_cons.mp ha with
              heq | htail

            · omega

            · exact le_of_lt (h₂front a htail)

          have heq : a = b := by
            omega

          subst b

          have hnotAs : a ∉ as := by

            intro ha

            have hlt := h₁front a ha

            omega

          have hnotBs : a ∉ bs := by

            intro hb

            have hlt := h₂front a hb

            omega

          have htailMem :
              ∀ x, x ∈ as ↔ x ∈ bs := by

            intro x

            constructor

            · intro hx

              have hx' :
                  x ∈ a :: bs :=
                (hmem x).mp
                  (List.mem_cons_of_mem a hx)

              rcases List.mem_cons.mp hx' with
                heqHead | hxBs

              · have hxa : x = a := heqHead

                have haa : a ∈ as := by
                  rw [hxa] at hx
                  exact hx

                exact False.elim (hnotAs haa)

              · exact hxBs

            · intro hx

              have hx' :
                  x ∈ a :: as :=
                (hmem x).mpr
                  (List.mem_cons_of_mem a hx)

              rcases List.mem_cons.mp hx' with
                heqHead | hxAs

              · have hxa : x = a := heqHead

                have haa : a ∈ bs := by
                  rw [hxa] at hx
                  exact hx

                exact False.elim (hnotBs haa)

              · exact hxAs

          have htailEq :
              as = bs :=
            ih bs h₁tail h₂tail htailMem

          exact congrArg (List.cons a) htailEq

/-! ### 103.6. Ordinamento di startsE -/

/--
Transitività del comparatore booleano su ℤ.
-/
private theorem t6a103_leBool_trans :
    ∀ a b c : ℤ,
      decide (a ≤ b) = true →
      decide (b ≤ c) = true →
      decide (a ≤ c) = true := by

  intro a b c hab hbc

  have hab' : a ≤ b :=
    (decide_eq_true_eq).mp hab

  have hbc' : b ≤ c :=
    (decide_eq_true_eq).mp hbc

  exact
    (decide_eq_true_eq).mpr
      (le_trans hab' hbc')

/--
Totalità del comparatore booleano su ℤ.
-/
private theorem t6a103_leBool_total :
    ∀ a b : ℤ,
      (decide (a ≤ b) ||
       decide (b ≤ a)) = true := by

  intro a b

  rw [Bool.or_eq_true]

  rcases le_total a b with hab | hba

  · exact Or.inl
      ((decide_eq_true_eq).mpr hab)

  · exact Or.inr
      ((decide_eq_true_eq).mpr hba)

/--
La lista startsE è ordinata debolmente.
-/
private theorem t6a103_startsE_pairwise_le
    (L : IvList) :
    (startsE L).Pairwise
      (fun x y : ℤ => x ≤ y) := by

  have hsort :
      ((collectStartsE L L).mergeSort
        (fun x y => decide (x ≤ y))).Pairwise
          (fun x y : ℤ =>
            decide (x ≤ y) = true) :=

    List.pairwise_mergeSort
      t6a103_leBool_trans
      t6a103_leBool_total
      (collectStartsE L L)

  unfold startsE

  simpa only [decide_eq_true_eq] using hsort

/--
La lista startsE non contiene duplicati.
-/
private theorem t6a103_startsE_nodup
    (L : IvList) :
    (startsE L).Nodup := by

  unfold startsE

  exact
    List.Nodup.mergeSort
      (collectStartsE_nodup L L)

/--
La lista startsE è strettamente ordinata.
-/
private theorem t6a103_startsE_pairwise_lt
    (L : IvList) :
    (startsE L).Pairwise
      (fun x y : ℤ => x < y) := by

  exact
    t6a103_pairwise_lt_of_le_nodup
      (startsE L)
      (t6a103_startsE_pairwise_le L)
      (t6a103_startsE_nodup L)

/-! ### 103.7. Uguaglianza delle liste ordinate -/

/--
Teorema principale della parte A.

startsE produce esattamente la lista degli inizi
di ivPoints L, in ordine numerico crescente.

Non è necessaria l'ipotesi ValidIvE.
-/
private theorem startsE_eq
    (L : IvList) :
    startsE L =
      (ivStarts (ivPoints L)).sort
        (fun x y => x ≤ y) := by

  let F : Finset ℤ :=
    ivStarts (ivPoints L)

  have hleft :
      (startsE L).Pairwise
        (fun x y : ℤ => x < y) :=
    t6a103_startsE_pairwise_lt L

  have hright :
      (F.sort (fun x y : ℤ => x ≤ y)).Pairwise
        (fun x y : ℤ => x < y) := by

    exact (Finset.sortedLT_sort F).pairwise

  have hmem :
      ∀ x : ℤ,
        x ∈ startsE L ↔
          x ∈ F.sort (fun a b : ℤ => a ≤ b) := by

    intro x

    constructor

    · intro hx

      have hxF :
          x ∈ F :=
        (mem_startsE L x).mp hx

      exact
        (Finset.mem_sort
          (fun a b : ℤ => a ≤ b)).mpr hxF

    · intro hx

      have hxF :
          x ∈ F :=
        (Finset.mem_sort
          (fun a b : ℤ => a ≤ b)).mp hx

      exact
        (mem_startsE L x).mpr hxF

  exact
    t6a103_eq_of_pairwise_lt_mem
      (startsE L)
      (F.sort (fun a b : ℤ => a ≤ b))
      hleft
      hright
      hmem

/-! ### 103.8. Controllo degli assiomi -/

#print axioms startsE_eq

/-!
## 104. Parte B — Estremi destri e normalizzazione canonica

Obiettivo principale:

  normalizeE L = ivCanon (ivPoints L)

per ogni lista L di run validi.

La parte A (sezione 103) fornisce startsE_eq.

La parte B dimostra:
1. ivEnd F a + 2 non appartiene a F;
2. ivEnd F a coincide con un estremo destro originale;
3. ivEnd F a appartiene a endCandidatesE L a;
4. ivEnd F a è il minimo dei candidati;
5. endE L a = ivEnd F a;
6. normalizeE_eq e i due corollari.

Nessun nuovo assioma.
-/

/-! ### 104.1. Il successore dell'estremo massimo è assente -/

private theorem ivEnd_next_notMem
    (L : IvList)
    (a : ℤ)
    (ha : a ∈ ivStarts (ivPoints L)) :
    ivEnd (ivPoints L) a + 2 ∉ ivPoints L := by

  let F : Finset ℤ := ivPoints L
  let e : ℤ := ivEnd F a

  have haF : a ∈ F :=
    ((mem_ivStarts F a).mp ha).1

  obtain ⟨hae, hpar, hgood⟩ :=
    ivEnd_spec F a haF

  intro hnext

  have hnextF : e + 2 ∈ F := hnext

  have hgoodNext :
      ivGood F a (e + 2) := by

    intro z hz hzpar

    have hbounds :=
      Finset.mem_Icc.mp hz

    by_cases hze : z ≤ e

    · exact
        hgood z
          (Finset.mem_Icc.mpr
            ⟨hbounds.1, hze⟩)
          hzpar

    · have heq : z = e + 2 := by
        omega

      rw [heq]

      exact hnextF

  have hparNext :
      ((e + 2) - a) % 2 = 0 := by
    omega

  have hc :
      e + 2 ∈ ivRightCandidates F a := by

    apply
      (mem_ivRightCandidates F a (e + 2)).mpr

    right

    exact ⟨
      hnextF,
      by omega,
      hparNext,
      hgoodNext
    ⟩

  have hmax :
      e + 2 ≤ e :=
    ivEnd_le F a (e + 2) hc

  omega

/-! ### 104.2. L'estremo massimo appartiene a F -/

private theorem ivEnd_mem_points
    (L : IvList)
    (a : ℤ)
    (ha : a ∈ ivStarts (ivPoints L)) :
    ivEnd (ivPoints L) a ∈ ivPoints L := by

  let F : Finset ℤ := ivPoints L
  let e : ℤ := ivEnd F a

  have haF : a ∈ F :=
    ((mem_ivStarts F a).mp ha).1

  obtain ⟨hae, hpar, hgood⟩ :=
    ivEnd_spec F a haF

  apply hgood e

  · exact
      Finset.mem_Icc.mpr
        ⟨hae, le_refl e⟩

  · exact hpar

/-! ### 104.3. L'estremo massimo è un estremo originale -/

private theorem ivEnd_is_right
    (L : IvList)
    (a : ℤ)
    (hL : ValidIvE L)
    (ha : a ∈ ivStarts (ivPoints L)) :
    ∃ p ∈ L, p.2 = ivEnd (ivPoints L) a := by

  let F : Finset ℤ := ivPoints L
  let e : ℤ := ivEnd F a

  have heF : e ∈ F :=
    ivEnd_mem_points L a ha

  obtain ⟨p, hpL, hep⟩ :=
    (ivPoints_mem L e).mp heF

  obtain ⟨hpLo, hpHi, hpPar⟩ :=
    (mem_ivRun p.1 p.2 e).mp hep

  have hpValid : ValidRunE p :=
    hL p hpL

  change
    p.1 ≤ p.2 ∧
      (p.2 - p.1) % 2 = 0
    at hpValid

  have hpEndPar :
      (p.2 - p.1) % 2 = 0 :=
    hpValid.2

  by_cases heq : p.2 = e

  · exact ⟨p, hpL, heq⟩

  · have hpNextLe :
        e + 2 ≤ p.2 := by
      omega

    have hpNextPar :
        ((e + 2) - p.1) % 2 = 0 := by
      omega

    have hpNextRun :
        e + 2 ∈ ivRun p.1 p.2 := by

      apply
        (mem_ivRun p.1 p.2 (e + 2)).mpr

      exact ⟨
        by omega,
        hpNextLe,
        hpNextPar
      ⟩

    have hpNextF :
        e + 2 ∈ F :=
      (ivPoints_mem L (e + 2)).mpr
        ⟨p, hpL, hpNextRun⟩

    have hnot :
        e + 2 ∉ F :=
      ivEnd_next_notMem L a ha

    exact False.elim (hnot hpNextF)

/-! ### 104.4. Il test booleano di assenza -/

/--
Se z non appartiene ai punti rappresentati,
containsE L z restituisce false.
-/
private theorem t6a104_contains_false
    (L : IvList)
    (z : ℤ)
    (hz : z ∉ ivPoints L) :
    containsE L z = false := by

  cases h : containsE L z with

  | false =>
      rfl

  | true =>

      have hzL : z ∈ denote L :=
        (containsE_iff L z).mp h

      have hzF : z ∈ ivPoints L := hzL

      exact False.elim (hz hzF)

/-! ### 104.5. L'estremo massimo è un candidato -/

private theorem ivEnd_mem_candidates
    (L : IvList)
    (a : ℤ)
    (hL : ValidIvE L)
    (ha : a ∈ ivStarts (ivPoints L)) :
    ivEnd (ivPoints L) a ∈
      endCandidatesE L a := by

  let F : Finset ℤ := ivPoints L
  let e : ℤ := ivEnd F a

  have haF : a ∈ F :=
    ((mem_ivStarts F a).mp ha).1

  obtain ⟨hae, hpar, hgood⟩ :=
    ivEnd_spec F a haF

  obtain ⟨p, hpL, hpEnd⟩ :=
    ivEnd_is_right L a hL ha

  have hnot :
      e + 2 ∉ F :=
    ivEnd_next_notMem L a ha

  have hfalse :
      containsE L (e + 2) = false :=
    t6a104_contains_false L (e + 2) hnot

  have htest :
      isEndCandidateE L a p = true := by

    change
      (decide (a ≤ p.2) &&
       decide ((p.2 - a) % 2 = 0) &&
       !(containsE L (p.2 + 2))) = true

    rw [hpEnd]

    rw [Bool.and_eq_true]

    constructor

    · rw [Bool.and_eq_true]

      exact ⟨
        (decide_eq_true_eq).mpr hae,
        (decide_eq_true_eq).mpr hpar
      ⟩

    · have hf : containsE L (ivEnd (ivPoints L) a + 2) = false := hfalse
      rw [hf]
      rfl

  unfold endCandidatesE

  apply List.mem_map.mpr

  refine ⟨p, ?_, hpEnd⟩

  apply List.mem_filter.mpr

  exact ⟨hpL, htest⟩

/-! ### 104.6. Caratterizzazione di un candidato -/

/--
Ogni candidato b soddisfa:
- a ≤ b;
- b ha la parità di a;
- b+2 non appartiene all'insieme rappresentato.
-/
private theorem t6a104_candidate_spec
    (L : IvList)
    (a b : ℤ)
    (hb : b ∈ endCandidatesE L a) :
    a ≤ b ∧
    (b - a) % 2 = 0 ∧
    containsE L (b + 2) = false := by

  unfold endCandidatesE at hb

  obtain ⟨p, hp, hpEnd⟩ :=
    List.mem_map.mp hb

  obtain ⟨hpL, hpTest⟩ :=
    List.mem_filter.mp hp

  change
    (decide (a ≤ p.2) &&
     decide ((p.2 - a) % 2 = 0) &&
     !(containsE L (p.2 + 2))) = true
    at hpTest

  simp only [Bool.and_eq_true] at hpTest

  obtain ⟨⟨hlo, hpar⟩, hnot⟩ := hpTest

  have hpLo : a ≤ p.2 :=
    (decide_eq_true_eq).mp hlo

  have hpPar :
      (p.2 - a) % 2 = 0 :=
    (decide_eq_true_eq).mp hpar

  have hpFalse :
      containsE L (p.2 + 2) = false := by

    cases hc : containsE L (p.2 + 2) with

    | false =>
        rfl

    | true =>
        simp only [hc] at hnot
        cases hnot

  rw [hpEnd] at hpLo hpPar hpFalse

  exact ⟨hpLo, hpPar, hpFalse⟩

/-! ### 104.7. Minimalità dell'estremo massimo -/

private theorem ivEnd_le_candidates
    (L : IvList)
    (a : ℤ)
    (ha : a ∈ ivStarts (ivPoints L)) :
    ∀ b ∈ endCandidatesE L a,
      ivEnd (ivPoints L) a ≤ b := by

  intro b hb

  let F : Finset ℤ := ivPoints L
  let e : ℤ := ivEnd F a

  have haF : a ∈ F :=
    ((mem_ivStarts F a).mp ha).1

  obtain ⟨hae, hePar, hgood⟩ :=
    ivEnd_spec F a haF

  obtain ⟨hab, hbPar, hbFalse⟩ :=
    t6a104_candidate_spec L a b hb

  have hEe : e = ivEnd (ivPoints L) a := rfl

  by_contra hne

  have hlt : b < e := by
    omega

  have hbNextLe :
      b + 2 ≤ e := by
    omega

  have hbNextPar :
      ((b + 2) - a) % 2 = 0 := by
    omega

  have hbNextF :
      b + 2 ∈ F := by

    apply hgood (b + 2)

    · exact
        Finset.mem_Icc.mpr
          ⟨by omega, hbNextLe⟩

    · exact hbNextPar

  have hbNextContains :
      containsE L (b + 2) = true :=
    (containsE_iff L (b + 2)).mpr hbNextF

  rw [hbFalse] at hbNextContains

  cases hbNextContains

/-! ### 104.8. Lemma generale sul minimo di una lista -/

/--
Se x è minore o uguale all'accumulatore iniziale,
è minore o uguale a ogni elemento della lista
e compare fra l'accumulatore e la lista,
allora foldl min restituisce x.
-/
private theorem t6a104_foldl_min_least :
    ∀ (ys : List ℤ) (x v : ℤ),
      x ≤ v →
      (∀ y ∈ ys, x ≤ y) →
      (x = v ∨ x ∈ ys) →
      ys.foldl min v = x := by

  intro ys

  induction ys with

  | nil =>

      intro x v hxv _ hx

      rcases hx with heq | hmem

      · simp only [List.foldl_nil]
        omega

      · cases hmem

  | cons y ys ih =>

      intro x v hxv hbound hx

      have hxy : x ≤ y :=
        hbound y List.mem_cons_self

      have hxMin :
          x ≤ min v y :=
        le_min hxv hxy

      have htail :
          ∀ z ∈ ys, x ≤ z := by

        intro z hz

        exact
          hbound z
            (List.mem_cons_of_mem y hz)

      have hxMember :
          x = min v y ∨ x ∈ ys := by

        rcases hx with heq | hmem

        · left

          subst v

          simp only [min_eq_left hxy]

        · rcases List.mem_cons.mp hmem with
            heq | hmemTail

          · left

            subst y

            simp only [min_eq_right hxv]

          · right

            exact hmemTail

      simp only [List.foldl_cons]

      exact
        ih x (min v y)
          hxMin htail hxMember

/--
Lemma richiesto sul minimo di una lista.

La dimostrazione è per induzione sulla lista e
utilizza il lemma esplicito su foldl min.
-/
private theorem min?_of_least
    (l : List ℤ)
    (x : ℤ)
    (hx : x ∈ l)
    (h : ∀ y ∈ l, x ≤ y) :
    l.min? = some x := by

  induction l with

  | nil =>

      cases hx

  | cons y ys ih =>

      have hxy : x ≤ y :=
        h y List.mem_cons_self

      have htail :
          ∀ z ∈ ys, x ≤ z := by

        intro z hz

        exact
          h z
            (List.mem_cons_of_mem y hz)

      have hxMember :
          x = y ∨ x ∈ ys :=
        List.mem_cons.mp hx

      have hfold :
          ys.foldl min y = x :=
        t6a104_foldl_min_least
          ys x y
          hxy htail hxMember

      rw [List.min?_cons']

      rw [hfold]

/-! ### 104.9. Uguaglianza degli estremi -/

/--
Per ogni inizio effettivo a, la ricerca sugli estremi
originali restituisce esattamente ivEnd F a.
-/
private theorem endE_eq
    (L : IvList)
    (a : ℤ)
    (hL : ValidIvE L)
    (ha : a ∈ ivStarts (ivPoints L)) :
    endE L a = ivEnd (ivPoints L) a := by

  have hmem :
      ivEnd (ivPoints L) a ∈
        endCandidatesE L a :=
    ivEnd_mem_candidates L a hL ha

  have hleast :
      ∀ b ∈ endCandidatesE L a,
        ivEnd (ivPoints L) a ≤ b :=
    ivEnd_le_candidates L a ha

  have hmin :
      (endCandidatesE L a).min? =
        some (ivEnd (ivPoints L) a) :=
    min?_of_least
      (endCandidatesE L a)
      (ivEnd (ivPoints L) a)
      hmem hleast

  unfold endE

  rw [hmin]

  rfl

/-! ### 104.10. Teorema principale di normalizzazione -/

/--
normalizeE produce esattamente la rappresentazione
canonica ivCanon (ivPoints L) per ogni lista valida.

La dimostrazione combina:
- startsE_eq, dalla parte A;
- endE_eq, dalla parte B.

Non viene espanso alcun run nel codice computabile.
-/
theorem normalizeE_eq
    (L : IvList)
    (hL : ValidIvE L) :
    normalizeE L =
      ivCanon (ivPoints L) := by

  unfold normalizeE ivCanon

  rw [startsE_eq]

  apply List.map_congr_left

  intro a ha

  have hstart :
      a ∈ ivStarts (ivPoints L) :=
    (Finset.mem_sort
      (fun x y : ℤ => x ≤ y)).mp ha

  have hend :
      endE L a =
        ivEnd (ivPoints L) a :=
    endE_eq L a hL hstart

  rw [hend]

/-! ### 104.11. Correttezza semantica -/

/--
T6a'_1.

La normalizzazione sugli estremi conserva
esattamente l'insieme rappresentato.
-/
theorem T6a'_1
    (L : IvList)
    (hL : ValidIvE L) :
    denote (normalizeE L) =
      denote L := by

  rw [normalizeE_eq L hL]

  rw [denote_canon]

  rfl

/-! ### 104.12. Normalità -/

/--
T6a'_2.

La normalizzazione sugli estremi produce
la stessa forma normale della tappa 6a.
-/
theorem T6a'_2
    (L : IvList)
    (hL : ValidIvE L) :
    Normal (normalizeE L) := by

  rw [normalizeE_eq L hL]

  exact ivCanon_normal (ivPoints L)

/-! ### 104.13. Controllo degli assiomi -/

#print axioms normalizeE_eq
#print axioms T6a'_1
#print axioms T6a'_2


/-! ## 105. Tappa 6a′ parte C — evalE coincide con eval -/

/-! ### 105.1. Liste normali: validità e unicità -/

theorem ivCanon_valid (F : Finset ℤ) : ValidIvE (ivCanon F) := by
  intro p hp
  unfold ivCanon at hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  have has : a ∈ ivStarts F := by simpa only [Finset.mem_sort] using ha
  have haF : a ∈ F := ((mem_ivStarts F a).mp has).1
  obtain ⟨h1, h2, _⟩ := ivEnd_spec F a haF
  exact ⟨h1, h2⟩

theorem normal_valid (L : IvList) (h : Normal L) : ValidIvE L := by
  have heq : L = ivCanon (ivPoints L) := h
  rw [heq]
  exact ivCanon_valid _

theorem normalizeE_eq_points (L : IvList) (hL : ValidIvE L) (F : Finset ℤ)
    (hF : ivPoints L = F) : normalizeE L = ivCanon F := by
  rw [normalizeE_eq L hL, hF]

theorem ivPoints_ext (L R : IvList)
    (h : ∀ z, (∃ p ∈ L, z ∈ ivRun p.1 p.2) ↔ (∃ p ∈ R, z ∈ ivRun p.1 p.2)) :
    ivPoints L = ivPoints R := by
  ext z
  rw [ivPoints_mem, ivPoints_mem]
  exact h z

/-! ### 105.2. Validità delle liste speciali -/

theorem valid_nil : ValidIvE [] := by
  intro p hp
  simp at hp

theorem valid_append (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    ValidIvE (L ++ R) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hR p h

theorem valid_band (n : ℤ) (hn : 0 ≤ n) : ValidIvE [(-(2 * n), 2 * n)] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  constructor <;> simp only <;> omega

/-! ### 105.3. shiftE -/

theorem shiftE_valid (L : IvList) (d : ℤ) (hL : ValidIvE L) :
    ValidIvE (shiftE L d) := by
  intro p hp
  unfold shiftE at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨h1, h2⟩ := hL q hq
  constructor
  · show q.1 + d ≤ q.2 + d
    omega
  · show (q.2 + d - (q.1 + d)) % 2 = 0
    have : q.2 + d - (q.1 + d) = q.2 - q.1 := by ring
    rw [this]; exact h2

theorem shiftE_points (L : IvList) (d : ℤ) :
    ivPoints (shiftE L d) = (ivPoints L).image (fun x => x + d) := by
  ext z
  rw [ivPoints_mem, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hz⟩
    unfold shiftE at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3⟩ := (mem_ivRun _ _ z).mp hz
    refine ⟨z - d, (ivPoints_mem L _).mpr ⟨q, hq, ?_⟩, by ring⟩
    apply (mem_ivRun _ _ _).mpr
    simp only at h1 h2 h3
    refine ⟨by omega, by omega, ?_⟩
    have : z - d - q.1 = z - (q.1 + d) := by ring
    rw [this]; exact h3
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨q, hq, hxq⟩ := (ivPoints_mem L x).mp hx
    obtain ⟨h1, h2, h3⟩ := (mem_ivRun _ _ x).mp hxq
    refine ⟨(q.1 + d, q.2 + d), List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    apply (mem_ivRun _ _ _).mpr
    refine ⟨by simp only; omega, by simp only; omega, ?_⟩
    simp only
    have : x + d - (q.1 + d) = x - q.1 := by ring
    rw [this]; exact h3

theorem shift_points (L : IvList) (d : ℤ) :
    ivPoints (shift L d) = (ivPoints L).image (fun x => x + d) := by
  unfold shift
  exact ivPoints_canon _

/-! ### 105.4. unionE -/

theorem append_points (L R : IvList) :
    ivPoints (L ++ R) = ivPoints L ∪ ivPoints R := by
  ext z
  rw [Finset.mem_union, ivPoints_mem, ivPoints_mem, ivPoints_mem]
  constructor
  · rintro ⟨p, hp, hz⟩
    rcases List.mem_append.mp hp with h | h
    · exact Or.inl ⟨p, h, hz⟩
    · exact Or.inr ⟨p, h, hz⟩
  · rintro (⟨p, hp, hz⟩ | ⟨p, hp, hz⟩)
    · exact ⟨p, List.mem_append.mpr (Or.inl hp), hz⟩
    · exact ⟨p, List.mem_append.mpr (Or.inr hp), hz⟩

theorem unionE_eq (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    unionE L R = union L R := by
  unfold unionE union
  exact normalizeE_eq_points _ (valid_append L R hL hR) _ (append_points L R)

/-! ### 105.5. interE -/

theorem interRunE_valid (p q : ℤ × ℤ) (hp : ValidRunE p) (hq : ValidRunE q) :
    ValidIvE (interRunE p q) := by
  intro r hr
  unfold interRunE at hr
  dsimp only at hr
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  split_ifs at hr with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hpar, hle⟩ := h
    refine ⟨hle, ?_⟩
    show (min p.2 q.2 - max p.1 q.1) % 2 = 0
    rcases le_total p.2 q.2 with h1 | h1 <;>
    rcases le_total p.1 q.1 with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2]; omega
    · rw [min_eq_left h1, max_eq_left h2]; omega
    · rw [min_eq_right h1, max_eq_right h2]; omega
    · rw [min_eq_right h1, max_eq_left h2]; omega
  · simp at hr

theorem interRunE_mem (p q : ℤ × ℤ) (hp : ValidRunE p) (hq : ValidRunE q) (z : ℤ) :
    (∃ r ∈ interRunE p q, z ∈ ivRun r.1 r.2) ↔
      (z ∈ ivRun p.1 p.2 ∧ z ∈ ivRun q.1 q.2) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  rw [mem_ivRun, mem_ivRun]
  unfold interRunE
  dsimp only
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hpar, _⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, mem_ivRun]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have a1 := le_max_left p.1 q.1
      have a2 := le_max_right p.1 q.1
      have b1 := min_le_left p.2 q.2
      have b2 := min_le_right p.2 q.2
      rcases max_choice p.1 q.1 with hm | hm <;> rw [hm] at h3 <;>
        refine ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩⟩
    · rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩
      refine ⟨max_le h1 h4, le_min h2 h5, ?_⟩
      rcases max_choice p.1 q.1 with hm | hm <;> rw [hm] <;> omega
  · simp only [List.not_mem_nil, false_and, exists_false, false_iff]
    rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩
    apply h
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, le_trans (max_le h1 h4) (le_min h2 h5)⟩

theorem interRawE_valid (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    ValidIvE (interRawE L R) := by
  intro r hr
  unfold interRawE at hr
  obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨q, hq, hr⟩ := List.mem_flatMap.mp hr
  exact interRunE_valid p q (hL p hp) (hR q hq) r hr

theorem interRawE_points (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    ivPoints (interRawE L R) = ivPoints L ∩ ivPoints R := by
  ext z
  rw [Finset.mem_inter, ivPoints_mem, ivPoints_mem, ivPoints_mem]
  constructor
  · rintro ⟨r, hr, hz⟩
    unfold interRawE at hr
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨q, hq, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨h1, h2⟩ := (interRunE_mem p q (hL p hp) (hR q hq) z).mp ⟨r, hr, hz⟩
    exact ⟨⟨p, hp, h1⟩, ⟨q, hq, h2⟩⟩
  · rintro ⟨⟨p, hp, h1⟩, ⟨q, hq, h2⟩⟩
    obtain ⟨r, hr, hz⟩ := (interRunE_mem p q (hL p hp) (hR q hq) z).mpr ⟨h1, h2⟩
    refine ⟨r, ?_, hz⟩
    unfold interRawE
    exact List.mem_flatMap.mpr ⟨p, hp, List.mem_flatMap.mpr ⟨q, hq, hr⟩⟩

theorem interE_canon (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    interE L R = ivCanon (ivPoints L ∩ ivPoints R) := by
  unfold interE
  exact normalizeE_eq_points _ (interRawE_valid L R hL hR) _ (interRawE_points L R hL hR)

theorem interE_eq (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    interE L R = inter L R := interE_canon L R hL hR

/-! ### 105.6. minkE -/

theorem minkRawE_valid (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    ValidIvE (minkRawE L R) := by
  intro r hr
  unfold minkRawE at hr
  obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  obtain ⟨h1, h2⟩ := hL p hp
  obtain ⟨h3, h4⟩ := hR q hq
  refine ⟨?_, ?_⟩
  · show p.1 + q.1 ≤ p.2 + q.2
    omega
  · show (p.2 + q.2 - (p.1 + q.1)) % 2 = 0
    omega

theorem minkRun_mem (p q : ℤ × ℤ) (hp : ValidRunE p) (hq : ValidRunE q) (z : ℤ) :
    z ∈ ivRun (p.1 + q.1) (p.2 + q.2) ↔
      ∃ x ∈ ivRun p.1 p.2, ∃ y ∈ ivRun q.1 q.2, z = x + y := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  simp only [mem_ivRun]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hc : p.1 ≤ z - q.2
    · refine ⟨z - q.2, ⟨hc, by omega, by omega⟩, q.2, ⟨hq1, le_refl _, by omega⟩, by ring⟩
    · refine ⟨p.1, ⟨le_refl _, hp1, by omega⟩, z - p.1, ⟨by omega, by omega, by omega⟩, by ring⟩
  · rintro ⟨x, ⟨h1, h2, h3⟩, y, ⟨h4, h5, h6⟩, rfl⟩
    refine ⟨by omega, by omega, by omega⟩

theorem minkRawE_points (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    ivPoints (minkRawE L R) =
      ((ivPoints L) ×ˢ (ivPoints R)).image (fun p => p.1 + p.2) := by
  ext z
  rw [Finset.mem_image, ivPoints_mem]
  constructor
  · rintro ⟨r, hr, hz⟩
    unfold minkRawE at hr
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    obtain ⟨x, hx, y, hy, rfl⟩ := (minkRun_mem p q (hL p hp) (hR q hq) z).mp hz
    exact ⟨(x, y), Finset.mem_product.mpr
      ⟨(ivPoints_mem L x).mpr ⟨p, hp, hx⟩, (ivPoints_mem R y).mpr ⟨q, hq, hy⟩⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨p, hp, hxp⟩ := (ivPoints_mem L x).mp hx
    obtain ⟨q, hq, hyq⟩ := (ivPoints_mem R y).mp hy
    refine ⟨minkRunE p q, ?_, ?_⟩
    · unfold minkRawE
      exact List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨q, hq, rfl⟩⟩
    · exact (minkRun_mem p q (hL p hp) (hR q hq) _).mpr ⟨x, hxp, y, hyq, rfl⟩

theorem minkE_eq (L R : IvList) (hL : ValidIvE L) (hR : ValidIvE R) :
    minkE L R = mink L R := by
  unfold minkE mink
  exact normalizeE_eq_points _ (minkRawE_valid L R hL hR) _ (minkRawE_points L R hL hR)


/-! ### 105.7. La lista vuota è normale -/

theorem normal_nil : Normal [] := by
  unfold Normal
  have h0 : ivPoints ([] : IvList) = ∅ := rfl
  rw [h0]
  symm
  apply List.eq_nil_of_length_eq_zero
  rw [ivCanon_length]
  simp [ivStarts]

/-! ### 105.8. Regole P2 e P3 sugli estremi -/

def ivP2ConfigE
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) : IvList :=
  if degree4AnglesB
      kl_u kl_v kr_u kr_v
      uv.1.1 uv.1.2 uv.2.1 uv.2.2 = true then
    interE
      (shiftE L (-(kl_u * uv.1.1 + kl_v * uv.2.1)))
      (shiftE R (kr_u * uv.1.2 + kr_v * uv.2.2))
  else []

def ivUnionManyE : List IvList → IvList
  | [] => normalizeE []
  | L :: ls => unionE L (ivUnionManyE ls)

def ivP2OrderE
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList) : IvList :=
  ivUnionManyE
    (angleConfigsL.map (ivP2ConfigE kl_u kl_v kr_u kr_v L R))

def ivP2E
    (kl_u kl_v kr_u kr_v : ℤ)
    (L R : IvList) : IvList :=
  unionE
    (ivP2OrderE kl_u kl_v kr_u kr_v L R)
    (ivP2OrderE kr_u kr_v kl_u kl_v R L)

def ivP3OrderE (L C R : IvList) : IvList :=
  interE (interE (shiftE L (-4)) C) (shiftE R 4)

def ivP3E (L C R : IvList) : IvList :=
  ivUnionManyE
    [ ivP3OrderE L C R, ivP3OrderE L R C,
      ivP3OrderE C L R, ivP3OrderE C R L,
      ivP3OrderE R L C, ivP3OrderE R C L ]

/-! ### 105.9. Algoritmo evalE (solo operazioni sugli estremi) -/

mutual

def evalE : SPTree → IvList
  | .Q len =>
      normalizeE
        [(-(2 * ((len - 1 : ℕ) : ℤ)), 2 * ((len - 1 : ℕ) : ℤ))]
  | .S children =>
      evalListE children
  | .P2 kl_u kl_v kr_u kr_v l r =>
      ivP2E kl_u kl_v kr_u kr_v (evalE l) (evalE r)
  | .P3 l c r =>
      ivP3E (evalE l) (evalE c) (evalE r)

def evalListE : List SPTree → IvList
  | [] =>
      normalizeE [(0, 0)]
  | t :: ts =>
      minkE (evalE t) (evalListE ts)

end

/-! ### 105.10. Equivalenza delle regole -/

theorem ivP2ConfigE_eq
    (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList)
    (hL : ValidIvE L) (hR : ValidIvE R)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) :
    ivP2ConfigE kl_u kl_v kr_u kr_v L R uv =
      ivP2Config kl_u kl_v kr_u kr_v L R uv := by
  unfold ivP2ConfigE ivP2Config
  split_ifs
  · rw [interE_canon _ _ (shiftE_valid L _ hL) (shiftE_valid R _ hR)]
    unfold inter
    rw [shiftE_points, shiftE_points, shift_points, shift_points]
  · rfl

theorem ivP2Config_normal
    (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) :
    Normal (ivP2Config kl_u kl_v kr_u kr_v L R uv) := by
  unfold ivP2Config
  split_ifs
  · exact inter_normal _ _
  · exact normal_nil

theorem ivUnionManyE_eq (ls : List IvList)
    (h : ∀ X ∈ ls, Normal X) :
    ivUnionManyE ls = ivUnionMany ls := by
  induction ls with
  | nil =>
      show normalizeE [] = normalize []
      rw [normalizeE_eq [] valid_nil]
      rfl
  | cons X ls ih =>
      show unionE X (ivUnionManyE ls) = union X (ivUnionMany ls)
      rw [ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY))]
      exact unionE_eq _ _
        (normal_valid X (h X List.mem_cons_self))
        (normal_valid _ (ivUnionMany_normal ls))

theorem ivP2OrderE_eq
    (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList)
    (hL : ValidIvE L) (hR : ValidIvE R) :
    ivP2OrderE kl_u kl_v kr_u kr_v L R =
      ivP2Order kl_u kl_v kr_u kr_v L R := by
  unfold ivP2OrderE ivP2Order
  have hmap :
      angleConfigsL.map (ivP2ConfigE kl_u kl_v kr_u kr_v L R) =
      angleConfigsL.map (ivP2Config kl_u kl_v kr_u kr_v L R) :=
    List.map_congr_left (fun uv _ => ivP2ConfigE_eq _ _ _ _ L R hL hR uv)
  rw [hmap]
  apply ivUnionManyE_eq
  intro X hX
  obtain ⟨uv, _, rfl⟩ := List.mem_map.mp hX
  exact ivP2Config_normal _ _ _ _ _ _ _

theorem ivP2E_eq
    (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList)
    (hL : ValidIvE L) (hR : ValidIvE R) :
    ivP2E kl_u kl_v kr_u kr_v L R =
      ivP2 kl_u kl_v kr_u kr_v L R := by
  unfold ivP2E ivP2
  rw [ivP2OrderE_eq _ _ _ _ L R hL hR, ivP2OrderE_eq _ _ _ _ R L hR hL]
  exact unionE_eq _ _
    (normal_valid _ (ivP2Order_normal _ _ _ _ _ _))
    (normal_valid _ (ivP2Order_normal _ _ _ _ _ _))

theorem ivP3OrderE_eq (L C R : IvList)
    (hL : ValidIvE L) (hC : ValidIvE C) (hR : ValidIvE R) :
    ivP3OrderE L C R = ivP3Order L C R := by
  unfold ivP3OrderE ivP3Order
  have h1 := interE_canon _ _ (shiftE_valid L (-4) hL) hC
  have hv : ValidIvE (interE (shiftE L (-4)) C) := by
    rw [h1]; exact ivCanon_valid _
  rw [interE_canon _ _ hv (shiftE_valid R 4 hR), h1]
  unfold inter
  rw [ivPoints_canon, ivPoints_canon, shiftE_points, shiftE_points,
    shift_points, shift_points]

theorem ivP3E_eq (L C R : IvList)
    (hL : ValidIvE L) (hC : ValidIvE C) (hR : ValidIvE R) :
    ivP3E L C R = ivP3 L C R := by
  unfold ivP3E ivP3
  rw [ivP3OrderE_eq L C R hL hC hR, ivP3OrderE_eq L R C hL hR hC,
    ivP3OrderE_eq C L R hC hL hR, ivP3OrderE_eq C R L hC hR hL,
    ivP3OrderE_eq R L C hR hL hC, ivP3OrderE_eq R C L hR hC hL]
  apply ivUnionManyE_eq
  intro X hX
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ivP3Order_normal _ _ _

/-! ### 105.11. T6a'_3 — evalE calcola esattamente eval -/

mutual

theorem T6a'_3 (t : SPTree) : evalE t = eval t := by
  cases t with
  | Q len =>
      show normalizeE _ = normalize _
      rw [normalizeE_eq _ (valid_band _ (by positivity))]
      rfl
  | S children =>
      exact evalListE_eq children
  | P2 kl_u kl_v kr_u kr_v l r =>
      show ivP2E kl_u kl_v kr_u kr_v (evalE l) (evalE r) =
        ivP2 kl_u kl_v kr_u kr_v (eval l) (eval r)
      rw [T6a'_3 l, T6a'_3 r]
      exact ivP2E_eq _ _ _ _ _ _
        (normal_valid _ (eval_normal l)) (normal_valid _ (eval_normal r))
  | P3 l c r =>
      show ivP3E (evalE l) (evalE c) (evalE r) =
        ivP3 (eval l) (eval c) (eval r)
      rw [T6a'_3 l, T6a'_3 c, T6a'_3 r]
      exact ivP3E_eq _ _ _
        (normal_valid _ (eval_normal l)) (normal_valid _ (eval_normal c))
        (normal_valid _ (eval_normal r))

theorem evalListE_eq (ts : List SPTree) : evalListE ts = evalList ts := by
  cases ts with
  | nil =>
      show normalizeE [(0, 0)] = normalize [(0, 0)]
      have hv : ValidIvE [((0 : ℤ), (0 : ℤ))] := by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact ⟨le_refl _, by norm_num⟩
      rw [normalizeE_eq _ hv]
      rfl
  | cons t ts =>
      show minkE (evalE t) (evalListE ts) = mink (eval t) (evalList ts)
      rw [T6a'_3 t, evalListE_eq ts]
      exact minkE_eq _ _
        (normal_valid _ (eval_normal t)) (normal_valid _ (evalList_normal ts))

end

/-! ### 105.12. T6a'_4 — Proprietà di evalE -/

theorem T6a'_4 (t : SPTree) (hwf : WF t) :
    denote (evalE t) = Sigma t ∧
    Normal (evalE t) ∧
    (evalE t).length = pieces2 (Sigma t) ∧
    (evalE t).length ≤ 36 ^ (2 * heavyP t) := by
  rw [T6a'_3 t]
  exact ⟨T6a_1 t, (T6a_2 t).1, (T6a_2 t).2, T6a_3 t hwf⟩

#eval evalE (.P2 2 2 2 2 (.Q 3) (.Q 2))

#print axioms T6a'_3
#print axioms T6a'_4


/-!
## 106. Tappa 6b — Modello di costo e bound per nodo

Modello di costo esplicito: ogni funzione `c…` conta i passi elementari
(confronti, accessi a una coppia, celle di lista visitate) dell'operazione
omonima `…E`, seguendone la struttura ricorsiva.
Il merge sort su n elementi è contato n² + 1 (maggiorante di n log n).
-/

/-! ### 106.1. Costo di normalizeE -/

/-- containsE scorre la lista. -/
def cContains (L : IvList) : ℕ := L.length + 1

/-- collectStartsE: per ogni coppia un isStartE (due containsE)
    e un test di appartenenza alla lista parziale. -/
def cCollect (L : IvList) : IvList → ℕ
  | [] => 1
  | _ :: ps => cCollect L ps + 2 * cContains L + (collectStartsE L ps).length + 1

def cSort (n : ℕ) : ℕ := n * n + 1

/-- endE: filtro (un containsE per elemento), map, minimo. -/
def cEnd (L : IvList) : ℕ := L.length * (2 * cContains L) + 2 * L.length + 1

def cNormalizeE (L : IvList) : ℕ :=
  cCollect L L + cSort (collectStartsE L L).length +
    (startsE L).length * (cEnd L + 1) + 1

/-! ### 106.2. Lunghezze -/

theorem collect_length (L M : IvList) : (collectStartsE L M).length ≤ M.length := by
  induction M with
  | nil => simp [collectStartsE]
  | cons p ps ih =>
      simp only [collectStartsE, List.length_cons]
      split_ifs <;> (try simp only [List.length_cons]) <;> omega

theorem startsE_length (L : IvList) : (startsE L).length ≤ L.length := by
  unfold startsE
  rw [List.length_mergeSort]
  exact collect_length L L

theorem normalizeE_length (L : IvList) : (normalizeE L).length ≤ L.length := by
  unfold normalizeE
  rw [List.length_map]
  exact startsE_length L

theorem cCollect_le (L M : IvList) :
    cCollect L M ≤ M.length * (2 * L.length + M.length + 4) + 1 := by
  induction M with
  | nil => simp [cCollect]
  | cons p ps ih =>
      have h := collect_length L ps
      simp only [cCollect, cContains, List.length_cons]
      nlinarith

theorem cNormalizeE_le (L : IvList) :
    cNormalizeE L ≤ 12 * (L.length + 1) ^ 3 := by
  have h1 := cCollect_le L L
  have h2 := collect_length L L
  have h3 := startsE_length L
  unfold cNormalizeE cSort cEnd cContains
  set n := L.length
  have h4 : (collectStartsE L L).length * (collectStartsE L L).length ≤ n * n :=
    Nat.mul_le_mul h2 h2
  have h5 : (startsE L).length * (n * (2 * (n + 1)) + 2 * n + 1 + 1) ≤
      n * (n * (2 * (n + 1)) + 2 * n + 1 + 1) := Nat.mul_le_mul_right _ h3
  nlinarith

/-! ### 106.3. Costo delle operazioni -/

def cShiftE (L : IvList) : ℕ := L.length + 1

def cUnionE (L R : IvList) : ℕ := L.length + R.length + 1 + cNormalizeE (L ++ R)

def cInterE (L R : IvList) : ℕ :=
  L.length * R.length + 1 + cNormalizeE (interRawE L R)

def cMinkE (L R : IvList) : ℕ :=
  L.length * R.length + 1 + cNormalizeE (minkRawE L R)

theorem interRunE_length (p q : ℤ × ℤ) : (interRunE p q).length ≤ 1 := by
  unfold interRunE
  dsimp only
  split_ifs <;> simp

theorem flatMap_interRunE_length (p : ℤ × ℤ) (R : IvList) :
    (R.flatMap (fun q => interRunE p q)).length ≤ R.length := by
  induction R with
  | nil => simp
  | cons q qs ihq =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := interRunE_length p q
      omega

theorem interRawE_length (L R : IvList) :
    (interRawE L R).length ≤ L.length * R.length := by
  induction L with
  | nil => simp [interRawE]
  | cons p ps ih =>
      have hR := flatMap_interRunE_length p R
      have : interRawE (p :: ps) R =
          R.flatMap (fun q => interRunE p q) ++ interRawE ps R := by
        simp [interRawE]
      rw [this, List.length_append, List.length_cons]
      nlinarith

theorem minkRawE_length (L R : IvList) :
    (minkRawE L R).length = L.length * R.length := by
  induction L with
  | nil => simp [minkRawE]
  | cons p ps ih =>
      have : minkRawE (p :: ps) R =
          R.map (fun q => minkRunE p q) ++ minkRawE ps R := by
        simp [minkRawE]
      rw [this, List.length_append, List.length_map, ih, List.length_cons]
      ring

theorem shiftE_length (L : IvList) (d : ℤ) : (shiftE L d).length = L.length := by
  simp [shiftE]

theorem unionE_length (L R : IvList) :
    (unionE L R).length ≤ L.length + R.length := by
  unfold unionE
  have := normalizeE_length (L ++ R)
  simpa using this

theorem interE_length (L R : IvList) :
    (interE L R).length ≤ L.length * R.length :=
  (normalizeE_length _).trans (interRawE_length L R)

theorem minkE_length (L R : IvList) :
    (minkE L R).length ≤ L.length * R.length := by
  have := normalizeE_length (minkRawE L R)
  rw [minkRawE_length] at this
  exact this

theorem cUnionE_le (L R : IvList) :
    cUnionE L R ≤ 13 * (L.length + R.length + 1) ^ 3 := by
  have h := cNormalizeE_le (L ++ R)
  rw [List.length_append] at h
  unfold cUnionE
  have : L.length + R.length + 1 ≤ (L.length + R.length + 1) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  omega

theorem cInterE_le (L R : IvList) :
    cInterE L R ≤ 13 * (L.length * R.length + 1) ^ 3 := by
  have h := cNormalizeE_le (interRawE L R)
  have hl := interRawE_length L R
  have h2 : (interRawE L R).length + 1 ≤ L.length * R.length + 1 := by omega
  have h3 : ((interRawE L R).length + 1) ^ 3 ≤ (L.length * R.length + 1) ^ 3 :=
    Nat.pow_le_pow_left h2 3
  have : L.length * R.length + 1 ≤ (L.length * R.length + 1) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  unfold cInterE
  omega

theorem cMinkE_le (L R : IvList) :
    cMinkE L R ≤ 13 * (L.length * R.length + 1) ^ 3 := by
  have h := cNormalizeE_le (minkRawE L R)
  rw [minkRawE_length] at h
  have : L.length * R.length + 1 ≤ (L.length * R.length + 1) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  unfold cMinkE
  omega


/-! ### 106.4. Costo delle regole P2, P3 e del passo S -/

def cP2ConfigE (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList)
    (uv : (ℤ × ℤ) × (ℤ × ℤ)) : ℕ :=
  if degree4AnglesB kl_u kl_v kr_u kr_v
      uv.1.1 uv.1.2 uv.2.1 uv.2.2 = true then
    cShiftE L + cShiftE R +
      cInterE (shiftE L (-(kl_u * uv.1.1 + kl_v * uv.2.1)))
        (shiftE R (kr_u * uv.1.2 + kr_v * uv.2.2)) + 1
  else 1

def cUnionManyE : List IvList → ℕ
  | [] => cNormalizeE []
  | X :: ls => cUnionManyE ls + cUnionE X (ivUnionManyE ls)

def cP2OrderE (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList) : ℕ :=
  (angleConfigsL.map (cP2ConfigE kl_u kl_v kr_u kr_v L R)).sum +
    cUnionManyE (angleConfigsL.map (ivP2ConfigE kl_u kl_v kr_u kr_v L R))

def cP2E (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList) : ℕ :=
  cP2OrderE kl_u kl_v kr_u kr_v L R +
    cP2OrderE kr_u kr_v kl_u kl_v R L +
    cUnionE (ivP2OrderE kl_u kl_v kr_u kr_v L R)
      (ivP2OrderE kr_u kr_v kl_u kl_v R L)

def cP3OrderE (L C R : IvList) : ℕ :=
  cShiftE L + cShiftE R + cInterE (shiftE L (-4)) C +
    cInterE (interE (shiftE L (-4)) C) (shiftE R 4)

def cP3E (L C R : IvList) : ℕ :=
  cP3OrderE L C R + cP3OrderE L R C + cP3OrderE C L R +
    cP3OrderE C R L + cP3OrderE R L C + cP3OrderE R C L +
    cUnionManyE
      [ ivP3OrderE L C R, ivP3OrderE L R C,
        ivP3OrderE C L R, ivP3OrderE C R L,
        ivP3OrderE R L C, ivP3OrderE R C L ]

/-! ### 106.5. Costo totale di evalE -/

mutual

def costE : SPTree → ℕ
  | .Q len =>
      cNormalizeE
        [(-(2 * ((len - 1 : ℕ) : ℤ)), 2 * ((len - 1 : ℕ) : ℤ))] + 1
  | .S children =>
      costListE children
  | .P2 kl_u kl_v kr_u kr_v l r =>
      costE l + costE r + cP2E kl_u kl_v kr_u kr_v (evalE l) (evalE r)
  | .P3 l c r =>
      costE l + costE c + costE r + cP3E (evalE l) (evalE c) (evalE r)

def costListE : List SPTree → ℕ
  | [] =>
      cNormalizeE [(0, 0)] + 1
  | t :: ts =>
      costE t + costListE ts + cMinkE (evalE t) (evalListE ts)

end

/- Dimensione: nodi dell'albero più celle delle liste di figli. -/
mutual

def sizeT : SPTree → ℕ
  | .Q _ => 1
  | .S children => sizeL children
  | .P2 _ _ _ _ l r => sizeT l + sizeT r + 1
  | .P3 l c r => sizeT l + sizeT c + sizeT r + 1

def sizeL : List SPTree → ℕ
  | [] => 1
  | t :: ts => sizeT t + sizeL ts + 1

end

/-! ### 106.6. Bound locali in funzione di N -/

/-- Bound locale uniforme. -/
def locB (N : ℕ) : ℕ := 3000000 * (N + 1) ^ 9

theorem locB_mono {N M : ℕ} (h : N ≤ M) : locB N ≤ locB M := by
  unfold locB
  have : (N + 1) ^ 9 ≤ (M + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  omega

theorem cube_mono {a b : ℕ} (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left h 3

theorem unionMany_bound (M : ℕ) (ls : List IvList)
    (h : ∀ X ∈ ls, X.length ≤ M) :
    (ivUnionManyE ls).length ≤ ls.length * M ∧
    cUnionManyE ls ≤ (ls.length + 1) * (13 * ((ls.length + 1) * (M + 1)) ^ 3) := by
  induction ls with
  | nil =>
      refine ⟨?_, ?_⟩
      · have := normalizeE_length ([] : IvList)
        simp only [ivUnionManyE, List.length_nil] at this ⊢
        omega
      · have h0 := cNormalizeE_le ([] : IvList)
        have h1 : 1 ≤ (1 * (M + 1)) ^ 3 := Nat.one_le_pow _ _ (by omega)
        simp only [cUnionManyE, List.length_nil] at h0 ⊢
        nlinarith
  | cons X ls ih =>
      obtain ⟨ih1, ih2⟩ := ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY))
      have hX := h X List.mem_cons_self
      set m := ls.length
      have hU := unionE_length X (ivUnionManyE ls)
      have hc := cUnionE_le X (ivUnionManyE ls)
      refine ⟨?_, ?_⟩
      · show (unionE X (ivUnionManyE ls)).length ≤ (m + 1) * M
        nlinarith
      · show cUnionManyE ls + cUnionE X (ivUnionManyE ls) ≤
          (m + 1 + 1) * (13 * ((m + 1 + 1) * (M + 1)) ^ 3)
        have e1 : X.length + (ivUnionManyE ls).length + 1 ≤ (m + 2) * (M + 1) := by
          nlinarith
        have e2 : (m + 1) * (M + 1) ≤ (m + 2) * (M + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have f1 := cube_mono e1
        have f2 := cube_mono e2
        have g : (m + 1) * (13 * ((m + 1) * (M + 1)) ^ 3) ≤
            (m + 1) * (13 * ((m + 2) * (M + 1)) ^ 3) :=
          Nat.mul_le_mul_left _ (by omega)
        nlinarith

theorem cP2ConfigE_bound (N : ℕ) (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList)
    (hL : L.length ≤ N) (hR : R.length ≤ N) (uv : (ℤ × ℤ) × (ℤ × ℤ)) :
    (ivP2ConfigE kl_u kl_v kr_u kr_v L R uv).length ≤ N * N ∧
    cP2ConfigE kl_u kl_v kr_u kr_v L R uv ≤ 16 * ((N + 1) ^ 2) ^ 3 := by
  have hX : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX3 : (N + 1) ^ 2 ≤ ((N + 1) ^ 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold ivP2ConfigE cP2ConfigE
  split_ifs
  · refine ⟨?_, ?_⟩
    · have := interE_length (shiftE L (-(kl_u * uv.1.1 + kl_v * uv.2.1)))
        (shiftE R (kr_u * uv.1.2 + kr_v * uv.2.2))
      rw [shiftE_length, shiftE_length] at this
      exact this.trans (Nat.mul_le_mul hL hR)
    · have hc := cInterE_le (shiftE L (-(kl_u * uv.1.1 + kl_v * uv.2.1)))
        (shiftE R (kr_u * uv.1.2 + kr_v * uv.2.2))
      rw [shiftE_length, shiftE_length] at hc
      have e : L.length * R.length + 1 ≤ (N + 1) ^ 2 := by
        have := Nat.mul_le_mul hL hR
        nlinarith
      have f := cube_mono e
      unfold cShiftE
      nlinarith
  · exact ⟨by simp, by omega⟩

theorem angleConfigsL_length : angleConfigsL.length = 9 := by decide

theorem sum_map_le {α : Type*} (l : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ l, f x ≤ B) : (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := h a List.mem_cons_self
      have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      nlinarith

theorem cP2OrderE_bound (N : ℕ) (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList)
    (hL : L.length ≤ N) (hR : R.length ≤ N) :
    (ivP2OrderE kl_u kl_v kr_u kr_v L R).length ≤ 9 * (N + 1) ^ 2 ∧
    cP2OrderE kl_u kl_v kr_u kr_v L R ≤ 1100000 * ((N + 1) ^ 2) ^ 3 := by
  set X := (N + 1) ^ 2 with hXdef
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hNN : N * N ≤ X := by rw [hXdef]; nlinarith
  have hb := fun uv => cP2ConfigE_bound N kl_u kl_v kr_u kr_v L R hL hR uv
  have hU := unionMany_bound (N * N)
    (angleConfigsL.map (ivP2ConfigE kl_u kl_v kr_u kr_v L R)) (by
      intro Y hY
      obtain ⟨uv, _, rfl⟩ := List.mem_map.mp hY
      exact (hb uv).1)
  rw [List.length_map, angleConfigsL_length] at hU
  have hs := sum_map_le angleConfigsL (cP2ConfigE kl_u kl_v kr_u kr_v L R)
    (16 * X ^ 3) (fun uv _ => (hb uv).2)
  rw [angleConfigsL_length] at hs
  refine ⟨?_, ?_⟩
  · unfold ivP2OrderE
    nlinarith [hU.1]
  · unfold cP2OrderE
    have e : (9 + 1) * (N * N + 1) ≤ 20 * X := by nlinarith
    have f := cube_mono e
    have g : (20 * X) ^ 3 = 8000 * X ^ 3 := by ring
    nlinarith [hU.2]

theorem cP2E_bound (N : ℕ) (kl_u kl_v kr_u kr_v : ℤ) (L R : IvList)
    (hL : L.length ≤ N) (hR : R.length ≤ N) :
    cP2E kl_u kl_v kr_u kr_v L R ≤ locB N := by
  set X := (N + 1) ^ 2 with hXdef
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have h1 := cP2OrderE_bound N kl_u kl_v kr_u kr_v L R hL hR
  have h2 := cP2OrderE_bound N kr_u kr_v kl_u kl_v R L hR hL
  have hu := cUnionE_le (ivP2OrderE kl_u kl_v kr_u kr_v L R)
    (ivP2OrderE kr_u kr_v kl_u kl_v R L)
  have e : (ivP2OrderE kl_u kl_v kr_u kr_v L R).length +
      (ivP2OrderE kr_u kr_v kl_u kl_v R L).length + 1 ≤ 19 * X := by
    rw [← hXdef] at h1 h2; omega
  have f := cube_mono e
  have g : (19 * X) ^ 3 = 6859 * X ^ 3 := by ring
  have hpow : X ^ 3 ≤ (N + 1) ^ 9 := by
    rw [hXdef, ← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold cP2E locB
  rw [← hXdef] at h1 h2
  nlinarith [h1.2, h2.2]

theorem cP3OrderE_bound (N : ℕ) (L C R : IvList)
    (hL : L.length ≤ N) (hC : C.length ≤ N) (hR : R.length ≤ N) :
    (ivP3OrderE L C R).length ≤ (N + 1) ^ 3 ∧
    cP3OrderE L C R ≤ 30 * ((N + 1) ^ 3) ^ 3 := by
  set Y := (N + 1) ^ 3 with hYdef
  have hY : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
  have hi := interE_length (shiftE L (-4)) C
  rw [shiftE_length] at hi
  have hLC : L.length * C.length ≤ N * N := Nat.mul_le_mul hL hC
  have ho := interE_length (interE (shiftE L (-4)) C) (shiftE R 4)
  rw [shiftE_length] at ho
  have hNNN : N * N * N + 1 ≤ Y := by rw [hYdef]; nlinarith
  have hNN : N * N + 1 ≤ Y := by rw [hYdef]; nlinarith
  refine ⟨?_, ?_⟩
  · unfold ivP3OrderE
    have : (interE (shiftE L (-4)) C).length * R.length ≤ N * N * N :=
      Nat.mul_le_mul (hi.trans hLC) hR
    omega
  · have c1 := cInterE_le (shiftE L (-4)) C
    have c2 := cInterE_le (interE (shiftE L (-4)) C) (shiftE R 4)
    rw [shiftE_length] at c1 c2
    have e1 : L.length * C.length + 1 ≤ Y := by omega
    have e2 : (interE (shiftE L (-4)) C).length * R.length + 1 ≤ Y := by
      have : (interE (shiftE L (-4)) C).length * R.length ≤ N * N * N :=
        Nat.mul_le_mul (hi.trans hLC) hR
      omega
    have f1 := cube_mono e1
    have f2 := cube_mono e2
    have hY3 : Y ≤ Y ^ 3 := Nat.le_self_pow (by norm_num) _
    have hNY : N + 1 ≤ Y := by rw [hYdef]; exact Nat.le_self_pow (by norm_num) _
    unfold cP3OrderE cShiftE
    omega

theorem cP3E_bound (N : ℕ) (L C R : IvList)
    (hL : L.length ≤ N) (hC : C.length ≤ N) (hR : R.length ≤ N) :
    cP3E L C R ≤ locB N := by
  set Y := (N + 1) ^ 3 with hYdef
  have hY : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
  have b1 := cP3OrderE_bound N L C R hL hC hR
  have b2 := cP3OrderE_bound N L R C hL hR hC
  have b3 := cP3OrderE_bound N C L R hC hL hR
  have b4 := cP3OrderE_bound N C R L hC hR hL
  have b5 := cP3OrderE_bound N R L C hR hL hC
  have b6 := cP3OrderE_bound N R C L hR hC hL
  rw [← hYdef] at b1 b2 b3 b4 b5 b6
  have hU := unionMany_bound Y
    [ ivP3OrderE L C R, ivP3OrderE L R C,
      ivP3OrderE C L R, ivP3OrderE C R L,
      ivP3OrderE R L C, ivP3OrderE R C L ] (by
      intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
      · exact b1.1
      · exact b2.1
      · exact b3.1
      · exact b4.1
      · exact b5.1
      · exact b6.1)
  simp only [List.length_cons, List.length_nil] at hU
  have e : (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * (Y + 1) ≤ 14 * Y := by omega
  have f := cube_mono e
  have g : (14 * Y) ^ 3 = 2744 * Y ^ 3 := by ring
  have hpow : Y ^ 3 = (N + 1) ^ 9 := by rw [hYdef, ← pow_mul]
  unfold cP3E locB
  nlinarith [hU.2]

theorem cMinkE_bound (N : ℕ) (L R : IvList)
    (hL : L.length ≤ N) (hR : R.length ≤ N) :
    cMinkE L R ≤ locB N := by
  have hc := cMinkE_le L R
  have e : L.length * R.length + 1 ≤ (N + 1) ^ 2 := by
    have := Nat.mul_le_mul hL hR
    nlinarith
  have f := cube_mono e
  have hpow : ((N + 1) ^ 2) ^ 3 ≤ (N + 1) ^ 9 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold locB
  omega


/-! ### 106.7. T6b — Costo totale -/

theorem len_evalE (t : SPTree) (hwf : WF t) (H : ℕ) (hH : heavyP t ≤ H) :
    (evalE t).length ≤ 36 ^ (2 * H) :=
  ((T6a'_4 t hwf).2.2.2).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem locB_pos (N : ℕ) : 100 ≤ locB N := by
  unfold locB
  have : 1 ≤ (N + 1) ^ 9 := Nat.one_le_pow _ _ (by omega)
  omega

mutual

theorem T6b_tree (t : SPTree) (H : ℕ) (hH : heavyP t ≤ H) (hwf : WF t) :
    costE t ≤ sizeT t * locB (36 ^ (2 * H)) := by
  cases t with
  | Q len =>
      have h := cNormalizeE_le
        [(-(2 * ((len - 1 : ℕ) : ℤ)), 2 * ((len - 1 : ℕ) : ℤ))]
      have hp := locB_pos (36 ^ (2 * H))
      simp only [List.length_cons, List.length_nil] at h
      show cNormalizeE _ + 1 ≤ 1 * locB (36 ^ (2 * H))
      omega
  | S children =>
      exact T6b_list children H hH hwf
  | P2 kl_u kl_v kr_u kr_v l r =>
      obtain ⟨hwl, hwr, _⟩ := hwf
      have hh : heavyP l + heavyP r ≤ H := by
        have : heavyP (.P2 kl_u kl_v kr_u kr_v l r) =
            heavyP l + heavyP r +
              (if AllKTwo kl_u kl_v kr_u kr_v then 0 else 1) := rfl
        omega
      have il := T6b_tree l H (by omega) hwl
      have ir := T6b_tree r H (by omega) hwr
      have hc := cP2E_bound (36 ^ (2 * H)) kl_u kl_v kr_u kr_v (evalE l) (evalE r)
        (len_evalE l hwl H (by omega)) (len_evalE r hwr H (by omega))
      show costE l + costE r + cP2E kl_u kl_v kr_u kr_v (evalE l) (evalE r) ≤
        (sizeT l + sizeT r + 1) * locB (36 ^ (2 * H))
      nlinarith
  | P3 l c r =>
      obtain ⟨hwl, hwc, hwr⟩ := hwf
      have hh : heavyP l + heavyP c + heavyP r + 1 ≤ H := hH
      have il := T6b_tree l H (by omega) hwl
      have ic := T6b_tree c H (by omega) hwc
      have ir := T6b_tree r H (by omega) hwr
      have hc := cP3E_bound (36 ^ (2 * H)) (evalE l) (evalE c) (evalE r)
        (len_evalE l hwl H (by omega)) (len_evalE c hwc H (by omega))
        (len_evalE r hwr H (by omega))
      show costE l + costE c + costE r + cP3E (evalE l) (evalE c) (evalE r) ≤
        (sizeT l + sizeT c + sizeT r + 1) * locB (36 ^ (2 * H))
      nlinarith

theorem T6b_list (ts : List SPTree) (H : ℕ) (hH : heavyPList ts ≤ H)
    (hwf : WFList ts) :
    costListE ts ≤ sizeL ts * locB (36 ^ (2 * H)) := by
  cases ts with
  | nil =>
      have h := cNormalizeE_le [((0 : ℤ), (0 : ℤ))]
      have hp := locB_pos (36 ^ (2 * H))
      simp only [List.length_cons, List.length_nil] at h
      show cNormalizeE _ + 1 ≤ 1 * locB (36 ^ (2 * H))
      omega
  | cons t ts =>
      obtain ⟨hwt, hwts⟩ := hwf
      have hh : heavyP t + heavyPList ts ≤ H := hH
      have it := T6b_tree t H (by omega) hwt
      have its := T6b_list ts H (by omega) hwts
      have hlt := len_evalE t hwt H (by omega)
      have hlts : (evalListE ts).length ≤ 36 ^ (2 * H) :=
        len_evalE (.S ts) hwts H (by show heavyPList ts ≤ H; omega)
      have hc := cMinkE_bound (36 ^ (2 * H)) (evalE t) (evalListE ts) hlt hlts
      show costE t + costListE ts + cMinkE (evalE t) (evalListE ts) ≤
        (sizeT t + sizeL ts + 1) * locB (36 ^ (2 * H))
      nlinarith

end

/--
T6b.

Il costo totale di evalE (nel modello di costo esplicito della sezione 106)
è al più  size(t) · 3·10⁶ · (36^(2·heavyP t) + 1)^9,
cioè lineare nella dimensione dell'albero e 2^{O(heavyP)} per nodo.
-/
theorem T6b (t : SPTree) (hwf : WF t) :
    costE t ≤ sizeT t * (3000000 * (36 ^ (2 * heavyP t) + 1) ^ 9) :=
  T6b_tree t (heavyP t) le_rfl hwf

#print axioms T6b


/-!
## 107. Tappa 6d — Chiusura alla radice

La radice è un arco (Q-nodo di riferimento). Per il modello
(Didimo–Kaufmann–Liotta–Ortali, citato) l'istanza è rettilinea
con quella radice se e solo se il resto dell'albero ammette
spiralità 4, cioè 8 nella scala raddoppiata.
-/

def rootTestE (t : SPTree) : Bool := containsE (evalE t) 8

def cRootTest (t : SPTree) : ℕ := costE t + cContains (evalE t)

/-- T6d_1: il test calcolato coincide con la condizione semantica. -/
theorem T6d_1 (t : SPTree) (hwf : WF t) :
    rootTestE t = true ↔ (8 : ℤ) ∈ Sigma t := by
  unfold rootTestE
  rw [containsE_iff, (T6a'_4 t hwf).1]

/-- T6d_2: costo del test completo. -/
theorem T6d_2 (t : SPTree) (hwf : WF t) :
    cRootTest t ≤ (sizeT t + 1) * (3000000 * (36 ^ (2 * heavyP t) + 1) ^ 9) := by
  have h1 := T6b t hwf
  have h2 := (T6a'_4 t hwf).2.2.2
  have h3 : 36 ^ (2 * heavyP t) + 1 ≤ (36 ^ (2 * heavyP t) + 1) ^ 9 :=
    Nat.le_self_pow (by norm_num) _
  unfold cRootTest cContains
  nlinarith

#eval rootTestE (.P2 2 2 2 2 (.Q 3) (.Q 2))
#eval rootTestE (.Q 5)

#print axioms T6d_1
#print axioms T6d_2


/-! ## 25. Controllo degli assiomi -/

#print axioms T1_1
#print axioms T1_2
#print axioms T1_3
#print axioms T2_0
#print axioms T2_1

end RectilinearSP
