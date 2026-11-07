import Core.M11

/-!
# M12（一）：一般的拥有关系与动态数组 `Vec<T>`

**问题**：M11（一）要求子格子比父格子早分配（`Ordered`），这只对“先有子格子再分配父格子”的构造成立。
往已有的格子里放进新的值时不成立：`Vec` 的 `push`（新元素可能比数组新）、
通过 `inout` 给堆里的位置整体赋值（`set((*b).a)`）。这里换成一般的无环条件：
存在一个“秩”，每个子格子的秩都小于父格子（`Ranked`）。

**动态数组**：数组的缓冲区是一个格子，它拥有每个元素的值里的格子（`Vec<Box<I64>>` 的每个元素一个）。
`push`：把一个值的格子挂到数组的格子下（`attach`）；`pop`：把最后一个元素的格子取下来交给变量（`detach`）；
扩容（`realloc`）只换地址，拥有关系不变；`get(v, i)` 是按借用读，不改拥有关系（锁由 M4 负责），
下标越界时 panic，不读内存。析构数组：逐个析构元素，再释放缓冲区（就是 M11 的递归析构）。

**`attach` 的条件**：数组不能在要放进去的值的子树里（`¬ Below`），否则成环、永远不会被释放。
编译器靠排他性保证：`push(v, x)` 里 `v` 是 `inout`、`x` 是 `sink`，同一个变量不能同时出现，
而 `v` 的位置在 `x` 的子树里，意味着两者的根是同一个变量。

**主定理** `scope_end`：从空堆出发经过分配、拆开、析构、`attach`、`detach`，作用域结束时析构所有根成功
（没有重复释放、一定结束），之后堆是空的（没有泄漏）。

**关键引理** `attach_inv`：挂接后重新取秩——被挂接的子树保持原来的秩，其余格子的秩整体抬高；
因为每个格子只有一个拥有者，子树外的格子不会拥有子树里的格子（`owner_below`）。
-/

namespace Core.M12
open Core.M11 (Cell Heap keys kids look del dropList look_some look_keys look_kids)

/-- 把格子 `l` 的子格子换成 `ns`。 -/
def setKids : Heap → Cell → List Cell → Heap
  | [], _, _ => []
  | (k, cs) :: h, l, ns => if k = l then (k, ns) :: h else (k, cs) :: setKids h l ns

/-- 秩：每个子格子的秩都小于父格子，所以拥有关系没有环。 -/
def Ranked (r : Cell → Nat) (h : Heap) : Prop :=
  ∀ p cs, (p, cs) ∈ h → ∀ c ∈ cs, r c < r p

structure Inv (h : Heap) (roots : List Cell) : Prop where
  nd   : (keys h).Nodup
  own  : (roots ++ kids h).Perm (keys h)
  rank : ∃ r : Cell → Nat, Ranked r h

/-- 从 `xs` 出发沿拥有关系能到的格子（`xs` 的子树）。 -/
inductive Below (h : Heap) (xs : List Cell) : Cell → Prop
  | root {c : Cell} : c ∈ xs → Below h xs c
  | step {p c : Cell} {cs : List Cell} : Below h xs p → (p, cs) ∈ h → c ∈ cs → Below h xs c

/-! ## 计数 -/

theorem count_pos : ∀ {c : Cell} {l : List Cell}, c ∈ l → 0 < l.count c
  | _, [], h => by simp at h
  | c, x :: l, h => by
    rcases List.mem_cons.1 h with e | h
    · subst e
      rw [List.count_cons]
      simp
    · have := count_pos h
      rw [List.count_cons]
      exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)

theorem count_zero : ∀ {a : Cell} {l : List Cell}, a ∉ l → l.count a = 0
  | _, [], _ => by simp
  | a, x :: l, h => by
    simp only [List.mem_cons, not_or] at h
    rw [List.count_cons, count_zero h.2]
    simp [Ne.symm h.1]

theorem count_le_one : ∀ {l : List Cell}, l.Nodup → ∀ a, l.count a ≤ 1
  | [], _, _ => by simp
  | x :: l, h, a => by
    rw [List.nodup_cons] at h
    rw [List.count_cons]
    by_cases e : x = a
    · subst e
      rw [count_zero h.1]
      simp
    · have := count_le_one h.2 a
      simpa [e] using this

/-! ## 堆的基本性质 -/

theorem look_mem : ∀ (h : Heap) (l : Cell) (cs : List Cell), look h l = some cs → (l, cs) ∈ h
  | [], _, _, e => by simp [look] at e
  | (k, ks) :: h, l, cs, e => by
    by_cases hk : k = l
    · simp [look, hk] at e
      subst hk
      subst e
      simp
    · simp [look, hk] at e
      exact List.mem_cons_of_mem _ (look_mem h l cs e)

theorem del_sub : ∀ (h : Heap) (l : Cell) (e : Cell × List Cell), e ∈ del h l → e ∈ h
  | [], _, _, he => by simp [del] at he
  | (k, ks) :: h, l, e, he => by
    by_cases hk : k = l
    · simp [del, hk] at he
      exact List.mem_cons_of_mem _ he
    · simp [del, hk] at he
      rcases he with he | he
      · rw [he]; simp
      · exact List.mem_cons_of_mem _ (del_sub h l e he)

theorem mem_kids : ∀ (h : Heap) (c : Cell), c ∈ kids h → ∃ p cs, (p, cs) ∈ h ∧ c ∈ cs
  | [], _, hc => by simp [kids] at hc
  | (k, ks) :: h, c, hc => by
    simp only [kids, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨k, ks, by simp, hc⟩
    · obtain ⟨p, cs, hm, hc⟩ := mem_kids h c hc
      exact ⟨p, cs, List.mem_cons_of_mem _ hm, hc⟩

theorem kids_of_mem : ∀ (h : Heap) (p : Cell) (cs : List Cell) (c : Cell), (p, cs) ∈ h → c ∈ cs →
    c ∈ kids h
  | [], _, _, _, he, _ => by simp at he
  | (k, ks) :: h, p, cs, c, he, hc => by
    simp only [kids, List.mem_append]
    rcases List.mem_cons.1 he with e | he
    · simp only [Prod.mk.injEq] at e
      exact Or.inl (e.2 ▸ hc)
    · exact Or.inr (kids_of_mem h p cs c he hc)

theorem keys_of_mem : ∀ (h : Heap) (p : Cell) (cs : List Cell), (p, cs) ∈ h → p ∈ keys h
  | [], _, _, he => by simp at he
  | (k, ks) :: h, p, cs, he => by
    simp only [keys, List.mem_cons]
    rcases List.mem_cons.1 he with e | he
    · simp only [Prod.mk.injEq] at e
      exact Or.inl e.1
    · exact Or.inr (keys_of_mem h p cs he)

/-- 两个不同的格子都拥有 `c`，则 `c` 在所有子格子里至少出现两次。 -/
theorem two_owners : ∀ (h : Heap) (p q c : Cell) (cs ds : List Cell), (p, cs) ∈ h → (q, ds) ∈ h →
    p ≠ q → c ∈ cs → c ∈ ds → 2 ≤ (kids h).count c
  | [], _, _, _, _, _, hp, _, _, _, _ => by simp at hp
  | (k, ks) :: h, p, q, c, cs, ds, hp, hq, hne, hc, hd => by
    simp only [kids, List.count_append]
    rcases List.mem_cons.1 hp with e1 | hp' <;> rcases List.mem_cons.1 hq with e2 | hq'
    · simp only [Prod.mk.injEq] at e1 e2
      exact absurd (e1.1.trans e2.1.symm) hne
    · simp only [Prod.mk.injEq] at e1
      have h1 : 0 < ks.count c := count_pos (e1.2 ▸ hc)
      have h2 : 0 < (kids h).count c := count_pos (kids_of_mem h q ds c hq' hd)
      omega
    · simp only [Prod.mk.injEq] at e2
      have h1 : 0 < ks.count c := count_pos (e2.2 ▸ hd)
      have h2 : 0 < (kids h).count c := count_pos (kids_of_mem h p cs c hp' hc)
      omega
    · have := two_owners h p q c cs ds hp' hq' hne hc hd
      omega

/-- 唯一拥有者：子树里的格子（不是子树的根时）的拥有者也在子树里。 -/
theorem owner_below {h : Heap} {xs rest : List Cell} (hnd : ((xs ++ rest) ++ kids h).Nodup)
    {p c : Cell} {cs : List Cell} (hp : (p, cs) ∈ h) (hc : c ∈ cs) (hb : Below h xs c) :
    Below h xs p := by
  have hcnt := count_le_one hnd c
  simp only [List.count_append] at hcnt
  cases hb with
  | root hx =>
    have h1 : 0 < xs.count c := count_pos hx
    have h2 : 0 < (kids h).count c := count_pos (kids_of_mem h p cs c hp hc)
    omega
  | @step q _ ds hb' hq hd =>
    by_cases e : q = p
    · subst e
      exact hb'
    · have := two_owners h q p c ds cs hq hp e hd hc
      omega

theorem keys_set : ∀ (h : Heap) (l : Cell) (ns : List Cell), keys (setKids h l ns) = keys h
  | [], _, _ => rfl
  | (k, ks) :: h, l, ns => by
    by_cases hk : k = l
    · simp [setKids, hk, keys]
    · simp [setKids, hk, keys, keys_set h l ns]

theorem kids_set : ∀ (h : Heap) (l : Cell) (ks ns : List Cell), look h l = some ks →
    (kids (setKids h l ns) ++ ks).Perm (kids h ++ ns)
  | [], _, _, _, e => by simp [look] at e
  | (k, ks0) :: h, l, ks, ns, e => by
    by_cases hk : k = l
    · simp [look, hk] at e
      subst e
      have : setKids ((k, ks0) :: h) l ns = (k, ns) :: h := by simp [setKids, hk]
      rw [this]
      exact List.perm_iff_count.2 (fun a => by simp only [kids, List.count_append]; omega)
    · simp [look, hk] at e
      have ih := kids_set h l ks ns e
      have : setKids ((k, ks0) :: h) l ns = (k, ks0) :: setKids h l ns := by simp [setKids, hk]
      rw [this]
      refine List.perm_iff_count.2 (fun a => ?_)
      have e1 := List.perm_iff_count.1 ih a
      simp only [kids, List.count_append] at e1 ⊢
      omega

theorem mem_set : ∀ (h : Heap) (l : Cell) (ns : List Cell) (e : Cell × List Cell),
    e ∈ setKids h l ns → e ∈ h ∨ e = (l, ns)
  | [], _, _, _, he => by simp [setKids] at he
  | (k, ks) :: h, l, ns, e, he => by
    by_cases hk : k = l
    · simp only [setKids, hk, ite_true, List.mem_cons] at he
      rcases he with he | he
      · exact Or.inr he
      · exact Or.inl (List.mem_cons_of_mem _ he)
    · simp only [setKids, hk, ite_false, List.mem_cons] at he
      rcases he with he | he
      · exact Or.inl (by rw [he]; simp)
      · rcases mem_set h l ns e he with he | he
        · exact Or.inl (List.mem_cons_of_mem _ he)
        · exact Or.inr he

theorem le_foldr_max (r : Cell → Nat) : ∀ (xs : List Cell) (c : Cell), c ∈ xs →
    r c ≤ xs.foldr (fun c m => max (r c) m) 0
  | [], _, hc => by simp at hc
  | x :: xs, c, hc => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hc with e | hc
    · subst e; exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max r xs c hc) (Nat.le_max_right _ _)

/-! ## 操作保持不变式 -/

/-- 分配新格子，把若干根移进去当子格子。新格子的秩比它的子格子都大。 -/
theorem alloc_inv (h : Heap) (l : Cell) (cs rest : List Cell) (hI : Inv h (cs ++ rest))
    (hl : l ∉ keys h) : Inv ((l, cs) :: h) (l :: rest) := by
  obtain ⟨r, hr⟩ := hI.rank
  have hsub : ∀ c, c ∈ (cs ++ rest) ++ kids h → c ∈ keys h := fun c hc => hI.own.subset hc
  refine ⟨?_, ?_, ?_⟩
  · show (l :: keys h).Nodup
    exact List.nodup_cons.2 ⟨hl, hI.nd⟩
  · show (l :: (rest ++ (cs ++ kids h))).Perm (l :: keys h)
    refine List.Perm.cons l ?_
    have q : (rest ++ (cs ++ kids h)).Perm (cs ++ rest ++ kids h) := by
      rw [← List.append_assoc]
      exact List.perm_append_comm.append_right _
    exact q.trans hI.own
  · obtain ⟨M, hM⟩ : ∃ M, ∀ c ∈ cs, r c < M :=
      ⟨cs.foldr (fun c m => max (r c) m) 0 + 1, fun c hc => Nat.lt_succ_of_le (le_foldr_max r cs c hc)⟩
    refine ⟨fun c => if c = l then M else r c, ?_⟩
    intro p ds he c hc
    have hcl : ∀ c, c ∈ keys h → c ≠ l := fun c hc e => hl (e ▸ hc)
    rcases List.mem_cons.1 he with e | he
    · simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      rw [e2] at hc
      have hck : c ∈ keys h := hsub c (by simp [hc])
      have := hM c hc
      try dsimp only
      rw [ite_eq_right (hcl c hck), ite_eq_left e1]
      omega
    · have hpk := keys_of_mem h p ds he
      have hck := hsub c (by simp [kids_of_mem h p ds c he hc])
      try dsimp only
      rw [ite_eq_right (hcl c hck), ite_eq_right (hcl p hpk)]
      exact hr p ds he c hc

/-- 按移动拆开一个根（或者析构时释放它）：秩不变。 -/
theorem unbox_inv (h : Heap) (l : Cell) (rest : List Cell) (hI : Inv h (l :: rest)) :
    ∃ cs, look h l = some cs ∧ Inv (del h l) (cs ++ rest) := by
  have hown : (l :: (rest ++ kids h)).Perm (keys h) := hI.own
  have hl : l ∈ keys h := hown.subset (by simp)
  obtain ⟨cs, hc⟩ := look_some h l hl
  have p1 := look_keys h l cs hc
  have p2 := look_kids h l cs hc
  obtain ⟨r, hr⟩ := hI.rank
  refine ⟨cs, hc, ⟨(p1.nodup_iff.1 hI.nd).of_cons, ?_, ⟨r, fun p ds he => hr p ds (del_sub h l _ he)⟩⟩⟩
  have q : (rest ++ kids h).Perm (keys (del h l)) := List.Perm.cons_inv (hown.trans p1)
  have q2 : (rest ++ (cs ++ kids (del h l))).Perm (keys (del h l)) := (p2.append_left rest).symm.trans q
  have q3 : (cs ++ rest ++ kids (del h l)).Perm (rest ++ (cs ++ kids (del h l))) := by
    rw [← List.append_assoc]
    exact List.perm_append_comm.append_right _
  exact q3.trans q2

/-- `push`：把根 `xs` 挂到格子 `k` 下（`k` 不在 `xs` 的子树里）。重新取秩。 -/
theorem attach_inv (h : Heap) (k : Cell) (ks xs rest : List Cell) (hI : Inv h (xs ++ rest))
    (hks : look h k = some ks) (hnb : ¬ Below h xs k) : Inv (setKids h k (ks ++ xs)) rest := by
  classical
  obtain ⟨r, hr⟩ := hI.rank
  have hnd : ((xs ++ rest) ++ kids h).Nodup := hI.own.nodup_iff.2 hI.nd
  have hkm := look_mem h k ks hks
  have p2 := kids_set h k ks (ks ++ xs) hks
  refine ⟨by rw [keys_set]; exact hI.nd, ?_, ?_⟩
  · rw [keys_set]
    refine List.perm_iff_count.2 (fun a => ?_)
    have e1 := List.perm_iff_count.1 hI.own a
    have e2 := List.perm_iff_count.1 p2 a
    simp only [List.count_append] at e1 e2 ⊢
    omega
  · obtain ⟨M, hM⟩ : ∃ M, ∀ c ∈ xs, r c < M :=
      ⟨xs.foldr (fun c m => max (r c) m) 0 + 1, fun c hc => Nat.lt_succ_of_le (le_foldr_max r xs c hc)⟩
    have old : ∀ p cs, (p, cs) ∈ h → ∀ c ∈ cs,
        (if Below h xs c then r c else r c + M) < (if Below h xs p then r p else r p + M) := by
      intro p cs he c hc
      have hrc := hr p cs he c hc
      by_cases hbp : Below h xs p
      · have hbc : Below h xs c := Below.step hbp he hc
        rw [ite_eq_left hbc, ite_eq_left hbp]
        exact hrc
      · have hbc : ¬ Below h xs c := fun hb => hbp (owner_below hnd he hc hb)
        rw [ite_eq_right hbc, ite_eq_right hbp]
        omega
    refine ⟨fun c => if Below h xs c then r c else r c + M, ?_⟩
    intro p cs he c hc
    rcases mem_set h k (ks ++ xs) (p, cs) he with he | he
    · exact old p cs he c hc
    · simp only [Prod.mk.injEq] at he
      obtain ⟨e1, e2⟩ := he
      rw [e2] at hc
      rw [e1]
      rcases List.mem_append.1 hc with hc | hc
      · exact old k ks hkm c hc
      · have hbc : Below h xs c := Below.root hc
        have := hM c hc
        try dsimp only
        rw [ite_eq_left hbc, ite_eq_right hnb]
        omega

/-- `pop`：把格子 `k` 的最后一部分子格子 `cs` 取下来交给变量。秩不变。 -/
theorem detach_inv (h : Heap) (k : Cell) (pre cs roots : List Cell) (hI : Inv h roots)
    (hks : look h k = some (pre ++ cs)) : Inv (setKids h k pre) (cs ++ roots) := by
  obtain ⟨r, hr⟩ := hI.rank
  have hkm := look_mem h k (pre ++ cs) hks
  have p2 := kids_set h k (pre ++ cs) pre hks
  refine ⟨by rw [keys_set]; exact hI.nd, ?_, ?_⟩
  · rw [keys_set]
    refine List.perm_iff_count.2 (fun a => ?_)
    have e1 := List.perm_iff_count.1 hI.own a
    have e2 := List.perm_iff_count.1 p2 a
    simp only [List.count_append] at e1 e2 ⊢
    omega
  · refine ⟨r, fun p ds he c hc => ?_⟩
    rcases mem_set h k pre (p, ds) he with he | he
    · exact hr p ds he c hc
    · simp only [Prod.mk.injEq] at he
      obtain ⟨e1, e2⟩ := he
      rw [e2] at hc
      rw [e1]
      exact hr k (pre ++ cs) hkm c (List.mem_append_left _ hc)

/-- 析构成功时，剩下的根仍然满足不变式。 -/
theorem drop_inv : ∀ (n : Nat) (h : Heap) (ls rest : List Cell) (h' : Heap), Inv h (ls ++ rest) →
    dropList n h ls = some h' → Inv h' rest
  | _, h, [], rest, h', hI, e => by
    simp [dropList] at e
    subst e
    exact hI
  | 0, _, _ :: _, _, _, _, e => by simp [dropList] at e
  | n + 1, h, l :: ls, rest, h', hI, e => by
    obtain ⟨cs, hc, hI2⟩ := unbox_inv h l (ls ++ rest) hI
    simp [dropList, hc] at e
    have hI3 : Inv (del h l) ((cs ++ ls) ++ rest) := by rw [List.append_assoc]; exact hI2
    exact drop_inv n (del h l) (cs ++ ls) rest h' hI3 e

/-- 燃料不少于格子数时，析构一定成功（一定结束、不会读到已释放的格子）。 -/
theorem drop_total : ∀ (n : Nat) (h : Heap) (ls rest : List Cell), Inv h (ls ++ rest) →
    (keys h).length ≤ n → ∃ h', dropList n h ls = some h'
  | _, h, [], _, _, _ => ⟨h, by simp [dropList]⟩
  | 0, h, l :: ls, rest, hI, hlen => by
    have hl : l ∈ keys h := hI.own.subset (by simp)
    have := List.length_pos_of_mem hl
    exact absurd hlen (by omega)
  | n + 1, h, l :: ls, rest, hI, hlen => by
    obtain ⟨cs, hc, hI2⟩ := unbox_inv h l (ls ++ rest) hI
    have hlen' : (keys (del h l)).length ≤ n := by
      have := (look_keys h l cs hc).length_eq
      simp at this
      omega
    have hI3 : Inv (del h l) ((cs ++ ls) ++ rest) := by rw [List.append_assoc]; exact hI2
    obtain ⟨h', e⟩ := drop_total n (del h l) (cs ++ ls) rest hI3 hlen'
    exact ⟨h', by simp [dropList, hc, e]⟩

theorem exists_max (r : Cell → Nat) : ∀ (l : List Cell), l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, r y ≤ r x
  | [], hne => absurd rfl hne
  | [x], _ => ⟨x, by simp, fun y hy => by simp at hy; subst hy; exact Nat.le_refl _⟩
  | x :: y :: l, _ => by
    obtain ⟨m, hm, hmax⟩ := exists_max r (y :: l) (by simp)
    by_cases hc : r x ≤ r m
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with e | hz
      · subst e; exact hc
      · exact hmax z hz
    · refine ⟨x, by simp, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with e | hz
      · subst e; exact Nat.le_refl _
      · exact Nat.le_trans (hmax z hz) (by omega)

/-- 没有根时堆是空的：秩最大的格子也必须有拥有者，而拥有者的秩更大，矛盾。 -/
theorem no_leak (h : Heap) (hI : Inv h []) : h = [] := by
  cases h with
  | nil => rfl
  | cons e t =>
    exfalso
    obtain ⟨r, hr⟩ := hI.rank
    have hne : keys (e :: t) ≠ [] := by
      obtain ⟨k, ks⟩ := e
      simp [keys]
    obtain ⟨m, hm, hmax⟩ := exists_max r (keys (e :: t)) hne
    have hk : m ∈ kids (e :: t) := hI.own.symm.subset hm
    obtain ⟨p, cs, hp, hc⟩ := mem_kids _ m hk
    have h1 := hr p cs hp m hc
    have h2 := hmax p (keys_of_mem _ p cs hp)
    omega

/-! ## 主定理 -/

/-- 从空堆出发能到达的状态：分配、拆开、析构一个根、`push`（`attach`）、`pop`（`detach`）、根的重新排列。 -/
inductive Reach : Heap → List Cell → Prop
  | empty : Reach [] []
  | alloc {h l cs rest} : Reach h (cs ++ rest) → l ∉ keys h → Reach ((l, cs) :: h) (l :: rest)
  | unbox {h l cs rest} : Reach h (l :: rest) → look h l = some cs → Reach (del h l) (cs ++ rest)
  | drop {h h' l rest n} : Reach h (l :: rest) → dropList n h [l] = some h' → Reach h' rest
  | attach {h k ks xs rest} : Reach h (xs ++ rest) → look h k = some ks → ¬ Below h xs k →
      Reach (setKids h k (ks ++ xs)) rest
  | detach {h k pre cs roots} : Reach h roots → look h k = some (pre ++ cs) →
      Reach (setKids h k pre) (cs ++ roots)
  | perm {h r r'} : Reach h r → r.Perm r' → Reach h r'

theorem reach_inv {h : Heap} {r : List Cell} (hr : Reach h r) : Inv h r := by
  induction hr with
  | empty => exact ⟨List.nodup_nil, List.Perm.refl _, ⟨fun _ => 0, fun _ _ he => by simp at he⟩⟩
  | @alloc h l cs rest _ hl ih => exact alloc_inv h l cs rest ih hl
  | @unbox h l cs rest _ hc ih =>
    obtain ⟨cs', hc', hI⟩ := unbox_inv h l rest ih
    rw [hc] at hc'
    cases hc'
    exact hI
  | @drop h h' l rest n _ e ih => exact drop_inv n h [l] rest h' ih e
  | @attach h k ks xs rest _ hks hnb ih => exact attach_inv h k ks xs rest ih hks hnb
  | @detach h k pre cs roots _ hks ih => exact detach_inv h k pre cs roots ih hks
  | @perm h r r' _ hp ih => exact ⟨ih.nd, (hp.symm.append_right _).trans ih.own, ih.rank⟩

/-- **主定理**：作用域结束时析构所有根，一定成功（没有重复释放、一定结束），并且之后堆是空的（没有泄漏）。 -/
theorem scope_end {h : Heap} {roots : List Cell} (hr : Reach h roots) :
    dropList (keys h).length h roots = some [] := by
  have hI' : Inv h (roots ++ []) := by rw [List.append_nil]; exact reach_inv hr
  obtain ⟨h', e⟩ := drop_total _ h roots [] hI' (Nat.le_refl _)
  have := no_leak h' (drop_inv _ h roots [] h' hI' e)
  rw [e, this]

/-! ## 例子

格子 5 是数组的缓冲区，7 是一个比数组新的 `Box`。 -/

/-- `push`：新的 `Box` 挂到数组下。M11 的 `Ordered` 不再成立，但析构数组照样释放全部。 -/
example : setKids [(7, []), (5, [])] 5 [7] = [(7, []), (5, [7])] := rfl
example : ¬ Core.M11.Ordered [(7, []), (5, [7])] := by simp [Core.M11.Ordered, keys]
example : dropList 2 [(7, []), (5, [7])] [5] = some [] := rfl

/-- `pop`：取下最后一个元素交给变量，数组和元素分别析构。 -/
example : setKids [(5, [1, 2]), (2, []), (1, [])] 5 [1] = [(5, [1]), (2, []), (1, [])] := rfl
example : dropList 3 [(5, [1]), (2, []), (1, [])] [2, 5] = some [] := rfl

/-- 把数组放进它自己（违反 `¬ Below`）：成环，永远不会被释放。 -/
example : dropList 1 (setKids [(5, [])] 5 [5]) [] = some [(5, [5])] := rfl

end Core.M12
