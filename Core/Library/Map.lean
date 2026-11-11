import Core.Library.Math

/-!
# `std.map` 的规格

`Map<K, V>` 按键从小到大存放键值对，键要实现 `math.Ord`（满足 `Library.Math` 的 `OrdLaws`）。
**模型**：键值对的列表，键严格递增（`Sorted`）。参考实现：
- `lookup k m`：键为 `k` 的值；
- `ins k v m`：放进 `(k, v)`；已有键 `k` 时替换它的值（旧值由 `insert` 返回，就是插入前的 `lookup k m`）；
- `del k m`：去掉键为 `k` 的一对（返回的值同样是删除前的 `lookup k m`）。

**定律**（都只依赖 `OrdLaws`）：
- `ins_sorted`、`del_sorted`：插入、删除之后键仍严格递增——所以没有重复的键，遍历按键的顺序；
- `lookup_ins`：插入后查得到刚放进的值；`lookup_ins_other`：别的键不受影响；
- `lookup_del`：删除后查不到（要用到有序：后面不会再有同一个键）；`lookup_del_other`：别的键不受影响。
-/

namespace Core.Library.Map
open Core.Library.Math (OrdLaws)

variable {α β : Type} (cmp : α → α → Int)

/-- 键严格递增：每个键都小于它后面的所有键。 -/
def Sorted : List (α × β) → Prop
  | [] => True
  | (k, _) :: rest => (∀ p ∈ rest, cmp k p.1 = -1) ∧ Sorted rest

def lookup (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: rest => if cmp k k' = 0 then some v else lookup k rest

def ins (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if cmp k k' = -1 then (k, v) :: (k', v') :: rest
    else if cmp k k' = 0 then (k, v) :: rest
    else (k', v') :: ins k v rest

def del (k : α) : List (α × β) → List (α × β)
  | [] => []
  | (k', v') :: rest => if cmp k k' = 0 then rest else (k', v') :: del k rest

variable {cmp}

theorem mem_ins {k : α} {v : β} : ∀ {m : List (α × β)} {p : α × β}, p ∈ ins cmp k v m → p = (k, v) ∨ p ∈ m
  | [], p, hp => by simp [ins] at hp; exact Or.inl hp
  | (k', v') :: rest, p, hp => by
    unfold ins at hp
    by_cases h1 : cmp k k' = -1
    · simp only [h1, ite_true, List.mem_cons] at hp
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (by simp [hp])
    · by_cases h2 : cmp k k' = 0
      · rw [ite_eq_right h1, ite_eq_left h2] at hp
        rcases List.mem_cons.1 hp with hp | hp
        · exact Or.inl hp
        · exact Or.inr (List.mem_cons_of_mem _ hp)
      · simp only [h1, h2, ite_false, List.mem_cons] at hp
        rcases hp with hp | hp
        · exact Or.inr (by simp [hp])
        · rcases mem_ins hp with e | e
          · exact Or.inl e
          · exact Or.inr (List.mem_cons_of_mem _ e)

theorem mem_del {k : α} : ∀ {m : List (α × β)} {p : α × β}, p ∈ del cmp k m → p ∈ m
  | [], p, hp => by simp [del] at hp
  | (k', v') :: rest, p, hp => by
    unfold del at hp
    by_cases h : cmp k k' = 0
    · simp only [h, ite_true] at hp
      exact List.mem_cons_of_mem _ hp
    · simp only [h, ite_false, List.mem_cons] at hp
      rcases hp with hp | hp
      · simp [hp]
      · exact List.mem_cons_of_mem _ (mem_del hp)

theorem ins_sorted (L : OrdLaws cmp) (k : α) (v : β) :
    ∀ (m : List (α × β)), Sorted cmp m → Sorted cmp (ins cmp k v m)
  | [], _ => by simp [ins, Sorted]
  | (k', v') :: rest, hs => by
    obtain ⟨hlt, hrest⟩ := hs
    unfold ins
    by_cases h1 : cmp k k' = -1
    · simp only [h1, ite_true]
      refine ⟨?_, hlt, hrest⟩
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · rw [hp]; exact h1
      · exact L.trans _ _ _ h1 (hlt p hp)
    · by_cases h2 : cmp k k' = 0
      · rw [ite_eq_right h1, ite_eq_left h2]
        have e := (L.zero k k').1 h2
        subst e
        exact ⟨hlt, hrest⟩
      · simp only [h1, h2, ite_false]
        refine ⟨?_, ins_sorted L k v rest hrest⟩
        intro p hp
        rcases mem_ins hp with e | e
        · rw [e]
          have hs := L.swap k k'
          rcases L.range k k' with r | r | r
          · exact absurd r h1
          · exact absurd r h2
          · simp only at hs ⊢; omega
        · exact hlt p e

theorem del_sorted (k : α) : ∀ (m : List (α × β)), Sorted cmp m → Sorted cmp (del cmp k m)
  | [], _ => by simp [del, Sorted]
  | (k', v') :: rest, hs => by
    obtain ⟨hlt, hrest⟩ := hs
    unfold del
    by_cases h : cmp k k' = 0
    · simp only [h, ite_true]; exact hrest
    · simp only [h, ite_false]
      exact ⟨fun p hp => hlt p (mem_del hp), del_sorted k rest hrest⟩

theorem lookup_ins (L : OrdLaws cmp) (k : α) (v : β) :
    ∀ (m : List (α × β)), lookup cmp k (ins cmp k v m) = some v
  | [] => by simp [ins, lookup, (L.zero k k).2 rfl]
  | (k', v') :: rest => by
    unfold ins
    by_cases h1 : cmp k k' = -1
    · simp [h1, lookup, (L.zero k k).2 rfl]
    · by_cases h2 : cmp k k' = 0
      · simp [h2, lookup, (L.zero k k).2 rfl]
      · simp only [h1, h2, ite_false, lookup]
        exact lookup_ins L k v rest

theorem lookup_ins_other (L : OrdLaws cmp) (k k2 : α) (v : β) (hne : k2 ≠ k) :
    ∀ (m : List (α × β)), lookup cmp k2 (ins cmp k v m) = lookup cmp k2 m
  | [] => by
    have : cmp k2 k ≠ 0 := fun e => hne ((L.zero k2 k).1 e)
    simp [ins, lookup, this]
  | (k', v') :: rest => by
    have hk : cmp k2 k ≠ 0 := fun e => hne ((L.zero k2 k).1 e)
    unfold ins
    by_cases h1 : cmp k k' = -1
    · simp only [h1, ite_true]
      conv => lhs; unfold lookup
      simp [hk]
    · by_cases h2 : cmp k k' = 0
      · rw [ite_eq_right h1, ite_eq_left h2]
        have e := (L.zero k k').1 h2
        subst e
        unfold lookup
        simp [hk]
      · simp only [h1, h2, ite_false]
        unfold lookup
        by_cases h3 : cmp k2 k' = 0
        · simp [h3]
        · simp only [h3, ite_false]
          exact lookup_ins_other L k k2 v hne rest

theorem lookup_none_of_lt (L : OrdLaws cmp) (k : α) :
    ∀ (m : List (α × β)), (∀ p ∈ m, cmp k p.1 = -1) → lookup cmp k m = none
  | [], _ => rfl
  | (k', v') :: rest, h => by
    have h1 := h (k', v') (by simp)
    have h0 : cmp k k' ≠ 0 := by simp only at h1; omega
    unfold lookup
    simp only [h0, ite_false]
    exact lookup_none_of_lt L k rest (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem lookup_del (L : OrdLaws cmp) (k : α) :
    ∀ (m : List (α × β)), Sorted cmp m → lookup cmp k (del cmp k m) = none
  | [], _ => rfl
  | (k', v') :: rest, hs => by
    obtain ⟨hlt, hrest⟩ := hs
    unfold del
    by_cases h : cmp k k' = 0
    · simp only [h, ite_true]
      have e := (L.zero k k').1 h
      subst e
      exact lookup_none_of_lt L k rest hlt
    · simp only [h, ite_false]
      unfold lookup
      simp only [h, ite_false]
      exact lookup_del L k rest hrest

theorem lookup_del_other (L : OrdLaws cmp) (k k2 : α) (hne : k2 ≠ k) :
    ∀ (m : List (α × β)), lookup cmp k2 (del cmp k m) = lookup cmp k2 m
  | [] => rfl
  | (k', v') :: rest => by
    unfold del
    by_cases h : cmp k k' = 0
    · simp only [h, ite_true]
      have e := (L.zero k k').1 h
      subst e
      have hk : cmp k2 k ≠ 0 := fun e => hne ((L.zero k2 k).1 e)
      conv => rhs; unfold lookup
      simp [hk]
    · simp only [h, ite_false]
      unfold lookup
      by_cases h3 : cmp k2 k' = 0
      · simp [h3]
      · simp only [h3, ite_false]
        exact lookup_del_other L k k2 hne rest

/-! ## 例子：I64 的键（`Library.Math` 的 `cmpI`） -/

#eval ins Core.Library.Math.cmpI (3 : Int) "c" (ins Core.Library.Math.cmpI 1 "a" (ins Core.Library.Math.cmpI 2 "b" []))
#eval lookup Core.Library.Math.cmpI (2 : Int) (del Core.Library.Math.cmpI 1 (ins Core.Library.Math.cmpI 1 "a" (ins Core.Library.Math.cmpI 2 "b" [])))

end Core.Library.Map
