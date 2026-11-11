/-!
# 开放寻址的哈希表——`std.hashmap`

`std.hashmap` 的键和值紧凑地存在两个 Vec 里，另有一张槽位表 `slots`：每个槽位是 -1（空）或一个下标。
容量 `cap` 是 2 的幂，键的起始位置 `home k = hash(k) % cap`，槽位表的长度是 `L = 2 * cap`，
线性探测**不绕回**：从 `home k` 往后找。元素个数不超过 `3/4 cap`，所以探测最远到
`cap - 1 + n < L`，不会走出表（这一点由扩容保证，这里作为 `q < L` 的前提）。

这里把槽位表看成位置到键的函数 `Tbl`（下标换成它指向的键），验证三个操作：

- `lookup`：从 `home k` 往后，遇到空位就停（没有这个键），遇到 `k` 就找到；
- `ins`：从 `home k` 往后找第一个空位或 `k` 所在的位置（`slot`），放进去；
- `erase`：找到 `k` 的位置，清空它，再**后移回填**（`shift`）：往后扫，遇到 `home` 不在空位后面的键
  就把它搬进空位、空位移到它原来的位置，直到遇到空位。不需要墓碑。

**不变式** `Inv`：每个键的位置 `p` 满足 `home k ≤ p < L`，并且 `[home k, p)` 都不空；同一个键只出现一次。

**定理**：
- `lookup_iff`：`Inv` 下，`lookup` 找到 `p` 恰好是 `p` 里放着 `k`；
- `ins_spec`：插入后 `Inv` 仍然成立，`k` 在表里，别的键所在的位置不变；
- `erase_spec`：删除（后移回填）后 `Inv` 仍然成立，表里的键恰好是原来的键去掉 `k`。

紧凑数组那一侧（删除时把最后一个元素换到被删的位置、改它的槽位）由 `test/c51.t` 和 `std.map` 的随机对照检查。
-/

namespace Core.Library.HashMap

abbrev Tbl := Nat → Option Nat

def upd (t : Tbl) (p : Nat) (v : Option Nat) : Tbl := fun r => if r = p then v else t r

theorem upd_same (t : Tbl) (p : Nat) (v : Option Nat) : upd t p v p = v := by simp [upd]

theorem upd_other (t : Tbl) (p r : Nat) (v : Option Nat) (h : r ≠ p) : upd t p v r = t r := by
  simp [upd, h]

variable (home : Nat → Nat) (L : Nat)

structure Inv (t : Tbl) : Prop where
  inside : ∀ p k, t p = some k → p < L
  home_le : ∀ p k, t p = some k → home k ≤ p
  path : ∀ p k, t p = some k → ∀ r, home k ≤ r → r < p → t r ≠ none
  inj : ∀ p q k, t p = some k → t q = some k → p = q

/-! ## 查找 -/

/-- 从 `p` 往后最多看 `n` 个位置。 -/
def probe (t : Tbl) (k : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, p =>
    match t p with
    | none => none
    | some k' => if k' = k then some p else probe t k n (p + 1)

def lookup (t : Tbl) (k : Nat) : Option Nat := probe t k L (home k)

theorem probe_sound (t : Tbl) (k : Nat) : ∀ n p q, probe t k n p = some q → t q = some k := by
  intro n
  induction n with
  | zero => intro p q h; simp [probe] at h
  | succ n ih =>
    intro p q h
    cases htp : t p with
    | none =>
      have e : probe t k (n + 1) p = none := by simp [probe, htp]
      rw [e] at h
      simp at h
    | some k' =>
      by_cases hk : k' = k
      · have e : probe t k (n + 1) p = some p := by simp [probe, htp, hk]
        rw [e] at h
        have hpq := Option.some.inj h
        rw [← hpq, htp, hk]
      · have e : probe t k (n + 1) p = probe t k n (p + 1) := by simp [probe, htp, hk]
        rw [e] at h
        exact ih _ _ h

theorem probe_found (t : Tbl) (k : Nat) (hI : Inv home L t) (q : Nat) (hq : t q = some k) :
    ∀ n p, home k ≤ p → p ≤ q → q < p + n → probe t k n p = some q := by
  intro n
  induction n with
  | zero => intro p _ _ h; omega
  | succ n ih =>
    intro p hp hpq hn
    by_cases he : p = q
    · rw [he]
      simp [probe, hq]
    · have hocc := hI.path q k hq p hp (by omega)
      cases htp : t p with
      | none => exact absurd htp hocc
      | some k' =>
        have hk : k' ≠ k := by
          intro e
          rw [e] at htp
          exact he (hI.inj p q k htp hq)
        have e : probe t k (n + 1) p = probe t k n (p + 1) := by simp [probe, htp, hk]
        rw [e]
        exact ih (p + 1) (by omega) (by omega) (by omega)

/-- **查找正确**：找到 `p` 恰好是 `p` 里放着 `k`。 -/
theorem lookup_iff (t : Tbl) (k p : Nat) (hI : Inv home L t) : lookup home L t k = some p ↔ t p = some k := by
  constructor
  · intro h
    exact probe_sound t k L (home k) p h
  · intro h
    have hin := hI.inside p k h
    exact probe_found home L t k hI p h L (home k) (Nat.le_refl _) (hI.home_le p k h) (by omega)

theorem lookup_none (t : Tbl) (k : Nat) (hI : Inv home L t) : lookup home L t k = none ↔ ∀ p, t p ≠ some k := by
  constructor
  · intro h p hp
    have := (lookup_iff home L t k p hI).mpr hp
    rw [h] at this
    simp at this
  · intro h
    cases hl : lookup home L t k with
    | none => rfl
    | some p => exact absurd ((lookup_iff home L t k p hI).mp hl) (h p)

/-! ## 插入 -/

/-- 从 `p` 往后第一个空位或 `k` 所在的位置。 -/
def slot (t : Tbl) (k : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, p =>
    match t p with
    | none => some p
    | some k' => if k' = k then some p else slot t k n (p + 1)

theorem slot_spec (t : Tbl) (k : Nat) : ∀ n p q, slot t k n p = some q →
    p ≤ q ∧ (t q = none ∨ t q = some k) ∧ ∀ r, p ≤ r → r < q → ∃ k', t r = some k' ∧ k' ≠ k := by
  intro n
  induction n with
  | zero => intro p q h; simp [slot] at h
  | succ n ih =>
    intro p q h
    cases htp : t p with
    | none =>
      have e : slot t k (n + 1) p = some p := by simp [slot, htp]
      rw [e] at h
      have hpq := Option.some.inj h
      rw [← hpq]
      exact ⟨Nat.le_refl _, Or.inl htp, fun r h1 h2 => by omega⟩
    | some k' =>
      by_cases hk : k' = k
      · have e : slot t k (n + 1) p = some p := by simp [slot, htp, hk]
        rw [e] at h
        have hpq := Option.some.inj h
        rw [← hpq]
        exact ⟨Nat.le_refl _, Or.inr (by rw [htp, hk]), fun r h1 h2 => by omega⟩
      · have e : slot t k (n + 1) p = slot t k n (p + 1) := by simp [slot, htp, hk]
        rw [e] at h
        obtain ⟨h1, h2, h3⟩ := ih (p + 1) q h
        refine ⟨by omega, h2, ?_⟩
        intro r hr1 hr2
        by_cases hr : r = p
        · rw [hr]; exact ⟨k', htp, hk⟩
        · exact h3 r (by omega) hr2

/-- 放进 `k`；位置走出表时失败（扩容保证不会发生）。已有 `k` 时表不变（只换紧凑数组里的值）。 -/
def ins (t : Tbl) (k : Nat) : Option Tbl :=
  match slot t k L (home k) with
  | none => none
  | some q => if q < L then some (upd t q (some k)) else none

/-- **插入正确**：`Inv` 保持，`k` 在表里，别的键所在的位置不变。 -/
theorem ins_spec (t t' : Tbl) (k : Nat) (hI : Inv home L t) (h : ins home L t k = some t') :
    Inv home L t' ∧ (∃ q, t' q = some k) ∧ ∀ k2, k2 ≠ k → ∀ p, (t' p = some k2 ↔ t p = some k2) := by
  cases hs : slot t k L (home k) with
  | none =>
    have e : ins home L t k = none := by simp [ins, hs]
    rw [e] at h
    simp at h
  | some q =>
    by_cases hqL : q < L
    · have e : ins home L t k = some (upd t q (some k)) := by simp [ins, hs, hqL]
      rw [e] at h
      have ht' := Option.some.inj h
      subst ht'
      obtain ⟨h1, h2, h3⟩ := slot_spec t k L (home k) q hs
      -- k 原来如果在表里，一定就在 q
      have uq : ∀ p2, t p2 = some k → p2 = q := by
        intro p2 hp2
        rcases h2 with hn | hs'
        · by_cases hlt : p2 < q
          · obtain ⟨k', hk', hne⟩ := h3 p2 (hI.home_le p2 k hp2) hlt
            rw [hp2] at hk'
            exact absurd (Option.some.inj hk').symm hne
          · by_cases heq : p2 = q
            · exact heq
            · exact absurd hn (hI.path p2 k hp2 q h1 (by omega))
        · exact hI.inj p2 q k hp2 hs'
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨q, upd_same t q _⟩, ?_⟩
      · intro p k2 hp
        by_cases e : p = q
        · omega
        · rw [upd_other _ _ _ _ e] at hp
          exact hI.inside p k2 hp
      · intro p k2 hp
        by_cases e : p = q
        · rw [e, upd_same] at hp
          rw [← Option.some.inj hp, e]
          exact h1
        · rw [upd_other _ _ _ _ e] at hp
          exact hI.home_le p k2 hp
      · intro p k2 hp r hr1 hr2
        by_cases er : r = q
        · rw [er, upd_same]; simp
        · rw [upd_other _ _ _ _ er]
          by_cases e : p = q
          · rw [e, upd_same] at hp
            have hk := Option.some.inj hp
            rw [← hk] at hr1
            rw [e] at hr2
            obtain ⟨k', hk', _⟩ := h3 r hr1 hr2
            rw [hk']; simp
          · rw [upd_other _ _ _ _ e] at hp
            exact hI.path p k2 hp r hr1 hr2
      · intro p p2 k2 hp hp2
        by_cases e : p = q
        · by_cases e2 : p2 = q
          · omega
          · rw [e, upd_same] at hp
            rw [upd_other _ _ _ _ e2, ← Option.some.inj hp] at hp2
            exact absurd (uq p2 hp2) e2
        · by_cases e2 : p2 = q
          · rw [e2, upd_same] at hp2
            rw [upd_other _ _ _ _ e, ← Option.some.inj hp2] at hp
            exact absurd (uq p hp) e
          · rw [upd_other _ _ _ _ e] at hp
            rw [upd_other _ _ _ _ e2] at hp2
            exact hI.inj p p2 k2 hp hp2
      · intro k2 hk2 p
        by_cases e : p = q
        · rw [e, upd_same]
          constructor
          · intro hc; exact absurd (Option.some.inj hc) (Ne.symm hk2)
          · intro hc
            rcases h2 with hn | hs'
            · rw [hn] at hc; simp at hc
            · rw [hs'] at hc; exact absurd (Option.some.inj hc) (Ne.symm hk2)
        · rw [upd_other _ _ _ _ e]
    · have e : ins home L t k = none := by simp [ins, hs, hqL]
      rw [e] at h
      simp at h

/-! ## 删除：后移回填 -/

/-- 空位是 `hole`，从 `j` 往后扫。`home` 不在空位后面的键搬进空位，空位移到它原来的位置。 -/
def shift : Nat → Tbl → Nat → Nat → Tbl
  | 0, t, _, _ => t
  | n + 1, t, hole, j =>
    match t j with
    | none => t
    | some k =>
      if home k ≤ hole then shift n (upd (upd t hole (some k)) j none) j (j + 1)
      else shift n t hole (j + 1)

def erase (t : Tbl) (k : Nat) : Tbl :=
  match lookup home L t k with
  | none => t
  | some i => shift home L (upd t i none) i (i + 1)

/-- 回填过程中的不变式：只有 `hole` 可能挡在 `j` 及以后的键的探测路上。 -/
structure SInv (t : Tbl) (hole j : Nat) : Prop where
  inside : ∀ p k, t p = some k → p < L
  home_le : ∀ p k, t p = some k → home k ≤ p
  path : ∀ p k, t p = some k → ∀ r, home k ≤ r → r < p → t r ≠ none ∨ (r = hole ∧ j ≤ p)
  inj : ∀ p q k, t p = some k → t q = some k → p = q
  hole_none : t hole = none
  lt : hole < j

/-- 扫到空位时，不变式恢复成 `Inv`。 -/
theorem sinv_done (t : Tbl) (hole j : Nat) (hS : SInv home L t hole j) (hj : t j = none) : Inv home L t := by
  refine ⟨hS.inside, hS.home_le, ?_, hS.inj⟩
  intro p k hp r hr1 hr2
  rcases hS.path p k hp r hr1 hr2 with h | ⟨hr, hjp⟩
  · exact h
  · exfalso
    have hpj : p ≠ j := by intro e; rw [e, hj] at hp; simp at hp
    have hl := hS.lt
    rcases hS.path p k hp j (by omega) (by omega) with h' | ⟨h', _⟩
    · exact h' hj
    · omega

theorem shift_spec : ∀ n (t : Tbl) hole j, SInv home L t hole j → L ≤ j + n →
    Inv home L (shift home n t hole j) ∧ ∀ k, (∃ p, shift home n t hole j p = some k) ↔ ∃ p, t p = some k := by
  intro n
  induction n with
  | zero =>
    intro t hole j hS hL
    have hj : t j = none := by
      cases h : t j with
      | none => rfl
      | some k => have := hS.inside j k h; omega
    show Inv home L t ∧ ∀ k, (∃ p, t p = some k) ↔ ∃ p, t p = some k
    exact ⟨sinv_done home L t hole j hS hj, fun k => Iff.rfl⟩
  | succ n ih =>
    intro t hole j hS hL
    cases htj : t j with
    | none =>
      have e : shift home (n + 1) t hole j = t := by simp [shift, htj]
      rw [e]
      exact ⟨sinv_done home L t hole j hS htj, fun k => Iff.rfl⟩
    | some k =>
      have hjL := hS.inside j k htj
      have hl := hS.lt
      by_cases hle : home k ≤ hole
      · -- 搬进空位
        have e : shift home (n + 1) t hole j = shift home n (upd (upd t hole (some k)) j none) j (j + 1) := by
          simp [shift, htj, hle]
        rw [e]
        have hhj : hole ≠ j := by omega
        have tj : upd (upd t hole (some k)) j none j = none := upd_same _ _ _
        have th : upd (upd t hole (some k)) j none hole = some k := by
          rw [upd_other _ _ _ _ hhj, upd_same]
        have to : ∀ r, r ≠ j → r ≠ hole → upd (upd t hole (some k)) j none r = t r := by
          intro r h1 h2
          rw [upd_other _ _ _ _ h1, upd_other _ _ _ _ h2]
        have hS' : SInv home L (upd (upd t hole (some k)) j none) j (j + 1) := by
          refine ⟨?_, ?_, ?_, ?_, tj, by omega⟩
          · intro p k2 hp
            by_cases e1 : p = j
            · rw [e1, tj] at hp; simp at hp
            · by_cases e2 : p = hole
              · omega
              · rw [to p e1 e2] at hp; exact hS.inside p k2 hp
          · intro p k2 hp
            by_cases e1 : p = j
            · rw [e1, tj] at hp; simp at hp
            · by_cases e2 : p = hole
              · rw [e2, th] at hp
                rw [← Option.some.inj hp, e2]
                exact hle
              · rw [to p e1 e2] at hp; exact hS.home_le p k2 hp
          · intro p k2 hp r hr1 hr2
            by_cases e1 : p = j
            · rw [e1, tj] at hp; simp at hp
            · by_cases e2 : p = hole
              · rw [e2, th] at hp
                have hk := Option.some.inj hp
                rw [← hk] at hr1
                rw [e2] at hr2
                left
                rw [to r (by omega) (by omega)]
                rcases hS.path j k htj r hr1 (by omega) with h | ⟨h, _⟩
                · exact h
                · omega
              · rw [to p e1 e2] at hp
                by_cases r1 : r = hole
                · left; rw [r1, th]; simp
                · by_cases r2 : r = j
                  · right; omega
                  · left
                    rw [to r r2 r1]
                    rcases hS.path p k2 hp r hr1 hr2 with h | ⟨h, _⟩
                    · exact h
                    · exact absurd h r1
          · intro p p2 k2 hp hp2
            by_cases e1 : p = j
            · rw [e1, tj] at hp; simp at hp
            · by_cases f1 : p2 = j
              · rw [f1, tj] at hp2; simp at hp2
              · by_cases e2 : p = hole
                · by_cases f2 : p2 = hole
                  · omega
                  · rw [e2, th] at hp
                    rw [to p2 f1 f2, ← Option.some.inj hp] at hp2
                    exact absurd (hS.inj p2 j k hp2 htj) f1
                · by_cases f2 : p2 = hole
                  · rw [f2, th] at hp2
                    rw [to p e1 e2, ← Option.some.inj hp2] at hp
                    exact absurd (hS.inj p j k hp htj) e1
                  · rw [to p e1 e2] at hp
                    rw [to p2 f1 f2] at hp2
                    exact hS.inj p p2 k2 hp hp2
        obtain ⟨hInv, hKeys⟩ := ih _ j (j + 1) hS' (by omega)
        refine ⟨hInv, fun k2 => (hKeys k2).trans ?_⟩
        constructor
        · rintro ⟨p, hp⟩
          by_cases e1 : p = j
          · rw [e1, tj] at hp; simp at hp
          · by_cases e2 : p = hole
            · rw [e2, th] at hp
              exact ⟨j, by rw [htj, hp]⟩
            · rw [to p e1 e2] at hp
              exact ⟨p, hp⟩
        · rintro ⟨p, hp⟩
          by_cases e1 : p = j
          · rw [e1, htj] at hp
            exact ⟨hole, by rw [th, hp]⟩
          · by_cases e2 : p = hole
            · rw [e2, hS.hole_none] at hp; simp at hp
            · exact ⟨p, by rw [to p e1 e2]; exact hp⟩
      · -- 不动，继续往后
        have e : shift home (n + 1) t hole j = shift home n t hole (j + 1) := by
          simp [shift, htj, hle]
        rw [e]
        have hS' : SInv home L t hole (j + 1) := by
          refine ⟨hS.inside, hS.home_le, ?_, hS.inj, hS.hole_none, by omega⟩
          intro p k2 hp r hr1 hr2
          rcases hS.path p k2 hp r hr1 hr2 with h | ⟨hr, hjp⟩
          · left; exact h
          · right
            refine ⟨hr, ?_⟩
            by_cases e1 : p = j
            · rw [e1, htj] at hp
              rw [← Option.some.inj hp] at hr1
              omega
            · omega
        exact ih t hole (j + 1) hS' (by omega)

/-- **删除正确**：`Inv` 保持，表里的键恰好是原来的键去掉 `k`。 -/
theorem erase_spec (t : Tbl) (k : Nat) (hI : Inv home L t) :
    Inv home L (erase home L t k) ∧
    ∀ k2, (∃ p, erase home L t k p = some k2) ↔ (∃ p, t p = some k2) ∧ k2 ≠ k := by
  cases hl : lookup home L t k with
  | none =>
    have e : erase home L t k = t := by simp [erase, hl]
    rw [e]
    have hn := (lookup_none home L t k hI).mp hl
    refine ⟨hI, fun k2 => ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩⟩
    rintro rfl
    obtain ⟨p, hp⟩ := h
    exact hn p hp
  | some i =>
    have e : erase home L t k = shift home L (upd t i none) i (i + 1) := by simp [erase, hl]
    rw [e]
    have hi := (lookup_iff home L t k i hI).mp hl
    have t0 : ∀ r, r ≠ i → upd t i none r = t r := fun r h => upd_other _ _ _ _ h
    have hS : SInv home L (upd t i none) i (i + 1) := by
      refine ⟨?_, ?_, ?_, ?_, upd_same _ _ _, by omega⟩
      · intro p k2 hp
        by_cases e1 : p = i
        · rw [e1, upd_same] at hp; simp at hp
        · rw [t0 p e1] at hp; exact hI.inside p k2 hp
      · intro p k2 hp
        by_cases e1 : p = i
        · rw [e1, upd_same] at hp; simp at hp
        · rw [t0 p e1] at hp; exact hI.home_le p k2 hp
      · intro p k2 hp r hr1 hr2
        by_cases e1 : p = i
        · rw [e1, upd_same] at hp; simp at hp
        · rw [t0 p e1] at hp
          by_cases r1 : r = i
          · right; omega
          · left; rw [t0 r r1]; exact hI.path p k2 hp r hr1 hr2
      · intro p p2 k2 hp hp2
        by_cases e1 : p = i
        · rw [e1, upd_same] at hp; simp at hp
        · by_cases f1 : p2 = i
          · rw [f1, upd_same] at hp2; simp at hp2
          · rw [t0 p e1] at hp
            rw [t0 p2 f1] at hp2
            exact hI.inj p p2 k2 hp hp2
    obtain ⟨hInv, hKeys⟩ := shift_spec home L L (upd t i none) i (i + 1) hS (by omega)
    refine ⟨hInv, fun k2 => (hKeys k2).trans ?_⟩
    constructor
    · rintro ⟨p, hp⟩
      by_cases e1 : p = i
      · rw [e1, upd_same] at hp; simp at hp
      · rw [t0 p e1] at hp
        refine ⟨⟨p, hp⟩, ?_⟩
        rintro rfl
        exact e1 (hI.inj p i _ hp hi)
    · rintro ⟨⟨p, hp⟩, hne⟩
      by_cases e1 : p = i
      · rw [e1, hi] at hp
        exact absurd (Option.some.inj hp).symm hne
      · exact ⟨p, by rw [t0 p e1]; exact hp⟩

/-! ## 例子：home k = k % 4，表长 8 -/

def h4 (k : Nat) : Nat := k % 4
def emp : Tbl := fun _ => none
def show8 (t : Tbl) : List (Option Nat) := (List.range 8).map t

-- 1、5、9 都落在 1：依次放在 1、2、3；2 落在 2，被挤到 4
def ex : Tbl :=
  match ins h4 8 emp 1 with
  | some a => match ins h4 8 a 5 with
    | some b => match ins h4 8 b 9 with
      | some c => match ins h4 8 c 2 with
        | some d => d
        | none => emp
      | none => emp
    | none => emp
  | none => emp

#eval show8 ex
-- 删掉 5：9 回填到 2，2 回填到 3
#eval show8 (erase h4 8 ex 5)
#eval (lookup h4 8 (erase h4 8 ex 5) 2, lookup h4 8 (erase h4 8 ex 5) 5)

end Core.Library.HashMap
