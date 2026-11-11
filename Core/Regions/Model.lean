import Core.Basic

/-!
# 区域的基本模型

**区域**按词法嵌套：`block p` 进入时创建一个新区域，退出时整块归还，不逐个释放。
当前深度为 `d` 时，区域 `0 … d-1` 活着；区域 `k` 在深度降到 `k` 时结束。

**变量**也按词法作用域：在深度 `d` 用 `decl x` 声明的变量，作用域深度为 `d`，
深度降到 `d` 以下时离开作用域。

**命令**：
- `decl x`：声明变量；
- `ralloc x k`：在区域 `k` 里分配一个值，指针放进 `x`（类型 `T in k`）；
- `copy x y`：`y := x`，复制只读引用；
- `read x`：通过 `x` 读取。

**静态规则**（核心只有一条）：变量 `x` 的作用域深度为 `dx` 时，只能存放区域 `k < dx` 的指针，
也就是变量一定比它指向的区域先结束。

**动态语义**仍然故意做得“危险”：区域结束后旧指针照样保留，读取时如果区域已死就出错。
每个区域有唯一编号（`rid`、`next`），不会因为编号复用掩盖悬空指针。

**主定理** `safety_and_no_leak`：检查器接受的程序执行不出错（每次读取时区域都活着），
并且结束时没有任何区域还活着。

这一轮只有顺序和块，没有分支、循环：区域规则不在汇合点产生新问题，合并方式和 `Ownership.Loop` 相同。
协变（D2）和 `Mut` 放在 `Regions.Variance`。
-/

namespace Core.Regions.Model

inductive Cmd5
  | decl   (x : Var)
  | ralloc (x : Var) (k : Nat)
  | copy   (x y : Var)
  | read   (x : Var)

inductive P
  | skip
  | cmd   (c : Cmd5)
  | seq   (p q : P)
  | block (p : P)

/-! ## 静态检查 -/

/-- 变量的静态信息：`none` 不在作用域；`some (dx, o)`：作用域深度 `dx`，`o` 是指向的区域。 -/
abbrev REnv := Var → Option (Nat × Option Nat)

def check1 (d : Nat) (σ : REnv) : Cmd5 → Option REnv
  | .decl x => if σ x = none then some (upd σ x (some (d, none))) else none
  | .ralloc x k =>
    match σ x with
    | some (dx, _) => if k < dx then some (upd σ x (some (dx, some k))) else none
    | none         => none
  | .copy x y =>
    match σ x, σ y with
    | some (_, some k), some (dy, _) =>
      if k < dy then some (upd σ y (some (dy, some k))) else none
    | _, _ => none
  | .read x =>
    match σ x with
    | some (_, some _) => some σ
    | _                => none

/-- 离开深度 `d + 1` 的块：作用域深度大于 `d` 的变量离开作用域。 -/
def restrict (d : Nat) (σ : REnv) : REnv := fun x =>
  match σ x with
  | some (dx, o) => if dx ≤ d then some (dx, o) else none
  | none         => none

def check : P → Nat → REnv → Option REnv
  | .skip,    _, σ => some σ
  | .cmd c,   d, σ => check1 d σ c
  | .seq p q, d, σ =>
    match check p d σ with
    | some σ₁ => check q d σ₁
    | none    => none
  | .block p, d, σ =>
    match check p (d + 1) σ with
    | some σ₁ => some (restrict d σ₁)
    | none    => none

/-! ## 动态语义 -/

/-- 区域栈：`rid k` 是深度 `k` 处区域的编号，`alive` 记录每个编号是否活着。 -/
structure RSt where
  alive : Nat → Bool
  rid   : Nat → Nat
  d     : Nat
  next  : Nat

structure St5 where
  ptr : Var → Option Nat   -- 变量指向的区域编号
  rs  : RSt

def St5.empty : St5 := ⟨fun _ => none, ⟨fun _ => false, fun _ => 0, 0, 0⟩⟩

def enterR (r : RSt) : RSt :=
  { alive := upd r.alive r.next true, rid := upd r.rid r.d r.next,
    d := r.d + 1, next := r.next + 1 }

def leaveR (r : RSt) (d : Nat) : RSt :=
  { r with alive := upd r.alive (r.rid d) false, d := d }

def exec1 (s : St5) : Cmd5 → Option St5
  | .decl x => some ⟨upd s.ptr x none, s.rs⟩
  | .ralloc x k =>
    if k < s.rs.d ∧ s.rs.alive (s.rs.rid k) = true then
      some ⟨upd s.ptr x (some (s.rs.rid k)), s.rs⟩
    else none
  | .copy x y => some ⟨upd s.ptr y (s.ptr x), s.rs⟩
  | .read x =>
    match s.ptr x with
    | some i => if s.rs.alive i = true then some s else none
    | none   => none

def exec : P → St5 → Option St5
  | .skip,    s => some s
  | .cmd c,   s => exec1 s c
  | .seq p q, s =>
    match exec p s with
    | some s₁ => exec q s₁
    | none    => none
  | .block p, s =>
    match exec p ⟨s.ptr, enterR s.rs⟩ with
    | some s₁ => some ⟨s₁.ptr, leaveR s₁.rs s.rs.d⟩
    | none    => none

/-! ## 不变式 -/

structure StackOk (d : Nat) (r : RSt) : Prop where
  depth : r.d = d
  live  : ∀ k, k < d → r.alive (r.rid k) = true
  mono  : ∀ k j, k < j → j < d → r.rid k < r.rid j
  fresh : ∀ k, k < d → r.rid k < r.next
  only  : ∀ i, r.alive i = true → ∃ k, k < d ∧ r.rid k = i

structure Good (d : Nat) (σ : REnv) (s : St5) : Prop where
  stk   : StackOk d s.rs
  scope : ∀ x dx o, σ x = some (dx, o) → dx ≤ d
  ptrs  : ∀ x dx k, σ x = some (dx, some k) → k < dx ∧ s.ptr x = some (s.rs.rid k)

theorem good_empty : Good 0 (fun _ => none) St5.empty :=
  ⟨⟨rfl, (fun k hk => absurd hk (Nat.not_lt_zero k)),
     (fun _ j _ hj => absurd hj (Nat.not_lt_zero j)),
     (fun k hk => absurd hk (Nat.not_lt_zero k)),
     (fun i hi => by simp [St5.empty] at hi)⟩,
   (fun _ _ _ h => by simp at h),
   (fun _ _ _ h => by simp at h)⟩

/-! ## 进入、离开区域 -/

theorem enter_ok {d : Nat} {r : RSt} (h : StackOk d r) : StackOk (d + 1) (enterR r) := by
  have hd := h.depth
  constructor
  · show r.d + 1 = d + 1
    rw [hd]
  · intro k hk
    show upd r.alive r.next true (upd r.rid r.d r.next k) = true
    by_cases hkd : k = d
    · have hk' : k = r.d := hkd.trans hd.symm
      rw [hk', upd_same, upd_same]
    · have hk' : k < d := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkd
      have hne : k ≠ r.d := by rw [hd]; exact hkd
      have hne2 : r.rid k ≠ r.next := Nat.ne_of_lt (h.fresh k hk')
      rw [upd_other r.rid r.next hne, upd_other r.alive true hne2]
      exact h.live k hk'
  · intro k j hkj hj
    show upd r.rid r.d r.next k < upd r.rid r.d r.next j
    have hkd : k < d := Nat.lt_of_lt_of_le hkj (Nat.le_of_lt_succ hj)
    have hk' : k ≠ r.d := by rw [hd]; exact Nat.ne_of_lt hkd
    rw [upd_other r.rid r.next hk']
    by_cases hjd : j = d
    · have hj' : j = r.d := hjd.trans hd.symm
      rw [hj', upd_same]
      exact h.fresh k hkd
    · have hj2 : j < d := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hjd
      have hj' : j ≠ r.d := by rw [hd]; exact hjd
      rw [upd_other r.rid r.next hj']
      exact h.mono k j hkj hj2
  · intro k hk
    show upd r.rid r.d r.next k < r.next + 1
    by_cases hkd : k = r.d
    · rw [hkd, upd_same]
      exact Nat.lt_succ_self _
    · have hk' : k < d := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) (by rw [← hd]; exact hkd)
      rw [upd_other r.rid r.next hkd]
      exact Nat.lt_succ_of_lt (h.fresh k hk')
  · intro i hi
    change upd r.alive r.next true i = true at hi
    by_cases hin : i = r.next
    · exact ⟨d, Nat.lt_succ_self d, by
        show upd r.rid r.d r.next d = i
        rw [← hd, upd_same, hin]⟩
    · rw [upd_other r.alive true hin] at hi
      obtain ⟨k, hk, hki⟩ := h.only i hi
      have hne : k ≠ r.d := by rw [hd]; exact Nat.ne_of_lt hk
      exact ⟨k, Nat.lt_succ_of_lt hk, by
        show upd r.rid r.d r.next k = i
        rw [upd_other r.rid r.next hne]
        exact hki⟩

theorem leave_ok {d : Nat} {r : RSt} (h : StackOk (d + 1) r) : StackOk d (leaveR r d) := by
  constructor
  · rfl
  · intro k hk
    show upd r.alive (r.rid d) false (r.rid k) = true
    have hne : r.rid k ≠ r.rid d := Nat.ne_of_lt (h.mono k d hk (Nat.lt_succ_self d))
    rw [upd_other r.alive false hne]
    exact h.live k (Nat.lt_succ_of_lt hk)
  · intro k j hkj hj
    exact h.mono k j hkj (Nat.lt_succ_of_lt hj)
  · intro k hk
    exact h.fresh k (Nat.lt_succ_of_lt hk)
  · intro i hi
    change upd r.alive (r.rid d) false i = true at hi
    by_cases hid : i = r.rid d
    · rw [hid, upd_same] at hi
      cases hi
    · rw [upd_other r.alive false hid] at hi
      obtain ⟨k, hk, hki⟩ := h.only i hi
      by_cases hkd : k = d
      · rw [hkd] at hki
        exact absurd hki.symm hid
      · exact ⟨k, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkd, hki⟩

theorem enter_good {d : Nat} {σ : REnv} {s : St5} (hg : Good d σ s) :
    Good (d + 1) σ ⟨s.ptr, enterR s.rs⟩ := by
  refine ⟨enter_ok hg.stk, ?_, ?_⟩
  · intro x dx o hx
    exact Nat.le_succ_of_le (hg.scope x dx o hx)
  · intro x dx k hx
    obtain ⟨h1, h2⟩ := hg.ptrs x dx k hx
    have hkd : k < d := Nat.lt_of_lt_of_le h1 (hg.scope x dx _ hx)
    have hne : k ≠ s.rs.d := by rw [hg.stk.depth]; exact Nat.ne_of_lt hkd
    refine ⟨h1, ?_⟩
    show s.ptr x = some (upd s.rs.rid s.rs.d s.rs.next k)
    rw [upd_other s.rs.rid s.rs.next hne]
    exact h2

theorem restrict_some {d : Nat} {σ : REnv} {x : Var} {dx : Nat} {o : Option Nat}
    (h : restrict d σ x = some (dx, o)) : σ x = some (dx, o) ∧ dx ≤ d := by
  simp only [restrict] at h
  split at h
  · rename_i dx' o' hx
    split at h
    · rename_i hle
      cases h
      exact ⟨hx, hle⟩
    · contradiction
  · contradiction

theorem leave_good {d : Nat} {σ : REnv} {s : St5} (hg : Good (d + 1) σ s) :
    Good d (restrict d σ) ⟨s.ptr, leaveR s.rs d⟩ := by
  refine ⟨leave_ok hg.stk, ?_, ?_⟩
  · intro x dx o hx
    exact (restrict_some hx).2
  · intro x dx k hx
    exact hg.ptrs x dx k (restrict_some hx).1

/-! ## 单步 -/

theorem step1 {d : Nat} {σ σ' : REnv} {s : St5} {c : Cmd5}
    (hc : check1 d σ c = some σ') (hg : Good d σ s) :
    ∃ s', exec1 s c = some s' ∧ Good d σ' s' := by
  cases c with
  | decl x =>
    simp only [check1] at hc
    split at hc
    · cases hc
      refine ⟨⟨upd s.ptr x none, s.rs⟩, rfl, ⟨hg.stk, ?_, ?_⟩⟩
      · intro z dz o hz
        by_cases hzx : z = x
        · rw [hzx, upd_same] at hz
          simp only [Option.some.injEq, Prod.mk.injEq] at hz
          rw [← hz.1]
          exact Nat.le_refl d
        · rw [upd_other σ (some (d, none)) hzx] at hz
          exact hg.scope z dz o hz
      · intro z dz k hz
        by_cases hzx : z = x
        · rw [hzx, upd_same] at hz
          simp at hz
        · rw [upd_other σ (some (d, none)) hzx] at hz
          obtain ⟨h1, h2⟩ := hg.ptrs z dz k hz
          refine ⟨h1, ?_⟩
          show upd s.ptr x none z = some (s.rs.rid k)
          rw [upd_other s.ptr none hzx]
          exact h2
    · contradiction
  | ralloc x k =>
    simp only [check1] at hc
    split at hc
    · rename_i dx o hx
      split at hc
      · rename_i hk
        cases hc
        have hdx := hg.scope x dx o hx
        have hkd : k < d := Nat.lt_of_lt_of_le hk hdx
        have hlive := hg.stk.live k hkd
        refine ⟨⟨upd s.ptr x (some (s.rs.rid k)), s.rs⟩, ?_, ⟨hg.stk, ?_, ?_⟩⟩
        · simp [exec1, hg.stk.depth, hkd, hlive]
        · intro z dz o' hz
          by_cases hzx : z = x
          · rw [hzx, upd_same] at hz
            simp only [Option.some.injEq, Prod.mk.injEq] at hz
            rw [← hz.1]
            exact hdx
          · rw [upd_other σ (some (dx, some k)) hzx] at hz
            exact hg.scope z dz o' hz
        · intro z dz k' hz
          by_cases hzx : z = x
          · rw [hzx, upd_same] at hz
            simp only [Option.some.injEq, Prod.mk.injEq] at hz
            obtain ⟨rfl, rfl⟩ := hz
            refine ⟨hk, ?_⟩
            show upd s.ptr x (some (s.rs.rid k)) z = some (s.rs.rid k)
            rw [hzx, upd_same]
          · rw [upd_other σ (some (dx, some k)) hzx] at hz
            obtain ⟨h1, h2⟩ := hg.ptrs z dz k' hz
            refine ⟨h1, ?_⟩
            show upd s.ptr x (some (s.rs.rid k)) z = some (s.rs.rid k')
            rw [upd_other s.ptr (some (s.rs.rid k)) hzx]
            exact h2
      · contradiction
    · contradiction
  | copy x y =>
    simp only [check1] at hc
    split at hc
    · rename_i dxx k dy o hx hy
      split at hc
      · rename_i hk
        cases hc
        have hpx := (hg.ptrs x dxx k hx).2
        have hdy := hg.scope y dy o hy
        refine ⟨⟨upd s.ptr y (s.ptr x), s.rs⟩, rfl, ⟨hg.stk, ?_, ?_⟩⟩
        · intro z dz o' hz
          by_cases hzy : z = y
          · rw [hzy, upd_same] at hz
            simp only [Option.some.injEq, Prod.mk.injEq] at hz
            rw [← hz.1]
            exact hdy
          · rw [upd_other σ (some (dy, some k)) hzy] at hz
            exact hg.scope z dz o' hz
        · intro z dz k' hz
          by_cases hzy : z = y
          · rw [hzy, upd_same] at hz
            simp only [Option.some.injEq, Prod.mk.injEq] at hz
            obtain ⟨rfl, rfl⟩ := hz
            refine ⟨hk, ?_⟩
            show upd s.ptr y (s.ptr x) z = some (s.rs.rid k)
            rw [hzy, upd_same]
            exact hpx
          · rw [upd_other σ (some (dy, some k)) hzy] at hz
            obtain ⟨h1, h2⟩ := hg.ptrs z dz k' hz
            refine ⟨h1, ?_⟩
            show upd s.ptr y (s.ptr x) z = some (s.rs.rid k')
            rw [upd_other s.ptr (s.ptr x) hzy]
            exact h2
      · contradiction
    · contradiction
  | read x =>
    simp only [check1] at hc
    split at hc
    · rename_i dxx k hx
      cases hc
      obtain ⟨h1, h2⟩ := hg.ptrs x dxx k hx
      have hkd : k < d := Nat.lt_of_lt_of_le h1 (hg.scope x dxx _ hx)
      have hlive := hg.stk.live k hkd
      exact ⟨s, by simp [exec1, h2, hlive], hg⟩
    · contradiction

/-! ## 程序 -/

theorem sound (p : P) : ∀ {d : Nat} {σ σ' : REnv} {s : St5},
    check p d σ = some σ' → Good d σ s → ∃ s', exec p s = some s' ∧ Good d σ' s' := by
  induction p with
  | skip =>
    intro d σ σ' s hc hg
    simp only [check] at hc
    cases hc
    exact ⟨s, rfl, hg⟩
  | cmd c =>
    intro d σ σ' s hc hg
    exact step1 hc hg
  | seq p q ihp ihq =>
    intro d σ σ' s hc hg
    simp only [check] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hg₁⟩ := ihp h₁ hg
      obtain ⟨s₂, he₂, hg₂⟩ := ihq hc hg₁
      exact ⟨s₂, by simp [exec, he₁, he₂], hg₂⟩
    · contradiction
  | block p ih =>
    intro d σ σ' s hc hg
    simp only [check] at hc
    split at hc
    · rename_i σ₁ h₁
      cases hc
      obtain ⟨s₁, he₁, hg₁⟩ := ih h₁ (enter_good hg)
      refine ⟨⟨s₁.ptr, leaveR s₁.rs s.rs.d⟩, by simp [exec, he₁], ?_⟩
      rw [hg.stk.depth]
      exact leave_good hg₁
    · contradiction

/-! ## 主定理 -/

/-- **`Regions.Model` 主定理。** 检查器接受的程序执行不出错：每次读取、每次分配时区域都活着；
并且结束时没有任何区域还活着。 -/
theorem safety_and_no_leak (p : P) (σ' : REnv)
    (h : check p 0 (fun _ => none) = some σ') :
    ∃ s', exec p St5.empty = some s' ∧ ∀ i, s'.rs.alive i = false := by
  obtain ⟨s', he, hg⟩ := sound p h good_empty
  refine ⟨s', he, ?_⟩
  intro i
  cases hi : s'.rs.alive i with
  | false => rfl
  | true =>
    obtain ⟨k, hk, _⟩ := hg.stk.only i hi
    exact absurd hk (Nat.not_lt_zero k)

/-! ## 例子 -/

def seqL : List P → P
  | []      => .skip
  | p :: ps => .seq p (seqL ps)

/-- 在块里声明变量、在本块的区域里分配、读取：接受。 -/
def ok1 : P := .block (seqL [.cmd (.decl 0), .cmd (.ralloc 0 0), .cmd (.read 0)])
example : (check ok1 0 (fun _ => none)).isSome = true := rfl

/-- 内层块往外层区域里分配，外层变量在内层块结束后继续使用：接受。 -/
def ok2 : P := .block (seqL [.cmd (.decl 0), .block (.cmd (.ralloc 0 0)), .cmd (.read 0)])
example : (check ok2 0 (fun _ => none)).isSome = true := rfl

/-- 内层变量引用外层区域的值（II.6 的 R4）：接受。 -/
def ok3 : P := .block (seqL
  [.cmd (.decl 0), .cmd (.ralloc 0 0),
   .block (seqL [.cmd (.decl 1), .cmd (.copy 0 1), .cmd (.read 1)]),
   .cmd (.read 0)])
example : (check ok3 0 (fun _ => none)).isSome = true := rfl

/-- 先后两个块各用一个区域：接受；结束时没有区域活着。 -/
def ok4 : P := seqL
  [.block (seqL [.cmd (.decl 0), .cmd (.ralloc 0 0)]),
   .block (seqL [.cmd (.decl 0), .cmd (.ralloc 0 0), .cmd (.read 0)])]
example : (check ok4 0 (fun _ => none)).isSome = true := rfl

/-- 外层变量拿到内层区域的指针：拒绝。不经检查执行，块结束后读取出错。 -/
def bad1 : P := seqL [.cmd (.decl 0), .block (.cmd (.ralloc 0 0)), .cmd (.read 0)]
example : (check bad1 0 (fun _ => none)).isNone = true := rfl
example : (exec bad1 St5.empty).isNone = true := rfl

/-- 通过复制把内层区域的引用带出块：拒绝。不经检查执行，出错。 -/
def bad2 : P := seqL
  [.cmd (.decl 1),
   .block (seqL [.cmd (.decl 0), .cmd (.ralloc 0 0), .cmd (.copy 0 1)]),
   .cmd (.read 1)]
example : (check bad2 0 (fun _ => none)).isNone = true := rfl
example : (exec bad2 St5.empty).isNone = true := rfl

/-- 外层块的变量存放内层区域的指针：即使不出块，也拒绝。 -/
def bad3 : P := .block (seqL [.cmd (.decl 0), .block (.cmd (.ralloc 0 1))])
example : (check bad3 0 (fun _ => none)).isNone = true := rfl

/-- 离开作用域的变量不能再读：拒绝。 -/
def bad4 : P := seqL [.block (seqL [.cmd (.decl 0), .cmd (.ralloc 0 0)]), .cmd (.read 0)]
example : (check bad4 0 (fun _ => none)).isNone = true := rfl

end Core.Regions.Model
