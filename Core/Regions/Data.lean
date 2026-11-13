import Core.Regions.Model

/-!
# 含引用的数据类型

**问题**：泛型结构体、枚举的类型实参可以是引用（`Option<&I64 in a>`、`Pair<&I64 in a, &I64 in b>`），
一个值里可能有好几个引用，分属不同的区域，也可能一个都没有（`.None`）。检查器按值的**类型**算出它可能
含有的区域（类型实参里的区域都要算上），存放时要求这些区域都比变量活得久。

**做法**：在 `Regions.Model` 上把“变量指向一个区域”推广成“变量的值里有一组指针”。静态信息是 `(dx, ks)`：
作用域深度和类型里的区域列表；动态状态里每个变量是一组区域编号。新的命令：
- `pack x ys`：`x := S { …ys… }`，把几个变量的值装进一个结构体（或 `.Some(y)`），
  类型的区域是各部分的区域拼起来；
- `empty x ks`：`x := .None`，值里没有指针，但类型 `Option<&T in k>` 仍然带着区域 `ks`；
- `read x`：读出值里的每个引用（例如 `match o { .Some(r) => *r }`）。

**不变式**：值里的每个指针都是类型里某个区域 `k` 的编号，并且 `k < dx`。

**主定理** `safety_and_no_leak`：检查器接受的程序执行不出错（每次读取时值里的每个区域都活着），
结束时没有区域还活着。

**反例**：如果算类型的区域时漏掉类型实参（把 `Option<&I64 in b>` 当作不含引用，
即编译器早先 `region_names` 的行为），检查器会接受一个读取悬空指针的程序（`bad1`）。
这正是在有这条规则之前，编译器必须拒绝含引用的泛型数据类型的原因。

泛型函数实例化时的区域换名对一组区域的情形见 `Regions.DataGeneric`。
-/

namespace Core.Regions.Data
open Core.Regions.Model (RSt StackOk enterR leaveR enter_ok leave_ok)

inductive Cmd
  | decl   (x : Var)
  | ralloc (x : Var) (k : Nat)
  | pack   (x : Var) (ys : List Var)
  | empty  (x : Var) (ks : List Nat)
  | copy   (x y : Var)
  | read   (x : Var)

inductive P
  | skip
  | cmd   (c : Cmd)
  | seq   (p q : P)
  | block (p : P)

/-! ## 静态检查 -/

/-- 变量的静态信息：`some (dx, ks)`：作用域深度 `dx`，值的类型里的区域 `ks`。 -/
abbrev REnv := Var → Option (Nat × List Nat)

/-- 列表里的区域都小于 `n`。 -/
def below (n : Nat) : List Nat → Bool
  | []      => true
  | k :: ks => decide (k < n) && below n ks

/-- 几个变量的类型里的区域拼起来；有变量不在作用域就失败。 -/
def regs (σ : REnv) : List Var → Option (List Nat)
  | []      => some []
  | y :: ys =>
    match σ y, regs σ ys with
    | some (_, ks), some rs => some (ks ++ rs)
    | _, _                  => none

def check1 (d : Nat) (σ : REnv) : Cmd → Option REnv
  | .decl x => if σ x = none then some (upd σ x (some (d, []))) else none
  | .ralloc x k =>
    match σ x with
    | some (dx, _) => if k < dx then some (upd σ x (some (dx, [k]))) else none
    | none         => none
  | .pack x ys =>
    match σ x, regs σ ys with
    | some (dx, _), some ks => if below dx ks then some (upd σ x (some (dx, ks))) else none
    | _, _                  => none
  | .empty x ks =>
    match σ x with
    | some (dx, _) => if below dx ks then some (upd σ x (some (dx, ks))) else none
    | none         => none
  | .copy x y =>
    match σ x, σ y with
    | some (_, ks), some (dy, _) => if below dy ks then some (upd σ y (some (dy, ks))) else none
    | _, _                       => none
  | .read x =>
    match σ x with
    | some (_, _) => some σ
    | none        => none

def restrict (d : Nat) (σ : REnv) : REnv := fun x =>
  match σ x with
  | some (dx, ks) => if dx ≤ d then some (dx, ks) else none
  | none          => none

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

structure St where
  ptr : Var → List Nat   -- 变量的值里的指针（区域编号）
  rs  : RSt

def St.empty : St := ⟨fun _ => [], ⟨fun _ => false, fun _ => 0, 0, 0⟩⟩

def gather (ptr : Var → List Nat) : List Var → List Nat
  | []      => []
  | y :: ys => ptr y ++ gather ptr ys

def exec1 (s : St) : Cmd → Option St
  | .decl x => some ⟨upd s.ptr x [], s.rs⟩
  | .ralloc x k =>
    if k < s.rs.d ∧ s.rs.alive (s.rs.rid k) = true then
      some ⟨upd s.ptr x [s.rs.rid k], s.rs⟩
    else none
  | .pack x ys  => some ⟨upd s.ptr x (gather s.ptr ys), s.rs⟩
  | .empty x _  => some ⟨upd s.ptr x [], s.rs⟩
  | .copy x y   => some ⟨upd s.ptr y (s.ptr x), s.rs⟩
  | .read x     => if (s.ptr x).all s.rs.alive = true then some s else none

def exec : P → St → Option St
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

/-- 指针 `ps` 都是区域 `ks` 里某个区域的编号。 -/
abbrev Covers (r : RSt) (ps ks : List Nat) : Prop := ∀ i ∈ ps, ∃ k ∈ ks, r.rid k = i

structure Good (d : Nat) (σ : REnv) (s : St) : Prop where
  stk   : StackOk d s.rs
  scope : ∀ x dx ks, σ x = some (dx, ks) → dx ≤ d
  ptrs  : ∀ x dx ks, σ x = some (dx, ks) → (∀ k ∈ ks, k < dx) ∧ Covers s.rs (s.ptr x) ks

theorem good_empty : Good 0 (fun _ => none) St.empty :=
  ⟨Core.Regions.Model.good_empty.stk, fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩

theorem below_ok {n : Nat} {ks : List Nat} (h : below n ks = true) : ∀ k ∈ ks, k < n := by
  induction ks with
  | nil => intro k hk; simp at hk
  | cons j ks ih =>
    simp only [below, Bool.and_eq_true, decide_eq_true_eq] at h
    intro k hk
    rcases List.mem_cons.mp hk with he | hk
    · rw [he]; exact h.1
    · exact ih h.2 k hk

theorem gather_covers {d : Nat} {σ : REnv} {s : St} (hg : Good d σ s) {ys : List Var} :
    ∀ {ks : List Nat}, regs σ ys = some ks → Covers s.rs (gather s.ptr ys) ks := by
  induction ys with
  | nil =>
    intro ks _ i hi
    simp [gather] at hi
  | cons y ys ih =>
    intro ks h
    simp only [regs] at h
    split at h
    · rename_i dy ky rs hy hr
      cases h
      intro i hi
      simp only [gather, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨k, hk, he⟩ := (hg.ptrs y dy ky hy).2 i hi
        exact ⟨k, List.mem_append_left _ hk, he⟩
      · obtain ⟨k, hk, he⟩ := ih hr i hi
        exact ⟨k, List.mem_append_right _ hk, he⟩
    · contradiction

/-- 给一个变量存进新值：新值的指针被它的类型的区域覆盖，这些区域都比变量活得久。 -/
theorem good_set {d : Nat} {σ : REnv} {s : St} {x : Var} {dx : Nat} {ks ps : List Nat}
    (hg : Good d σ s) (hdx : dx ≤ d) (hks : ∀ k ∈ ks, k < dx) (hps : Covers s.rs ps ks) :
    Good d (upd σ x (some (dx, ks))) ⟨upd s.ptr x ps, s.rs⟩ := by
  refine ⟨hg.stk, ?_, ?_⟩
  · intro z dz kz hz
    by_cases hzx : z = x
    · rw [hzx, upd_same] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at hz
      rw [← hz.1]
      exact hdx
    · rw [upd_other σ (some (dx, ks)) hzx] at hz
      exact hg.scope z dz kz hz
  · intro z dz kz hz
    by_cases hzx : z = x
    · rw [hzx, upd_same] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at hz
      rw [← hz.1, ← hz.2]
      refine ⟨hks, ?_⟩
      show Covers s.rs (upd s.ptr x ps z) ks
      rw [hzx, upd_same]
      exact hps
    · rw [upd_other σ (some (dx, ks)) hzx] at hz
      obtain ⟨h1, h2⟩ := hg.ptrs z dz kz hz
      refine ⟨h1, ?_⟩
      show Covers s.rs (upd s.ptr x ps z) kz
      rw [upd_other s.ptr ps hzx]
      exact h2

/-! ## 进入、离开区域 -/

theorem enter_good {d : Nat} {σ : REnv} {s : St} (hg : Good d σ s) :
    Good (d + 1) σ ⟨s.ptr, enterR s.rs⟩ := by
  refine ⟨enter_ok hg.stk, ?_, ?_⟩
  · intro x dx ks hx
    exact Nat.le_succ_of_le (hg.scope x dx ks hx)
  · intro x dx ks hx
    obtain ⟨h1, h2⟩ := hg.ptrs x dx ks hx
    refine ⟨h1, ?_⟩
    intro i hi
    obtain ⟨k, hk, he⟩ := h2 i hi
    have hkd : k < d := Nat.lt_of_lt_of_le (h1 k hk) (hg.scope x dx ks hx)
    have hne : k ≠ s.rs.d := by rw [hg.stk.depth]; exact Nat.ne_of_lt hkd
    refine ⟨k, hk, ?_⟩
    show upd s.rs.rid s.rs.d s.rs.next k = i
    rw [upd_other s.rs.rid s.rs.next hne]
    exact he

theorem restrict_some {d : Nat} {σ : REnv} {x : Var} {dx : Nat} {ks : List Nat}
    (h : restrict d σ x = some (dx, ks)) : σ x = some (dx, ks) ∧ dx ≤ d := by
  simp only [restrict] at h
  split at h
  · rename_i dx' ks' hx
    split at h
    · rename_i hle
      cases h
      exact ⟨hx, hle⟩
    · contradiction
  · contradiction

theorem leave_good {d : Nat} {σ : REnv} {s : St} (hg : Good (d + 1) σ s) :
    Good d (restrict d σ) ⟨s.ptr, leaveR s.rs d⟩ := by
  refine ⟨leave_ok hg.stk, ?_, ?_⟩
  · intro x dx ks hx
    exact (restrict_some hx).2
  · intro x dx ks hx
    exact hg.ptrs x dx ks (restrict_some hx).1

/-! ## 单步与程序 -/

theorem step1 {d : Nat} {σ σ' : REnv} {s : St} {c : Cmd}
    (hc : check1 d σ c = some σ') (hg : Good d σ s) :
    ∃ s', exec1 s c = some s' ∧ Good d σ' s' := by
  cases c with
  | decl x =>
    simp only [check1] at hc
    split at hc
    · cases hc
      exact ⟨⟨upd s.ptr x [], s.rs⟩, rfl,
        good_set hg (Nat.le_refl d) (fun k hk => by simp at hk) (fun i hi => by simp at hi)⟩
    · contradiction
  | ralloc x k =>
    simp only [check1] at hc
    split at hc
    · rename_i dx ks0 hx
      split at hc
      · rename_i hk
        cases hc
        have hdx := hg.scope x dx ks0 hx
        have hkd : k < d := Nat.lt_of_lt_of_le hk hdx
        have hlive := hg.stk.live k hkd
        refine ⟨⟨upd s.ptr x [s.rs.rid k], s.rs⟩, ?_, good_set hg hdx ?_ ?_⟩
        · simp [exec1, hg.stk.depth, hkd, hlive]
        · intro j hj
          rw [List.mem_singleton] at hj
          rw [hj]
          exact hk
        · intro i hi
          rw [List.mem_singleton] at hi
          exact ⟨k, List.mem_singleton.mpr rfl, hi.symm⟩
      · contradiction
    · contradiction
  | pack x ys =>
    simp only [check1] at hc
    split at hc
    · rename_i dx ks0 ks hx hr
      split at hc
      · rename_i hb
        cases hc
        exact ⟨⟨upd s.ptr x (gather s.ptr ys), s.rs⟩, rfl,
          good_set hg (hg.scope x dx ks0 hx) (below_ok hb) (gather_covers hg hr)⟩
      · contradiction
    · contradiction
  | empty x ks =>
    simp only [check1] at hc
    split at hc
    · rename_i dx ks0 hx
      split at hc
      · rename_i hb
        cases hc
        exact ⟨⟨upd s.ptr x [], s.rs⟩, rfl,
          good_set hg (hg.scope x dx ks0 hx) (below_ok hb) (fun i hi => by simp at hi)⟩
      · contradiction
    · contradiction
  | copy x y =>
    simp only [check1] at hc
    split at hc
    · rename_i dxx ks dy ks0 hx hy
      split at hc
      · rename_i hb
        cases hc
        exact ⟨⟨upd s.ptr y (s.ptr x), s.rs⟩, rfl,
          good_set hg (hg.scope y dy ks0 hy) (below_ok hb) (hg.ptrs x dxx ks hx).2⟩
      · contradiction
    · contradiction
  | read x =>
    simp only [check1] at hc
    split at hc
    · rename_i dx ks hx
      cases hc
      obtain ⟨h1, h2⟩ := hg.ptrs x dx ks hx
      have hall : (s.ptr x).all s.rs.alive = true := by
        rw [List.all_eq_true]
        intro i hi
        obtain ⟨k, hk, he⟩ := h2 i hi
        rw [← he]
        exact hg.stk.live k (Nat.lt_of_lt_of_le (h1 k hk) (hg.scope x dx ks hx))
      exact ⟨s, by simp [exec1, hall], hg⟩
    · contradiction

theorem sound (p : P) : ∀ {d : Nat} {σ σ' : REnv} {s : St},
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

/-- **`Regions.Data` 主定理。** 检查器接受的程序执行不出错：每次读取时，值里每个引用的区域都活着；
结束时没有区域还活着。 -/
theorem safety_and_no_leak (p : P) (σ' : REnv)
    (h : check p 0 (fun _ => none) = some σ') :
    ∃ s', exec p St.empty = some s' ∧ ∀ i, s'.rs.alive i = false := by
  obtain ⟨s', he, hg⟩ := sound p h good_empty
  refine ⟨s', he, ?_⟩
  intro i
  cases hi : s'.rs.alive i with
  | false => rfl
  | true =>
    obtain ⟨k, hk, _⟩ := hg.stk.only i hi
    exact absurd hk (Nat.not_lt_zero k)

/-! ## 漏掉类型实参的检查器 -/

/-- 算类型的区域时漏掉类型实参：装进结构体的值被当成不含引用，静态效果和 `empty x []` 一样。 -/
def eraseC : Cmd → Cmd
  | .pack x _ => .empty x []
  | c         => c

def eraseP : P → P
  | .skip    => .skip
  | .cmd c   => .cmd (eraseC c)
  | .seq p q => .seq (eraseP p) (eraseP q)
  | .block p => .block (eraseP p)

/-! ## 例子 -/

def seqL : List P → P
  | []      => .skip
  | p :: ps => .seq p (seqL ps)

/-- 外层区域和内层区域的引用装进同一个结构体，在内层读取：接受。 -/
def ok1 : P := .block (seqL
  [.cmd (.decl 0), .cmd (.ralloc 0 0),
   .block (seqL [.cmd (.decl 1), .cmd (.ralloc 1 1), .cmd (.decl 2), .cmd (.pack 2 [0, 1]),
                 .cmd (.read 2)]),
   .cmd (.read 0)])
example : (check ok1 0 (fun _ => none)).isSome = true := rfl

/-- 外层区域的引用装进 `.Some`，复制到外层变量，内层块结束后读取：接受。 -/
def ok2 : P := .block (seqL
  [.cmd (.decl 0), .cmd (.ralloc 0 0), .cmd (.decl 1),
   .block (seqL [.cmd (.decl 2), .cmd (.pack 2 [0]), .cmd (.copy 2 1)]),
   .cmd (.read 1)])
example : (check ok2 0 (fun _ => none)).isSome = true := rfl

/-- 内层区域的引用装进 `.Some(r)` 存到外层变量，块结束后读取：拒绝；不经检查执行出错；
漏掉类型实参的检查器却接受。 -/
def bad1 : P := .block (seqL
  [.cmd (.decl 0),
   .block (seqL [.cmd (.decl 1), .cmd (.ralloc 1 1), .cmd (.pack 0 [1])]),
   .cmd (.read 0)])
example : (check bad1 0 (fun _ => none)).isNone = true := rfl
example : (exec bad1 St.empty).isNone = true := rfl
example : (check (eraseP bad1) 0 (fun _ => none)).isSome = true := rfl

/-- 外层变量存 `.None : Option<&I64 in b>`（`b` 是内层区域）：值里没有指针，但类型带着 `b`，拒绝。 -/
def bad2 : P := .block (seqL [.cmd (.decl 0), .block (.cmd (.empty 0 [1]))])
example : (check bad2 0 (fun _ => none)).isNone = true := rfl

end Core.Regions.Data
