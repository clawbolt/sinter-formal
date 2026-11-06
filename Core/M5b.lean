import Core.M5

/-!
# M5（二）：协变（D2）与 `Mut`

在 M5（一）上加入**引用的类型**：`decl x k` 声明 `x : &T in k`，`k` 是类型里的区域参数。
`x` 可以指向区域 `k` 本身，也可以指向任何比 `k` 活得更久的外层区域 `j ≤ k`。

**协变（D2）**：`&T in 外层` 可以当作 `&T in 内层` 使用。
- `copy x y`：`x : &T in kx`，`y : &T in ky`，只要 `kx ≤ ky` 就允许；
- `ralloc x j`：往外层区域 `j ≤ kx` 里分配，结果也能放进 `x`。

**`Mut`**：D2 规定 `Mut<T>` 只能存可拷贝、不含引用的值。这样的格子不碰区域状态，
所以健全的检查器（`MutRule.plainOnly`）里不需要建模；存引用的格子一律拒绝。

**反例**：如果允许 `Mut` 存引用，并且 `Mut` 也跟着协变（`MutRule.covariant`），
内层代码就能把一个“外层格子”当作“内层格子”，往里写内层区域的引用；
内层区域结束后，外层再从格子里读出来，就是悬空指针。文件末尾的 `escape`
被这个检查器接受，执行却出错。这说明 D2 里“只读是协变的前提”这条限制是必要的。

**主定理** `safety_and_no_leak`：在 `plainOnly` 规则下，检查器接受的程序执行不出错，
结束时没有区域残留。
-/

namespace Core.M5b
open Core.M5 (RSt enterR leaveR StackOk enter_ok leave_ok)

inductive Cmd
  | decl   (x : Var) (k : Nat)          -- x : &T in k
  | ralloc (x : Var) (j : Nat)          -- 在区域 j 里分配，放进 x
  | copy   (x y : Var)                  -- y := x
  | read   (x : Var)
  | cdecl  (c : Var) (k : Nat)          -- c : Mut<&T in k>
  | cview  (v c : Var) (k : Nat)        -- v 是格子 c 的别名，类型看作 Mut<&T in k>
  | cset   (v x : Var)                  -- 通过别名 v 往格子里写 x
  | cget   (c y : Var)                  -- y := 格子 c 里的值

inductive P
  | skip
  | cmd   (c : Cmd)
  | seq   (p q : P)
  | block (p : P)

inductive MutRule | plainOnly | covariant

/-! ## 静态检查 -/

/-- 引用变量：`(作用域深度, 类型里的区域, 是否已赋值)`。 -/
abbrev VEnv := Var → Option (Nat × Nat × Bool)

structure SEnv where
  v : VEnv
  c : Var → Option Nat           -- 格子的区域参数
  w : Var → Option (Var × Nat)   -- 别名：指向哪个格子，看作什么区域

def SEnv.empty : SEnv := ⟨fun _ => none, fun _ => none, fun _ => none⟩

def checkCell (d : Nat) (σ : SEnv) : Cmd → Option SEnv
  | .cdecl c k => if k < d then some { σ with c := upd σ.c c (some k) } else none
  | .cview v c k =>
    match σ.c c with
    | some kc => if kc ≤ k ∧ k < d then some { σ with w := upd σ.w v (some (c, k)) } else none
    | none    => none
  | .cset v x =>
    match σ.w v, σ.v x with
    | some (_, k), some (_, kx, true) => if kx ≤ k then some σ else none
    | _, _ => none
  | .cget c y =>
    match σ.c c, σ.v y with
    | some kc, some (dy, ky, _) =>
      if kc ≤ ky then some { σ with v := upd σ.v y (some (dy, ky, true)) } else none
    | _, _ => none
  | _ => none

def check1 (m : MutRule) (d : Nat) (σ : SEnv) : Cmd → Option SEnv
  | .decl x k =>
    if σ.v x = none ∧ k < d then some { σ with v := upd σ.v x (some (d, k, false)) } else none
  | .ralloc x j =>
    match σ.v x with
    | some (dx, kx, _) =>
      if j ≤ kx then some { σ with v := upd σ.v x (some (dx, kx, true)) } else none
    | none => none
  | .copy x y =>
    match σ.v x, σ.v y with
    | some (_, kx, true), some (dy, ky, _) =>
      if kx ≤ ky then some { σ with v := upd σ.v y (some (dy, ky, true)) } else none
    | _, _ => none
  | .read x =>
    match σ.v x with
    | some (_, _, true) => some σ
    | _                 => none
  | c =>
    match m with
    | .plainOnly => none
    | .covariant => checkCell d σ c

def restrictV (d : Nat) (σ : VEnv) : VEnv := fun x =>
  match σ x with
  | some (dx, kx, b) => if dx ≤ d then some (dx, kx, b) else none
  | none             => none

def check (m : MutRule) : P → Nat → SEnv → Option SEnv
  | .skip,    _, σ => some σ
  | .cmd c,   d, σ => check1 m d σ c
  | .seq p q, d, σ =>
    match check m p d σ with
    | some σ₁ => check m q d σ₁
    | none    => none
  | .block p, d, σ =>
    match check m p (d + 1) σ with
    | some σ₁ => some { σ₁ with v := restrictV d σ₁.v }
    | none    => none

/-! ## 动态语义 -/

structure St where
  ptr   : Var → Option Nat
  cells : Var → Option Nat
  view  : Var → Option Var
  rs    : RSt

def St.empty : St :=
  ⟨fun _ => none, fun _ => none, fun _ => none, ⟨fun _ => false, fun _ => 0, 0, 0⟩⟩

def exec1 (s : St) : Cmd → Option St
  | .decl x _ => some { s with ptr := upd s.ptr x none }
  | .ralloc x j =>
    if j < s.rs.d ∧ s.rs.alive (s.rs.rid j) = true then
      some { s with ptr := upd s.ptr x (some (s.rs.rid j)) }
    else none
  | .copy x y => some { s with ptr := upd s.ptr y (s.ptr x) }
  | .read x =>
    match s.ptr x with
    | some i => if s.rs.alive i = true then some s else none
    | none   => none
  | .cdecl c _ => some { s with cells := upd s.cells c none }
  | .cview v c _ => some { s with view := upd s.view v (some c) }
  | .cset v x =>
    match s.view v with
    | some c => some { s with cells := upd s.cells c (s.ptr x) }
    | none   => none
  | .cget c y => some { s with ptr := upd s.ptr y (s.cells c) }

def exec : P → St → Option St
  | .skip,    s => some s
  | .cmd c,   s => exec1 s c
  | .seq p q, s =>
    match exec p s with
    | some s₁ => exec q s₁
    | none    => none
  | .block p, s =>
    match exec p { s with rs := enterR s.rs } with
    | some s₁ => some { s₁ with rs := leaveR s₁.rs s.rs.d }
    | none    => none

/-! ## 不变式 -/

structure Good (d : Nat) (σ : SEnv) (s : St) : Prop where
  stk   : StackOk d s.rs
  scope : ∀ x dx kx b, σ.v x = some (dx, kx, b) → dx ≤ d ∧ kx < dx
  ptrs  : ∀ x dx kx, σ.v x = some (dx, kx, true) →
    ∃ j, j ≤ kx ∧ s.ptr x = some (s.rs.rid j)

theorem good_empty : Good 0 SEnv.empty St.empty :=
  ⟨⟨rfl, (fun k hk => absurd hk (Nat.not_lt_zero k)),
     (fun _ j _ hj => absurd hj (Nat.not_lt_zero j)),
     (fun k hk => absurd hk (Nat.not_lt_zero k)),
     (fun i hi => by simp [St.empty] at hi)⟩,
   (fun _ _ _ _ h => by simp [SEnv.empty] at h),
   (fun _ _ _ h => by simp [SEnv.empty] at h)⟩

theorem enter_good {d : Nat} {σ : SEnv} {s : St} (hg : Good d σ s) :
    Good (d + 1) σ { s with rs := enterR s.rs } := by
  refine ⟨enter_ok hg.stk, ?_, ?_⟩
  · intro x dx kx b hx
    obtain ⟨h1, h2⟩ := hg.scope x dx kx b hx
    exact ⟨Nat.le_succ_of_le h1, h2⟩
  · intro x dx kx hx
    obtain ⟨j, hj, hp⟩ := hg.ptrs x dx kx hx
    obtain ⟨h1, h2⟩ := hg.scope x dx kx true hx
    have hjd : j < d := Nat.lt_of_le_of_lt hj (Nat.lt_of_lt_of_le h2 h1)
    have hne : j ≠ s.rs.d := by rw [hg.stk.depth]; exact Nat.ne_of_lt hjd
    refine ⟨j, hj, ?_⟩
    show s.ptr x = some (upd s.rs.rid s.rs.d s.rs.next j)
    rw [upd_other s.rs.rid s.rs.next hne]
    exact hp

theorem restrictV_some {d : Nat} {σ : VEnv} {x : Var} {dx kx : Nat} {b : Bool}
    (h : restrictV d σ x = some (dx, kx, b)) : σ x = some (dx, kx, b) ∧ dx ≤ d := by
  simp only [restrictV] at h
  split at h
  · rename_i dx' kx' b' hx
    split at h
    · rename_i hle
      cases h
      exact ⟨hx, hle⟩
    · contradiction
  · contradiction

theorem leave_good {d : Nat} {σ : SEnv} {s : St} (hg : Good (d + 1) σ s) :
    Good d { σ with v := restrictV d σ.v } { s with rs := leaveR s.rs d } := by
  refine ⟨leave_ok hg.stk, ?_, ?_⟩
  · intro x dx kx b hx
    obtain ⟨hx', hle⟩ := restrictV_some hx
    exact ⟨hle, (hg.scope x dx kx b hx').2⟩
  · intro x dx kx hx
    exact hg.ptrs x dx kx (restrictV_some hx).1

/-! ## 单步（`plainOnly`） -/

/-- 改写一个引用变量的静态信息后，其余变量的 `scope` 不受影响。 -/
theorem scope_upd {d : Nat} {σ : SEnv} {s : St} (hg : Good d σ s) {x : Var} {dx kx : Nat}
    {b : Bool} (hdx : dx ≤ d ∧ kx < dx) :
    ∀ z dz kz bz, upd σ.v x (some (dx, kx, b)) z = some (dz, kz, bz) → dz ≤ d ∧ kz < dz := by
  intro z dz kz bz hz
  by_cases hzx : z = x
  · rw [hzx, upd_same] at hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl, rfl⟩ := hz
    exact hdx
  · rw [upd_other σ.v (some (dx, kx, b)) hzx] at hz
    exact hg.scope z dz kz bz hz

theorem step1 {d : Nat} {σ σ' : SEnv} {s : St} {c : Cmd}
    (hc : check1 .plainOnly d σ c = some σ') (hg : Good d σ s) :
    ∃ s', exec1 s c = some s' ∧ Good d σ' s' := by
  cases c with
  | decl x k =>
    simp only [check1] at hc
    split at hc
    · rename_i hcond
      obtain ⟨_, hk⟩ := hcond
      cases hc
      refine ⟨{ s with ptr := upd s.ptr x none }, rfl,
        ⟨hg.stk, scope_upd hg ⟨Nat.le_refl d, hk⟩, ?_⟩⟩
      intro z dz kz hz
      change upd σ.v x (some (d, k, false)) z = some (dz, kz, true) at hz
      by_cases hzx : z = x
      · rw [hzx] at hz
        simp at hz
      · rw [upd_other σ.v (some (d, k, false)) hzx] at hz
        obtain ⟨j, hj, hp⟩ := hg.ptrs z dz kz hz
        refine ⟨j, hj, ?_⟩
        show upd s.ptr x none z = some (s.rs.rid j)
        rw [upd_other s.ptr none hzx]
        exact hp
    · contradiction
  | ralloc x j =>
    simp only [check1] at hc
    split at hc
    · rename_i dx kx b hx
      split at hc
      · rename_i hj
        cases hc
        obtain ⟨hdx, hkx⟩ := hg.scope x dx kx b hx
        have hjd : j < d := Nat.lt_of_le_of_lt hj (Nat.lt_of_lt_of_le hkx hdx)
        have hlive := hg.stk.live j hjd
        refine ⟨{ s with ptr := upd s.ptr x (some (s.rs.rid j)) }, ?_,
          ⟨hg.stk, scope_upd hg ⟨hdx, hkx⟩, ?_⟩⟩
        · simp [exec1, hg.stk.depth, hjd, hlive]
        · intro z dz kz hz
          change upd σ.v x (some (dx, kx, true)) z = some (dz, kz, true) at hz
          by_cases hzx : z = x
          · rw [hzx, upd_same] at hz
            simp only [Option.some.injEq, Prod.mk.injEq] at hz
            obtain ⟨rfl, rfl, _⟩ := hz
            refine ⟨j, hj, ?_⟩
            show upd s.ptr x (some (s.rs.rid j)) z = some (s.rs.rid j)
            rw [hzx, upd_same]
          · rw [upd_other σ.v (some (dx, kx, true)) hzx] at hz
            obtain ⟨j', hj', hp⟩ := hg.ptrs z dz kz hz
            refine ⟨j', hj', ?_⟩
            show upd s.ptr x (some (s.rs.rid j)) z = some (s.rs.rid j')
            rw [upd_other s.ptr (some (s.rs.rid j)) hzx]
            exact hp
      · contradiction
    · contradiction
  | copy x y =>
    simp only [check1] at hc
    split at hc
    · rename_i dxx kx dy ky b hx hy
      split at hc
      · rename_i hk
        cases hc
        obtain ⟨j, hj, hpx⟩ := hg.ptrs x dxx kx hx
        refine ⟨{ s with ptr := upd s.ptr y (s.ptr x) }, rfl,
          ⟨hg.stk, scope_upd hg (hg.scope y dy ky b hy), ?_⟩⟩
        intro z dz kz hz
        change upd σ.v y (some (dy, ky, true)) z = some (dz, kz, true) at hz
        by_cases hzy : z = y
        · rw [hzy, upd_same] at hz
          simp only [Option.some.injEq, Prod.mk.injEq] at hz
          obtain ⟨rfl, rfl, _⟩ := hz
          refine ⟨j, Nat.le_trans hj hk, ?_⟩
          show upd s.ptr y (s.ptr x) z = some (s.rs.rid j)
          rw [hzy, upd_same]
          exact hpx
        · rw [upd_other σ.v (some (dy, ky, true)) hzy] at hz
          obtain ⟨j', hj', hp⟩ := hg.ptrs z dz kz hz
          refine ⟨j', hj', ?_⟩
          show upd s.ptr y (s.ptr x) z = some (s.rs.rid j')
          rw [upd_other s.ptr (s.ptr x) hzy]
          exact hp
      · contradiction
    · contradiction
  | read x =>
    simp only [check1] at hc
    split at hc
    · rename_i dxx kx hx
      cases hc
      obtain ⟨j, hj, hp⟩ := hg.ptrs x dxx kx hx
      obtain ⟨hdx, hkx⟩ := hg.scope x dxx kx true hx
      have hjd : j < d := Nat.lt_of_le_of_lt hj (Nat.lt_of_lt_of_le hkx hdx)
      exact ⟨s, by simp [exec1, hp, hg.stk.live j hjd], hg⟩
    · contradiction
  | cdecl c k => simp [check1] at hc
  | cview v c k => simp [check1] at hc
  | cset v x => simp [check1] at hc
  | cget c y => simp [check1] at hc

theorem sound (p : P) : ∀ {d : Nat} {σ σ' : SEnv} {s : St},
    check .plainOnly p d σ = some σ' → Good d σ s →
    ∃ s', exec p s = some s' ∧ Good d σ' s' := by
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
      refine ⟨{ s₁ with rs := leaveR s₁.rs s.rs.d }, by simp [exec, he₁], ?_⟩
      rw [hg.stk.depth]
      exact leave_good hg₁
    · contradiction

/-! ## 主定理 -/

/-- **M5（二）主定理。** 在 D2 的规则下（只读引用协变，`Mut` 不存引用），
检查器接受的程序执行不出错，结束时没有区域残留。 -/
theorem safety_and_no_leak (p : P) (σ' : SEnv)
    (h : check .plainOnly p 0 SEnv.empty = some σ') :
    ∃ s', exec p St.empty = some s' ∧ ∀ i, s'.rs.alive i = false := by
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

/-- 协变：外层区域的引用 `x : &T in 0` 复制给内层类型的 `y : &T in 1`，接受。 -/
def cov1 : P := .block (seqL
  [.cmd (.decl 0 0), .cmd (.ralloc 0 0),
   .block (seqL [.cmd (.decl 1 1), .cmd (.copy 0 1), .cmd (.read 1)])])
example : (check .plainOnly cov1 0 SEnv.empty).isSome = true := rfl

/-- 往外层区域里分配，放进内层类型的变量：接受。 -/
def cov2 : P := .block (.block (seqL [.cmd (.decl 0 1), .cmd (.ralloc 0 0), .cmd (.read 0)]))
example : (check .plainOnly cov2 0 SEnv.empty).isSome = true := rfl

/-- 反方向：内层引用 `&T in 1` 复制给外层类型 `&T in 0`，拒绝。 -/
def contra : P := .block (seqL
  [.cmd (.decl 0 0),
   .block (seqL [.cmd (.decl 1 1), .cmd (.ralloc 1 1), .cmd (.copy 1 0)])])
example : (check .plainOnly contra 0 SEnv.empty).isNone = true := rfl

/-- 反例：外层格子 `c : Mut<&T in 0>`；内层把它看作 `Mut<&T in 1>`（Mut 也协变），
写进内层区域的引用；内层结束后外层读出来再使用。 -/
def escape : P := .block (seqL
  [.cmd (.cdecl 9 0),
   .block (seqL [.cmd (.decl 0 1), .cmd (.ralloc 0 1), .cmd (.cview 8 9 1), .cmd (.cset 8 0)]),
   .cmd (.decl 1 0), .cmd (.cget 9 1), .cmd (.read 1)])

/-- 如果 `Mut` 存引用并且跟着协变，检查器接受 `escape`…… -/
example : (check .covariant escape 0 SEnv.empty).isSome = true := rfl
/-- ……但执行时读到了已经结束的区域。 -/
example : (exec escape St.empty).isNone = true := rfl
/-- D2 的规则（`Mut` 不存引用）拒绝它。 -/
example : (check .plainOnly escape 0 SEnv.empty).isNone = true := rfl

end Core.M5b
