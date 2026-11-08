import Core.M5

/-!
# M16（一）：含引用的数据类型的协变

**问题**：M15 让 `Option<&I64 in a>`、`Pair<&I64 in x, &I64 in y>` 这样的值进了区域检查，
但实例之间不协变：外层的 `Option<&I64 in a>` 不能当作 `Option<&I64 in b>`（`b` 是内层区域）用。
引用本身是协变的（D2，M5（二））：外层区域的引用可以当作内层的用。这里证明只读的数据类型也可以。

**做法**：变量有**固定的类型**：类型里每个引用的位置一个区域（`ks`，例如 `Pair<&in 0, &in 1>` 是 `[0, 1]`）。
值是同样多的槽，每个槽要么没有指针（`.None` 的载荷），要么指向某个区域。命令：
- `decl x ks`：声明 `x`，类型的区域都要已经存在，值的槽都是空的；
- `mk x js`：造一个值放进 `x`（`.Some(alloc(a, …))`、`.None`、`Pair { … }`），
  槽 `i` 指向区域 `js[i]`（或者为空），要求 `js[i] ≤ ks[i]`：往更外层的区域里分配也可以放进来；
- `copy x y`：`y := x`，**协变**：`x` 的类型的每个区域都不比 `y` 的对应区域短命（逐个 `≤`）；
- `read x`：读出值里的每个引用。

**不变式**：槽 `i` 里的指针是某个区域 `j ≤ ks[i]` 的编号（不一定正好是 `ks[i]`，这正是协变需要的放宽），
类型的区域都比变量活得久（`ks[i] < dx`）。

**主定理** `safety_and_no_leak`：检查器接受的程序执行不出错，结束时没有区域还活着。

**只读是前提**：协变只对只读的值成立。可以修改的位置（`inout` 实参、`Mut`）必须不变：
M5（二）的 `escape` 说明可写的格子跟着协变时，内层代码能往外层的格子里写内层区域的引用。
编译器里 C19 已经让 inout 实参不变。
-/

namespace Core.M16
open Core.M5 (RSt StackOk enterR leaveR enter_ok leave_ok)

inductive Cmd
  | decl (x : Var) (ks : List Nat)
  | mk   (x : Var) (js : List (Option Nat))
  | copy (x y : Var)
  | read (x : Var)

inductive P
  | skip
  | cmd   (c : Cmd)
  | seq   (p q : P)
  | block (p : P)

/-! ## 静态检查 -/

/-- 变量的静态信息：`some (dx, ks)`：作用域深度 `dx`，类型里每个引用的位置的区域 `ks`。 -/
abbrev REnv := Var → Option (Nat × List Nat)

def below (n : Nat) : List Nat → Bool
  | []      => true
  | k :: ks => decide (k < n) && below n ks

/-- 造出的值放得进类型：槽数相同，每个指针的区域不比类型里对应的区域短命。 -/
def fits : List (Option Nat) → List Nat → Bool
  | [],                 []      => true
  | Option.none :: js,  _ :: ks => fits js ks
  | Option.some j :: js, k :: ks => decide (j ≤ k) && fits js ks
  | _,                  _       => false

/-- 协变：逐个位置 `≤`。 -/
def leAll : List Nat → List Nat → Bool
  | [],      []      => true
  | a :: as, b :: bs => decide (a ≤ b) && leAll as bs
  | _,       _       => false

def check1 (d : Nat) (σ : REnv) : Cmd → Option REnv
  | .decl x ks => if σ x = none ∧ below d ks = true then some (upd σ x (some (d, ks))) else none
  | .mk x js =>
    match σ x with
    | some (dx, ks) => if fits js ks then some (upd σ x (some (dx, ks))) else none
    | none          => none
  | .copy x y =>
    match σ x, σ y with
    | some (_, kx), some (dy, ky) => if leAll kx ky then some (upd σ y (some (dy, ky))) else none
    | _, _                        => none
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
  ptr : Var → List (Option Nat)   -- 每个槽：空，或者指向的区域编号
  rs  : RSt

def St.empty : St := ⟨fun _ => [], ⟨fun _ => false, fun _ => 0, 0, 0⟩⟩

/-- 值里的指针都活着。 -/
def liveAll (alive : Nat → Bool) : List (Option Nat) → Bool
  | []                => true
  | Option.none :: vs   => liveAll alive vs
  | Option.some i :: vs => alive i && liveAll alive vs

/-- 造值时用到的区域都存在。 -/
def okAll (d : Nat) : List (Option Nat) → Bool
  | []                => true
  | Option.none :: js   => okAll d js
  | Option.some j :: js => decide (j < d) && okAll d js

def exec1 (s : St) : Cmd → Option St
  | .decl x ks => some ⟨upd s.ptr x (List.replicate ks.length Option.none), s.rs⟩
  | .mk x js =>
    if okAll s.rs.d js then some ⟨upd s.ptr x (js.map (Option.map s.rs.rid)), s.rs⟩ else none
  | .copy x y => some ⟨upd s.ptr y (s.ptr x), s.rs⟩
  | .read x   => if liveAll s.rs.alive (s.ptr x) then some s else none

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

/-- 槽和类型对应：槽 `i` 为空，或者是某个区域 `j ≤ ks[i]` 的编号。 -/
inductive Slots (ρ : Nat → Nat) : List (Option Nat) → List Nat → Prop
  | nil  : Slots ρ [] []
  | skip {vs : List (Option Nat)} {ks : List Nat} {k : Nat} :
      Slots ρ vs ks → Slots ρ (Option.none :: vs) (k :: ks)
  | ptr  {vs : List (Option Nat)} {ks : List Nat} {k j : Nat} :
      j ≤ k → Slots ρ vs ks → Slots ρ (Option.some (ρ j) :: vs) (k :: ks)

structure Good (d : Nat) (σ : REnv) (s : St) : Prop where
  stk   : StackOk d s.rs
  scope : ∀ x dx ks, σ x = some (dx, ks) → dx ≤ d
  types : ∀ x dx ks, σ x = some (dx, ks) → ∀ k ∈ ks, k < dx
  slots : ∀ x dx ks, σ x = some (dx, ks) → Slots s.rs.rid (s.ptr x) ks

theorem good_empty : Good 0 (fun _ => none) St.empty :=
  ⟨Core.M5.good_empty.stk, fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h,
   fun _ _ _ h => by simp at h⟩

theorem below_ok {n : Nat} {ks : List Nat} (h : below n ks = true) : ∀ k ∈ ks, k < n := by
  induction ks with
  | nil => intro k hk; simp at hk
  | cons j ks ih =>
    simp only [below, Bool.and_eq_true, decide_eq_true_eq] at h
    intro k hk
    rcases List.mem_cons.mp hk with he | hk
    · rw [he]; exact h.1
    · exact ih h.2 k hk

theorem slots_replicate (ρ : Nat → Nat) (ks : List Nat) :
    Slots ρ (List.replicate ks.length Option.none) ks := by
  induction ks with
  | nil => exact Slots.nil
  | cons k ks ih =>
    show Slots ρ (Option.none :: List.replicate ks.length Option.none) (k :: ks)
    exact Slots.skip ih

theorem slots_mk (ρ : Nat → Nat) (js : List (Option Nat)) :
    ∀ ks : List Nat, fits js ks = true → Slots ρ (js.map (Option.map ρ)) ks := by
  induction js with
  | nil =>
    intro ks h
    cases ks with
    | nil => exact Slots.nil
    | cons _ _ => simp [fits] at h
  | cons o js ih =>
    intro ks h
    cases ks with
    | nil => cases o <;> simp [fits] at h
    | cons k ks =>
      cases o with
      | none =>
        simp only [fits] at h
        show Slots ρ (Option.none :: js.map (Option.map ρ)) (k :: ks)
        exact Slots.skip (ih ks h)
      | some j =>
        simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at h
        show Slots ρ (Option.some (ρ j) :: js.map (Option.map ρ)) (k :: ks)
        exact Slots.ptr h.1 (ih ks h.2)

/-- 协变：类型的区域逐个放宽（变成更内层的），槽和类型仍然对应。 -/
theorem slots_le {ρ : Nat → Nat} {vs : List (Option Nat)} {ks : List Nat} (hs : Slots ρ vs ks) :
    ∀ {ks' : List Nat}, leAll ks ks' = true → Slots ρ vs ks' := by
  induction hs with
  | nil =>
    intro ks' h
    cases ks' with
    | nil => exact Slots.nil
    | cons _ _ => simp [leAll] at h
  | skip _ ih =>
    intro ks' h
    cases ks' with
    | nil => simp [leAll] at h
    | cons _ _ =>
      simp only [leAll, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Slots.skip (ih h.2)
  | ptr hj _ ih =>
    intro ks' h
    cases ks' with
    | nil => simp [leAll] at h
    | cons _ _ =>
      simp only [leAll, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Slots.ptr (Nat.le_trans hj h.1) (ih h.2)

theorem ok_of_fits {n : Nat} (js : List (Option Nat)) :
    ∀ ks : List Nat, fits js ks = true → (∀ k ∈ ks, k < n) → okAll n js = true := by
  induction js with
  | nil => intro _ _ _; rfl
  | cons o js ih =>
    intro ks h hk
    cases ks with
    | nil => cases o <;> simp [fits] at h
    | cons k ks =>
      have hk' : ∀ k' ∈ ks, k' < n := fun k' hm => hk k' (List.mem_cons.mpr (Or.inr hm))
      cases o with
      | none =>
        simp only [fits] at h
        simp only [okAll]
        exact ih ks h hk'
      | some j =>
        simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at h
        simp only [okAll, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Nat.lt_of_le_of_lt h.1 (hk k (List.mem_cons.mpr (Or.inl rfl))), ih ks h.2 hk'⟩

theorem live_of_slots {d : Nat} {r : RSt} (hst : StackOk d r) {vs : List (Option Nat)} {ks : List Nat}
    (hs : Slots r.rid vs ks) : (∀ k ∈ ks, k < d) → liveAll r.alive vs = true := by
  induction hs with
  | nil => intro _; rfl
  | skip _ ih =>
    intro hk
    simp only [liveAll]
    exact ih (fun k' hm => hk k' (List.mem_cons.mpr (Or.inr hm)))
  | @ptr _ _ k j hj _ ih =>
    intro hk
    simp only [liveAll, Bool.and_eq_true]
    exact ⟨hst.live j (Nat.lt_of_le_of_lt hj (hk k (List.mem_cons.mpr (Or.inl rfl)))),
      ih (fun k' hm => hk k' (List.mem_cons.mpr (Or.inr hm)))⟩

theorem slots_enter {ρ : Nat → Nat} {m n : Nat} {vs : List (Option Nat)} {ks : List Nat}
    (hs : Slots ρ vs ks) : (∀ k ∈ ks, k < m) → Slots (upd ρ m n) vs ks := by
  induction hs with
  | nil => intro _; exact Slots.nil
  | skip _ ih =>
    intro hk
    exact Slots.skip (ih (fun k' hm => hk k' (List.mem_cons.mpr (Or.inr hm))))
  | @ptr _ _ k j hj _ ih =>
    intro hk
    have hlt : j < m := Nat.lt_of_le_of_lt hj (hk k (List.mem_cons.mpr (Or.inl rfl)))
    have he : upd ρ m n j = ρ j := upd_other ρ n (Nat.ne_of_lt hlt)
    rw [← he]
    exact Slots.ptr hj (ih (fun k' hm => hk k' (List.mem_cons.mpr (Or.inr hm))))

/-- 给一个变量存进新值。 -/
theorem good_set {d : Nat} {σ : REnv} {s : St} {x : Var} {dx : Nat} {ks : List Nat}
    {vs : List (Option Nat)} (hg : Good d σ s) (hdx : dx ≤ d) (hks : ∀ k ∈ ks, k < dx)
    (hvs : Slots s.rs.rid vs ks) :
    Good d (upd σ x (some (dx, ks))) ⟨upd s.ptr x vs, s.rs⟩ := by
  refine ⟨hg.stk, ?_, ?_, ?_⟩
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
      exact hks
    · rw [upd_other σ (some (dx, ks)) hzx] at hz
      exact hg.types z dz kz hz
  · intro z dz kz hz
    by_cases hzx : z = x
    · rw [hzx, upd_same] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at hz
      rw [← hz.2]
      show Slots s.rs.rid (upd s.ptr x vs z) ks
      rw [hzx, upd_same]
      exact hvs
    · rw [upd_other σ (some (dx, ks)) hzx] at hz
      show Slots s.rs.rid (upd s.ptr x vs z) kz
      rw [upd_other s.ptr vs hzx]
      exact hg.slots z dz kz hz

/-! ## 进入、离开区域 -/

theorem enter_good {d : Nat} {σ : REnv} {s : St} (hg : Good d σ s) :
    Good (d + 1) σ ⟨s.ptr, enterR s.rs⟩ := by
  refine ⟨enter_ok hg.stk, ?_, hg.types, ?_⟩
  · intro x dx ks hx
    exact Nat.le_succ_of_le (hg.scope x dx ks hx)
  · intro x dx ks hx
    exact slots_enter (hg.slots x dx ks hx) (fun k hk => by
      rw [hg.stk.depth]
      exact Nat.lt_of_lt_of_le (hg.types x dx ks hx k hk) (hg.scope x dx ks hx))

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
  refine ⟨leave_ok hg.stk, ?_, ?_, ?_⟩
  · intro x dx ks hx
    exact (restrict_some hx).2
  · intro x dx ks hx
    exact hg.types x dx ks (restrict_some hx).1
  · intro x dx ks hx
    exact hg.slots x dx ks (restrict_some hx).1

/-! ## 单步与程序 -/

theorem step1 {d : Nat} {σ σ' : REnv} {s : St} {c : Cmd}
    (hc : check1 d σ c = some σ') (hg : Good d σ s) :
    ∃ s', exec1 s c = some s' ∧ Good d σ' s' := by
  cases c with
  | decl x ks =>
    simp only [check1] at hc
    split at hc
    · rename_i hx
      cases hc
      exact ⟨⟨upd s.ptr x (List.replicate ks.length Option.none), s.rs⟩, rfl,
        good_set hg (Nat.le_refl d) (below_ok hx.2) (slots_replicate _ ks)⟩
    · contradiction
  | mk x js =>
    simp only [check1] at hc
    split at hc
    · rename_i dx ks hx
      split at hc
      · rename_i hf
        cases hc
        have hdx := hg.scope x dx ks hx
        have hks := hg.types x dx ks hx
        have hok : okAll s.rs.d js = true := by
          rw [hg.stk.depth]
          exact ok_of_fits js ks hf (fun k hk => Nat.lt_of_lt_of_le (hks k hk) hdx)
        exact ⟨⟨upd s.ptr x (js.map (Option.map s.rs.rid)), s.rs⟩, by simp [exec1, hok],
          good_set hg hdx hks (slots_mk _ js ks hf)⟩
      · contradiction
    · contradiction
  | copy x y =>
    simp only [check1] at hc
    split at hc
    · rename_i dxx kx dy ky hx hy
      split at hc
      · rename_i hle
        cases hc
        exact ⟨⟨upd s.ptr y (s.ptr x), s.rs⟩, rfl,
          good_set hg (hg.scope y dy ky hy) (hg.types y dy ky hy) (slots_le (hg.slots x dxx kx hx) hle)⟩
      · contradiction
    · contradiction
  | read x =>
    simp only [check1] at hc
    split at hc
    · rename_i dx ks hx
      cases hc
      have hlive := live_of_slots hg.stk (hg.slots x dx ks hx)
        (fun k hk => Nat.lt_of_lt_of_le (hg.types x dx ks hx k hk) (hg.scope x dx ks hx))
      exact ⟨s, by simp [exec1, hlive], hg⟩
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

/-- **M16（一）主定理。** 带协变的检查器接受的程序执行不出错：每次读取时，值里每个引用的区域都活着；
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

/-! ## 例子 -/

def seqL : List P → P
  | []      => .skip
  | p :: ps => .seq p (seqL ps)

/-- 外层的 `Option<&I64 in a>`（区域 0）复制给内层块里的 `Option<&I64 in b>`（区域 1）：协变，接受。 -/
def cov1 : P := .block (seqL
  [.cmd (.decl 0 [0]), .cmd (.mk 0 [some 0]),
   .block (seqL [.cmd (.decl 1 [1]), .cmd (.copy 0 1), .cmd (.read 1)]),
   .cmd (.read 0)])
example : (check cov1 0 (fun _ => none)).isSome = true := rfl

/-- `Pair<&in a, &in b>` 复制给 `Pair<&in b, &in b>`：逐个位置协变，接受；`.None` 也放得进。 -/
def cov2 : P := .block (.block (seqL
  [.cmd (.decl 0 [0, 1]), .cmd (.mk 0 [some 0, some 1]), .cmd (.decl 1 [1, 1]), .cmd (.copy 0 1),
   .cmd (.read 1), .cmd (.decl 2 [1]), .cmd (.mk 2 [none]), .cmd (.read 2)]))
example : (check cov2 0 (fun _ => none)).isSome = true := rfl

/-- 反方向：内层的 `Option<&I64 in b>` 复制给外层的 `Option<&I64 in a>`，块结束后读：拒绝；
不经检查执行，读到已经结束的区域，出错。 -/
def contra : P := .block (seqL
  [.cmd (.decl 0 [0]),
   .block (seqL [.cmd (.decl 1 [1]), .cmd (.mk 1 [some 1]), .cmd (.copy 1 0)]),
   .cmd (.read 0)])
example : (check contra 0 (fun _ => none)).isNone = true := rfl
example : (exec contra St.empty).isNone = true := rfl

/-- 往类型是外层区域的槽里放内层区域的指针：拒绝。 -/
def badMk : P := .block (.block (seqL [.cmd (.decl 0 [0]), .cmd (.mk 0 [some 1])]))
example : (check badMk 0 (fun _ => none)).isNone = true := rfl

end Core.M16
