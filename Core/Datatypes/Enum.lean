import Core.Basic

/-!
# 枚举（ADT）——构造、按移动的 `match`、按标签的析构

一个枚举类型，变体由 `D : List Bool` 给出：`D[i] = true` 表示第 `i` 个变体带一个 `Box` 载荷。
变量有静态类型 `Γ x`（`box` 或 `enum`），整个程序里不变（对应 `var x: T`）。

**语句**
* `alloc x` / `free x` / `use x` / `move x y`：同 `Ownership.Branch`，`alloc`、`free` 只用于 `box`；
* `mk x i none`：`x = .Vi`（无载荷变体）；`mk x i (some y)`：`x = .Vi(y)`，把 `y` 移进载荷；
* `mat x y arms`：`match x { .V0(y) => arms[0], … }`，按移动匹配：`x` 被拆开，载荷移给 `y`。

**静态检查**：`match` 必须穷尽（`arms.length = D.length`）；第 `i` 个分支开始时
`x` 为 `no`，`y` 在带载荷的变体里为 `yes`、否则为 `no`；各分支结束状态合并（不一致的变成 `maybe`）。

**动态语义**：每个位置有 `tag` 和 `pay`（载荷位置）。`match` 按运行时标签选分支，
没有对应分支就卡住（返回 `none`）——所以穷尽性是安全的必要条件。
作用域结束时按 drop flag 析构：`box` 直接释放；`enum` 按运行时标签决定是否先释放载荷。

**主定理** `safety_and_no_leak`：检查器接受的程序，执行和作用域结束时的析构都不出错，结束时堆上没有活着的值。
-/

namespace Core.Datatypes.Enum

inductive Own | no | yes | maybe
  deriving DecidableEq, Repr

inductive Ty | box | enum
  deriving DecidableEq, Repr

abbrev SEnv := Var → Own

/-- 第 `t` 个变体是否带载荷。 -/
def hasPay (D : List Bool) (t : Nat) : Bool := D.getD t false

inductive Stmt
  | alloc (x : Var)
  | free  (x : Var)
  | use   (x : Var)
  | move  (x y : Var)
  | mk    (x : Var) (i : Nat) (o : Option Var)

inductive Item
  | stmt (t : Stmt)
  | mat  (x y : Var) (arms : List (List Stmt))

/-! ## 静态检查 -/

section
variable (Γ : Var → Ty) (D : List Bool) (N : Nat)

def checkS (σ : SEnv) : Stmt → Option SEnv
  | .alloc x => if Γ x = .box ∧ σ x = .no ∧ x < N then some (upd σ x .yes) else none
  | .free x  => if Γ x = .box ∧ σ x = .yes then some (upd σ x .no) else none
  | .use x   => if σ x = .yes then some σ else none
  | .move x y =>
    if x ≠ y ∧ Γ x = Γ y ∧ σ x = .yes ∧ σ y = .no ∧ y < N
    then some (upd (upd σ x .no) y .yes) else none
  | .mk x i none =>
    if Γ x = .enum ∧ σ x = .no ∧ x < N ∧ i < D.length ∧ hasPay D i = false
    then some (upd σ x .yes) else none
  | .mk x i (some y) =>
    if Γ x = .enum ∧ Γ y = .box ∧ x ≠ y ∧ σ x = .no ∧ σ y = .yes ∧ x < N ∧
       i < D.length ∧ hasPay D i = true
    then some (upd (upd σ y .no) x .yes) else none

def checkList (σ : SEnv) : List Stmt → Option SEnv
  | []      => some σ
  | t :: ts =>
    match checkS Γ D N σ t with
    | some σ' => checkList σ' ts
    | none    => none

/-- 第 `i` 个分支开始时的静态状态。 -/
def armStart (σ : SEnv) (x y : Var) (i : Nat) : SEnv :=
  upd (upd σ x .no) y (if hasPay D i then .yes else .no)

def checkArms (start : Nat → SEnv) : Nat → List (List Stmt) → Option (List SEnv)
  | _, []      => some []
  | i, a :: as =>
    match checkList Γ D N (start i) a, checkArms start (i + 1) as with
    | some σ, some l => some (σ :: l)
    | _, _           => none

/-- 多个分支结束状态的合并：全部一致则保留，否则 `maybe`。 -/
def joinAll : List SEnv → SEnv
  | []      => fun _ => .maybe
  | σ0 :: l => fun x => if (σ0 :: l).all (fun σ => decide (σ x = σ0 x)) then σ0 x else .maybe

def checkItem (σ : SEnv) : Item → Option SEnv
  | .stmt t => checkS Γ D N σ t
  | .mat x y arms =>
    if Γ x = .enum ∧ Γ y = .box ∧ x ≠ y ∧ y < N ∧ σ x = .yes ∧ σ y = .no ∧
       arms.length = D.length
    then (checkArms Γ D N (armStart D σ x y) 0 arms).map joinAll
    else none

def checkItems (σ : SEnv) : List Item → Option SEnv
  | []        => some σ
  | it :: its =>
    match checkItem Γ D N σ it with
    | some σ' => checkItems σ' its
    | none    => none

end

/-! ## 动态语义 -/

structure St where
  env  : Var → Option Loc
  flag : Var → Bool
  live : Loc → Bool
  tag  : Loc → Nat
  pay  : Loc → Option Loc
  next : Loc

def St.empty : St :=
  { env := fun _ => none, flag := fun _ => false, live := fun _ => false,
    tag := fun _ => 0, pay := fun _ => none, next := 0 }

/-- 新位置交给 `x`，标签 `t`，没有载荷（`alloc` 和无载荷构造）。 -/
def newOp (x : Var) (t : Nat) (s : St) : St :=
  { env := upd s.env x (some s.next), flag := upd s.flag x true,
    live := upd s.live s.next true, tag := upd s.tag s.next t,
    pay := upd s.pay s.next none, next := s.next + 1 }

/-- 新位置交给 `x`，标签 `t`，载荷是 `y` 拥有的位置 `p`，`y` 被移走。 -/
def wrapOp (x : Var) (t : Nat) (y : Var) (p : Loc) (s : St) : St :=
  { env := upd s.env x (some s.next), flag := upd (upd s.flag y false) x true,
    live := upd s.live s.next true, tag := upd s.tag s.next t,
    pay := upd s.pay s.next (some p), next := s.next + 1 }

def moveOp (x y : Var) (l : Loc) (s : St) : St :=
  { s with env := upd s.env y (some l), flag := upd (upd s.flag x false) y true }

/-- 按移动拆开 `x` 指向的枚举 `l`（带载荷 `p` 的变体）：外层释放，载荷交给 `y`。
无载荷的变体直接用 `killOp`。 -/
def takeOp (x y : Var) (l p : Loc) (s : St) : St :=
  { s with live := upd s.live l false, flag := upd (upd s.flag x false) y true,
           env := upd s.env y (some p) }

/-- 释放 `x` 指向的位置 `l`。 -/
def killOp (x : Var) (l : Loc) (s : St) : St :=
  { s with live := upd s.live l false, flag := upd s.flag x false }

/-- 只释放位置 `p`（析构时先释放载荷）。 -/
def killLoc (p : Loc) (s : St) : St := { s with live := upd s.live p false }

/-- 读 `x`：拥有的位置必须活着。 -/
def look (s : St) (x : Var) : Option Loc :=
  match s.env x with
  | some l => if s.live l = true then some l else none
  | none   => none

section
variable (Γ : Var → Ty) (D : List Bool) (N : Nat)

def execS (s : St) : Stmt → Option St
  | .alloc x      => some (newOp x 0 s)
  | .free x       => (look s x).map (fun l => killOp x l s)
  | .use x        => (look s x).map (fun _ => s)
  | .move x y     => (look s x).map (fun l => moveOp x y l s)
  | .mk x i none  => some (newOp x i s)
  | .mk x i (some y) => (look s y).map (fun p => wrapOp x i y p s)

def execList (s : St) : List Stmt → Option St
  | []      => some s
  | t :: ts =>
    match execS s t with
    | some s' => execList s' ts
    | none    => none

/-- `match` 按运行时标签选分支；没有对应的分支就卡住。 -/
def execItem (s : St) : Item → Option St
  | .stmt t => execS s t
  | .mat x y arms =>
    match look s x with
    | some l =>
      match arms[s.tag l]? with
      | some a =>
        match s.pay l with
        | some p => execList (takeOp x y l p s) a
        | none   => execList (killOp x l s) a
      | none   => none
    | none => none

def execItems (s : St) : List Item → Option St
  | []        => some s
  | it :: its =>
    match execItem s it with
    | some s' => execItems s' its
    | none    => none

/-- 析构 `x`（drop flag 为真时）：`box` 直接释放；`enum` 按运行时标签决定是否先释放载荷。 -/
def dropOne (x : Var) (s : St) : Option St :=
  if s.flag x = true then
    match look s x with
    | some l =>
      match Γ x with
      | .box  => some (killOp x l s)
      | .enum =>
        if hasPay D (s.tag l) = true then
          match s.pay l with
          | some p => if s.live p = true then some (killOp x l (killLoc p s)) else none
          | none   => none
        else some (killOp x l s)
    | none => none
  else some s

def dropAll (s : St) : Nat → Option St
  | 0     => some s
  | n + 1 =>
    match dropAll s n with
    | some s' => dropOne Γ D n s'
    | none    => none

end

/-! ## 不变式 -/

/-- 变量拥有的位置的形状：`box` 没有载荷；`enum` 的标签合法，载荷有无与标签一致。 -/
def Shape (D : List Bool) : Ty → Nat → Option Loc → Prop
  | .box,  _, po => po = none
  | .enum, t, po => t < D.length ∧ po.isSome = hasPay D t

/-- 动态不变式。每个活着的位置恰好被一个拥有者持有：要么是 drop flag 为真的变量，
要么是某个活着的枚举的载荷；载荷本身没有载荷（深度为 2，没有环）。 -/
structure DInv (Γ : Var → Ty) (D : List Bool) (N : Nat) (s : St) : Prop where
  owned : ∀ x, s.flag x = true →
    ∃ l, s.env x = some l ∧ s.live l = true ∧ Shape D (Γ x) (s.tag l) (s.pay l)
  payok : ∀ l p, s.live l = true → s.pay l = some p → s.live p = true ∧ s.pay p = none
  held : ∀ m, s.live m = true →
    (∃ x, s.flag x = true ∧ s.env x = some m) ∨ (∃ l, s.live l = true ∧ s.pay l = some m)
  vv : ∀ x y m, s.flag x = true → s.flag y = true → s.env x = some m → s.env y = some m → x = y
  vp : ∀ x m l, s.flag x = true → s.env x = some m → s.live l = true → s.pay l = some m → False
  pp : ∀ l l' m, s.live l = true → s.live l' = true → s.pay l = some m → s.pay l' = some m → l = l'
  fresh : ∀ l, s.live l = true → l < s.next
  bound : ∀ x, s.flag x = true → x < N

/-- 静态状态与 drop flag 一致；`maybe` 不作要求。 -/
structure Compat (σ : SEnv) (f : Var → Bool) : Prop where
  yes : ∀ x, σ x = .yes → f x = true
  no  : ∀ x, σ x = .no → f x = false

theorem compat_empty : Compat (fun _ => .no) St.empty.flag :=
  { yes := by intro x h; cases h
    no := by intro x _; rfl }

theorem dinv_empty (Γ : Var → Ty) (D : List Bool) (N : Nat) : DInv Γ D N St.empty :=
  { owned := by intro x h; simp [St.empty] at h
    payok := by intro l p h; simp [St.empty] at h
    held := by intro m h; simp [St.empty] at h
    vv := by intro x y m h; simp [St.empty] at h
    vp := by intro x m l h; simp [St.empty] at h
    pp := by intro l l' m h; simp [St.empty] at h
    fresh := by intro l h; simp [St.empty] at h
    bound := by intro x h; simp [St.empty] at h }

theorem compat_upd {σ : SEnv} {f : Var → Bool} {x : Var} {o : Own} {b : Bool}
    (h : Compat σ f) (h1 : o = .yes → b = true) (h2 : o = .no → b = false) :
    Compat (upd σ x o) (upd f x b) := by
  constructor
  · intro z hz
    by_cases hzx : z = x
    · subst hzx; simp at hz ⊢; exact h1 hz
    · simp [hzx] at hz ⊢; exact h.yes z hz
  · intro z hz
    by_cases hzx : z = x
    · subst hzx; simp at hz ⊢; exact h2 hz
    · simp [hzx] at hz ⊢; exact h.no z hz

/-- 合并结果比列表里每个状态都“弱”。 -/
theorem compat_joinAll {L : List SEnv} {σ : SEnv} {f : Var → Bool}
    (hm : σ ∈ L) (h : Compat σ f) : Compat (joinAll L) f := by
  cases L with
  | nil => cases hm
  | cons σ0 l =>
    have key : ∀ x, joinAll (σ0 :: l) x ≠ .maybe → joinAll (σ0 :: l) x = σ x := by
      intro x hx
      simp only [joinAll] at hx ⊢
      split
      · rename_i hall
        rw [List.all_eq_true] at hall
        have := hall σ hm
        simp at this
        exact this.symm
      · rename_i hn; simp [hn] at hx
    constructor
    · intro x hx
      have := key x (by rw [hx]; intro h; cases h)
      rw [hx] at this
      exact h.yes x this.symm
    · intro x hx
      have := key x (by rw [hx]; intro h; cases h)
      rw [hx] at this
      exact h.no x this.symm

/-! ## 各个动态操作保持 `DInv` -/

section
variable {Γ : Var → Ty} {D : List Bool} {N : Nat} {s : St}

theorem live_ne_next (hd : DInv Γ D N s) : ∀ l, s.live l = true → l ≠ s.next := by
  intro l h e
  have := hd.fresh l h
  rw [e] at this
  exact Nat.lt_irrefl _ this

theorem dinv_new {x : Var} {t : Nat} (hd : DInv Γ D N s) (hfx : s.flag x = false) (hxN : x < N)
    (hsh : Shape D (Γ x) t none) : DInv Γ D N (newOp x t s) := by
  have hne := live_ne_next hd
  constructor
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      refine ⟨s.next, by simp [newOp], by simp [newOp], ?_⟩
      simpa [newOp] using hsh
    · simp [newOp, upd, hzx] at hz
      obtain ⟨l, hl, hlive, hsh'⟩ := hd.owned z hz
      have hln := hne l hlive
      refine ⟨l, by simp [newOp, upd, hzx, hl], by simp [newOp, upd, hln, hlive], ?_⟩
      simpa [newOp, upd, hln] using hsh'
  · intro l p hl hp
    by_cases hln : l = s.next
    · subst hln; simp [newOp] at hp
    · simp [newOp, upd, hln] at hl hp
      obtain ⟨h1, h2⟩ := hd.payok l p hl hp
      have hpn := hne p h1
      exact ⟨by simp [newOp, upd, hpn, h1], by simp [newOp, upd, hpn, h2]⟩
  · intro m hm
    by_cases hmn : m = s.next
    · left; exact ⟨x, by simp [newOp], by simp [newOp, hmn]⟩
    · simp [newOp, upd, hmn] at hm
      rcases hd.held m hm with ⟨z, hz, hez⟩ | ⟨l, hl, hpl⟩
      · have hzx : z ≠ x := by intro h; rw [h, hfx] at hz; contradiction
        left; exact ⟨z, by simp [newOp, upd, hzx, hz], by simp [newOp, upd, hzx, hez]⟩
      · have hln := hne l hl
        right; exact ⟨l, by simp [newOp, upd, hln, hl], by simp [newOp, upd, hln, hpl]⟩
  · intro a b m ha hb hea heb
    by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · exfalso
      simp [newOp, upd, hax] at hea
      simp [newOp, upd, hbx] at hb heb
      subst hea
      obtain ⟨l, hl, hlive, _⟩ := hd.owned b hb
      rw [hl] at heb
      simp at heb
      exact hne l hlive heb
    · exfalso
      simp [newOp, upd, hbx] at heb
      simp [newOp, upd, hax] at ha hea
      subst heb
      obtain ⟨l, hl, hlive, _⟩ := hd.owned a ha
      rw [hl] at hea
      simp at hea
      exact hne l hlive hea
    · simp [newOp, upd, hax] at ha hea
      simp [newOp, upd, hbx] at hb heb
      exact hd.vv a b m ha hb hea heb
  · intro a m l ha hea hl hpl
    by_cases hln : l = s.next
    · subst hln; simp [newOp] at hpl
    · simp [newOp, upd, hln] at hl hpl
      by_cases hax : a = x
      · simp [newOp, upd, hax] at hea
        subst hea
        exact hne _ (hd.payok l _ hl hpl).1 rfl
      · simp [newOp, upd, hax] at ha hea
        exact hd.vp a m l ha hea hl hpl
  · intro l l' m hl hl' hp hp'
    by_cases hln : l = s.next
    · subst hln; simp [newOp] at hp
    · by_cases hln' : l' = s.next
      · subst hln'; simp [newOp] at hp'
      · simp [newOp, upd, hln] at hl hp
        simp [newOp, upd, hln'] at hl' hp'
        exact hd.pp l l' m hl hl' hp hp'
  · intro l hl
    show l < s.next + 1
    by_cases hln : l = s.next
    · rw [hln]; exact Nat.lt_succ_self _
    · simp [newOp, upd, hln] at hl
      exact Nat.lt_succ_of_lt (hd.fresh l hl)
  · intro z hz
    by_cases hzx : z = x
    · rw [hzx]; exact hxN
    · simp [newOp, upd, hzx] at hz
      exact hd.bound z hz

theorem dinv_wrap {x y : Var} {t : Nat} {p : Loc} (hd : DInv Γ D N s) (hxy : x ≠ y)
    (hfx : s.flag x = false) (hxN : x < N) (hfy : s.flag y = true) (hy : s.env y = some p)
    (hp : s.live p = true) (hΓy : Γ y = .box) (hsh : Shape D (Γ x) t (some p)) :
    DInv Γ D N (wrapOp x t y p s) := by
  have hne := live_ne_next hd
  have hpn := hne p hp
  have hpp : s.pay p = none := by
    obtain ⟨l, hl, _, hs⟩ := hd.owned y hfy
    rw [hy] at hl
    cases hl
    rw [hΓy] at hs
    exact hs
  have own : ∀ z, z ≠ x → (wrapOp x t y p s).flag z = true → z ≠ y ∧ s.flag z = true := by
    intro z hzx hz
    by_cases hzy : z = y
    · subst hzy; simp [wrapOp, upd, Ne.symm hxy] at hz
    · simp [wrapOp, upd, hzx, hzy] at hz
      exact ⟨hzy, hz⟩
  constructor
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      refine ⟨s.next, by simp [wrapOp], by simp [wrapOp], ?_⟩
      simpa [wrapOp] using hsh
    · obtain ⟨_, hz'⟩ := own z hzx hz
      obtain ⟨l, hl, hlive, hsh'⟩ := hd.owned z hz'
      have hln := hne l hlive
      refine ⟨l, by simp [wrapOp, upd, hzx, hl], by simp [wrapOp, upd, hln, hlive], ?_⟩
      simpa [wrapOp, upd, hln] using hsh'
  · intro l q hl hq
    by_cases hln : l = s.next
    · subst hln
      simp [wrapOp] at hq
      subst hq
      exact ⟨by simp [wrapOp, upd, hpn, hp], by simp [wrapOp, upd, hpn, hpp]⟩
    · simp [wrapOp, upd, hln] at hl hq
      obtain ⟨h1, h2⟩ := hd.payok l q hl hq
      have hqn := hne q h1
      exact ⟨by simp [wrapOp, upd, hqn, h1], by simp [wrapOp, upd, hqn, h2]⟩
  · intro m hm
    by_cases hmn : m = s.next
    · left; exact ⟨x, by simp [wrapOp], by simp [wrapOp, hmn]⟩
    · simp [wrapOp, upd, hmn] at hm
      rcases hd.held m hm with ⟨z, hz, hez⟩ | ⟨l, hl, hpl⟩
      · by_cases hzy : z = y
        · subst hzy
          rw [hy] at hez
          cases hez
          right; exact ⟨s.next, by simp [wrapOp], by simp [wrapOp]⟩
        · have hzx : z ≠ x := by intro h; rw [h, hfx] at hz; contradiction
          left; exact ⟨z, by simp [wrapOp, upd, hzx, hzy, hz], by simp [wrapOp, upd, hzx, hez]⟩
      · have hln := hne l hl
        right; exact ⟨l, by simp [wrapOp, upd, hln, hl], by simp [wrapOp, upd, hln, hpl]⟩
  · intro a b m ha hb hea heb
    by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · exfalso
      obtain ⟨_, hb'⟩ := own b hbx hb
      simp [wrapOp, upd, hax] at hea
      simp [wrapOp, upd, hbx] at heb
      subst hea
      obtain ⟨l, hl, hlive, _⟩ := hd.owned b hb'
      rw [hl] at heb
      simp at heb
      exact hne l hlive heb
    · exfalso
      obtain ⟨_, ha'⟩ := own a hax ha
      simp [wrapOp, upd, hbx] at heb
      simp [wrapOp, upd, hax] at hea
      subst heb
      obtain ⟨l, hl, hlive, _⟩ := hd.owned a ha'
      rw [hl] at hea
      simp at hea
      exact hne l hlive hea
    · obtain ⟨_, ha'⟩ := own a hax ha
      obtain ⟨_, hb'⟩ := own b hbx hb
      simp [wrapOp, upd, hax] at hea
      simp [wrapOp, upd, hbx] at heb
      exact hd.vv a b m ha' hb' hea heb
  · intro a m l ha hea hl hpl
    by_cases hln : l = s.next
    · subst hln
      simp [wrapOp] at hpl
      subst hpl
      by_cases hax : a = x
      · simp [wrapOp, upd, hax] at hea
        exact hpn hea.symm
      · obtain ⟨hay, ha'⟩ := own a hax ha
        simp [wrapOp, upd, hax] at hea
        exact hay (hd.vv a y _ ha' hfy hea hy)
    · simp [wrapOp, upd, hln] at hl hpl
      by_cases hax : a = x
      · simp [wrapOp, upd, hax] at hea
        subst hea
        exact hne _ (hd.payok l _ hl hpl).1 rfl
      · obtain ⟨_, ha'⟩ := own a hax ha
        simp [wrapOp, upd, hax] at hea
        exact hd.vp a m l ha' hea hl hpl
  · intro l l' m hl hl' hq hq'
    by_cases hln : l = s.next <;> by_cases hln' : l' = s.next
    · rw [hln, hln']
    · exfalso
      rw [hln] at hq
      simp [wrapOp] at hq
      subst hq
      simp [wrapOp, upd, hln'] at hl' hq'
      exact hd.vp y _ l' hfy hy hl' hq'
    · exfalso
      rw [hln'] at hq'
      simp [wrapOp] at hq'
      subst hq'
      simp [wrapOp, upd, hln] at hl hq
      exact hd.vp y _ l hfy hy hl hq
    · simp [wrapOp, upd, hln] at hl hq
      simp [wrapOp, upd, hln'] at hl' hq'
      exact hd.pp l l' m hl hl' hq hq'
  · intro l hl
    show l < s.next + 1
    by_cases hln : l = s.next
    · rw [hln]; exact Nat.lt_succ_self _
    · simp [wrapOp, upd, hln] at hl
      exact Nat.lt_succ_of_lt (hd.fresh l hl)
  · intro z hz
    by_cases hzx : z = x
    · rw [hzx]; exact hxN
    · exact hd.bound z (own z hzx hz).2

theorem dinv_move {x y : Var} {l : Loc} (hd : DInv Γ D N s) (hxy : x ≠ y)
    (hfx : s.flag x = true) (hfy : s.flag y = false) (hyN : y < N)
    (hl : s.env x = some l) (hΓ : Γ x = Γ y) : DInv Γ D N (moveOp x y l s) := by
  have own : ∀ z, z ≠ y → (moveOp x y l s).flag z = true → z ≠ x ∧ s.flag z = true := by
    intro z hzy hz
    by_cases hzx : z = x
    · subst hzx; simp [moveOp, upd, hxy] at hz
    · simp [moveOp, upd, hzy, hzx] at hz
      exact ⟨hzx, hz⟩
  constructor
  · intro z hz
    by_cases hzy : z = y
    · subst hzy
      obtain ⟨m, hm, hlive, hsh⟩ := hd.owned x hfx
      rw [hl] at hm
      cases hm
      rw [hΓ] at hsh
      exact ⟨l, by simp [moveOp], hlive, hsh⟩
    · obtain ⟨_, hz'⟩ := own z hzy hz
      obtain ⟨m, hm, hlive, hsh⟩ := hd.owned z hz'
      exact ⟨m, by simp [moveOp, upd, hzy, hm], hlive, hsh⟩
  · intro m p h1 h2
    exact hd.payok m p h1 h2
  · intro m hm
    rcases hd.held m hm with ⟨z, hz, hez⟩ | ⟨l', hl', hpl⟩
    · by_cases hzx : z = x
      · subst hzx
        rw [hl] at hez
        cases hez
        left; exact ⟨y, by simp [moveOp], by simp [moveOp]⟩
      · have hzy : z ≠ y := by intro h; rw [h, hfy] at hz; contradiction
        left; exact ⟨z, by simp [moveOp, upd, hzx, hzy, hz], by simp [moveOp, upd, hzy, hez]⟩
    · right; exact ⟨l', hl', hpl⟩
  · intro a b m ha hb hea heb
    by_cases hay : a = y <;> by_cases hby : b = y
    · rw [hay, hby]
    · exfalso
      obtain ⟨hbx, hb'⟩ := own b hby hb
      simp [moveOp, upd, hay] at hea
      simp [moveOp, upd, hby] at heb
      rw [← hea] at heb
      exact hbx (hd.vv x b l hfx hb' hl heb).symm
    · exfalso
      obtain ⟨hax, ha'⟩ := own a hay ha
      simp [moveOp, upd, hay] at hea
      simp [moveOp, upd, hby] at heb
      rw [← heb] at hea
      exact hax (hd.vv x a l hfx ha' hl hea).symm
    · obtain ⟨_, ha'⟩ := own a hay ha
      obtain ⟨_, hb'⟩ := own b hby hb
      simp [moveOp, upd, hay] at hea
      simp [moveOp, upd, hby] at heb
      exact hd.vv a b m ha' hb' hea heb
  · intro a m l' ha hea hl' hpl
    by_cases hay : a = y
    · simp [moveOp, upd, hay] at hea
      subst hea
      exact hd.vp x l l' hfx hl hl' hpl
    · obtain ⟨_, ha'⟩ := own a hay ha
      simp [moveOp, upd, hay] at hea
      exact hd.vp a m l' ha' hea hl' hpl
  · intro m m' p h1 h2 h3 h4
    exact hd.pp m m' p h1 h2 h3 h4
  · intro m h
    exact hd.fresh m h
  · intro z hz
    by_cases hzy : z = y
    · rw [hzy]; exact hyN
    · exact hd.bound z (own z hzy hz).2

/-- 释放没有载荷的位置（`box`，或无载荷变体的枚举）。 -/
theorem dinv_kill {x : Var} {l : Loc} (hd : DInv Γ D N s) (hfx : s.flag x = true)
    (hl : s.env x = some l) (hpl : s.pay l = none) : DInv Γ D N (killOp x l s) := by
  have own : ∀ z, (killOp x l s).flag z = true → z ≠ x ∧ s.flag z = true := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx; simp [killOp] at hz
    · simp [killOp, upd, hzx] at hz
      exact ⟨hzx, hz⟩
  have alive : ∀ m, (killOp x l s).live m = true → m ≠ l ∧ s.live m = true := by
    intro m hm
    by_cases hml : m = l
    · subst hml; simp [killOp] at hm
    · simp [killOp, upd, hml] at hm
      exact ⟨hml, hm⟩
  constructor
  · intro z hz
    obtain ⟨hzx, hz'⟩ := own z hz
    obtain ⟨m, hm, hlive, hsh⟩ := hd.owned z hz'
    have hml : m ≠ l := by
      intro h; rw [h] at hm; exact hzx (hd.vv z x l hz' hfx hm hl)
    exact ⟨m, hm, by simp [killOp, upd, hml, hlive], hsh⟩
  · intro m p hm hp
    obtain ⟨_, hm'⟩ := alive m hm
    obtain ⟨h1, h2⟩ := hd.payok m p hm' hp
    have hpl' : p ≠ l := by
      intro h; rw [h] at hp; exact hd.vp x l m hfx hl hm' hp
    exact ⟨by simp [killOp, upd, hpl', h1], h2⟩
  · intro m hm
    obtain ⟨hml, hm'⟩ := alive m hm
    rcases hd.held m hm' with ⟨z, hz, hez⟩ | ⟨l', hl', hpl'⟩
    · have hzx : z ≠ x := by
        intro h; rw [h, hl] at hez; simp at hez; exact hml hez.symm
      left; exact ⟨z, by simp [killOp, upd, hzx, hz], hez⟩
    · have hll : l' ≠ l := by
        intro h; rw [h, hpl] at hpl'; simp at hpl'
      right; exact ⟨l', by simp [killOp, upd, hll, hl'], hpl'⟩
  · intro a b m ha hb hea heb
    exact hd.vv a b m (own a ha).2 (own b hb).2 hea heb
  · intro a m l' ha hea hl' hpl'
    exact hd.vp a m l' (own a ha).2 hea (alive l' hl').2 hpl'
  · intro m m' p h1 h2 h3 h4
    exact hd.pp m m' p (alive m h1).2 (alive m' h2).2 h3 h4
  · intro m h
    exact hd.fresh m (alive m h).2
  · intro z hz
    exact hd.bound z (own z hz).2

/-- 析构带载荷的枚举：先释放载荷 `p`，再释放外层 `l`。 -/
theorem dinv_kill2 {x : Var} {l p : Loc} (hd : DInv Γ D N s) (hfx : s.flag x = true)
    (hl : s.env x = some l) (hlive : s.live l = true) (hpl : s.pay l = some p) :
    DInv Γ D N (killOp x l (killLoc p s)) := by
  obtain ⟨_, hpp⟩ := hd.payok l p hlive hpl
  have own : ∀ z, (killOp x l (killLoc p s)).flag z = true → z ≠ x ∧ s.flag z = true := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx; simp [killOp] at hz
    · simp [killOp, killLoc, upd, hzx] at hz
      exact ⟨hzx, hz⟩
  have alive : ∀ m, (killOp x l (killLoc p s)).live m = true →
      m ≠ l ∧ m ≠ p ∧ s.live m = true := by
    intro m hm
    by_cases hml : m = l
    · subst hml; simp [killOp] at hm
    · by_cases hmp : m = p
      · subst hmp; simp [killOp, killLoc, upd, hml] at hm
      · simp [killOp, killLoc, upd, hml, hmp] at hm
        exact ⟨hml, hmp, hm⟩
  have back : ∀ m, m ≠ l → m ≠ p → s.live m = true → (killOp x l (killLoc p s)).live m = true := by
    intro m h1 h2 h3
    simp [killOp, killLoc, upd, h1, h2, h3]
  constructor
  · intro z hz
    obtain ⟨hzx, hz'⟩ := own z hz
    obtain ⟨m, hm, hmlive, hsh⟩ := hd.owned z hz'
    have hml : m ≠ l := by
      intro h; rw [h] at hm; exact hzx (hd.vv z x l hz' hfx hm hl)
    have hmp : m ≠ p := by
      intro h; rw [h] at hm; exact hd.vp z p l hz' hm hlive hpl
    exact ⟨m, hm, back m hml hmp hmlive, hsh⟩
  · intro m q hm hq
    obtain ⟨hml, _, hm'⟩ := alive m hm
    obtain ⟨h1, h2⟩ := hd.payok m q hm' hq
    have hql : q ≠ l := by
      intro h; rw [h] at hq; exact hd.vp x l m hfx hl hm' hq
    have hqp : q ≠ p := by
      intro h; rw [h] at hq; exact hml (hd.pp m l p hm' hlive hq hpl)
    exact ⟨back q hql hqp h1, h2⟩
  · intro m hm
    obtain ⟨hml, hmp, hm'⟩ := alive m hm
    rcases hd.held m hm' with ⟨z, hz, hez⟩ | ⟨l', hl', hpl'⟩
    · have hzx : z ≠ x := by
        intro h; rw [h, hl] at hez; simp at hez; exact hml hez.symm
      left; exact ⟨z, by simp [killOp, killLoc, upd, hzx, hz], hez⟩
    · have hll : l' ≠ l := by
        intro h; rw [h, hpl] at hpl'; simp at hpl'; exact hmp hpl'.symm
      have hlp : l' ≠ p := by
        intro h; rw [h, hpp] at hpl'; simp at hpl'
      right; exact ⟨l', back l' hll hlp hl', hpl'⟩
  · intro a b m ha hb hea heb
    exact hd.vv a b m (own a ha).2 (own b hb).2 hea heb
  · intro a m l' ha hea hl' hpl'
    exact hd.vp a m l' (own a ha).2 hea (alive l' hl').2.2 hpl'
  · intro m m' q h1 h2 h3 h4
    exact hd.pp m m' q (alive m h1).2.2 (alive m' h2).2.2 h3 h4
  · intro m h
    exact hd.fresh m (alive m h).2.2
  · intro z hz
    exact hd.bound z (own z hz).2

/-- 按移动匹配带载荷的变体：外层释放，载荷交给 `y`。 -/
theorem dinv_take {x y : Var} {l p : Loc} (hd : DInv Γ D N s) (hxy : x ≠ y)
    (hfx : s.flag x = true) (hl : s.env x = some l) (hlive : s.live l = true)
    (hpl : s.pay l = some p) (hfy : s.flag y = false) (hyN : y < N) (hΓy : Γ y = .box) :
    DInv Γ D N (takeOp x y l p s) := by
  obtain ⟨hp, hpp⟩ := hd.payok l p hlive hpl
  have hpl_ne : p ≠ l := by intro h; rw [h, hpl] at hpp; simp at hpp
  have own : ∀ z, z ≠ y → (takeOp x y l p s).flag z = true → z ≠ x ∧ s.flag z = true := by
    intro z hzy hz
    by_cases hzx : z = x
    · subst hzx; simp [takeOp, upd, hxy] at hz
    · simp [takeOp, upd, hzy, hzx] at hz
      exact ⟨hzx, hz⟩
  have alive : ∀ m, (takeOp x y l p s).live m = true → m ≠ l ∧ s.live m = true := by
    intro m hm
    by_cases hml : m = l
    · subst hml; simp [takeOp] at hm
    · simp [takeOp, upd, hml] at hm
      exact ⟨hml, hm⟩
  constructor
  · intro z hz
    by_cases hzy : z = y
    · subst hzy
      refine ⟨p, by simp [takeOp], by simp [takeOp, upd, hpl_ne, hp], ?_⟩
      rw [hΓy]
      exact hpp
    · obtain ⟨hzx, hz'⟩ := own z hzy hz
      obtain ⟨m, hm, hmlive, hsh⟩ := hd.owned z hz'
      have hml : m ≠ l := by
        intro h; rw [h] at hm; exact hzx (hd.vv z x l hz' hfx hm hl)
      exact ⟨m, by simp [takeOp, upd, hzy, hm], by simp [takeOp, upd, hml, hmlive], hsh⟩
  · intro m q hm hq
    obtain ⟨hml, hm'⟩ := alive m hm
    obtain ⟨h1, h2⟩ := hd.payok m q hm' hq
    have hql : q ≠ l := by
      intro h; rw [h] at hq; exact hd.vp x l m hfx hl hm' hq
    exact ⟨by simp [takeOp, upd, hql, h1], h2⟩
  · intro m hm
    obtain ⟨hml, hm'⟩ := alive m hm
    rcases hd.held m hm' with ⟨z, hz, hez⟩ | ⟨l', hl', hpl'⟩
    · have hzx : z ≠ x := by
        intro h; rw [h, hl] at hez; simp at hez; exact hml hez.symm
      have hzy : z ≠ y := by intro h; rw [h, hfy] at hz; contradiction
      left; exact ⟨z, by simp [takeOp, upd, hzx, hzy, hz], by simp [takeOp, upd, hzy, hez]⟩
    · by_cases hll : l' = l
      · rw [hll, hpl] at hpl'
        cases hpl'
        left; exact ⟨y, by simp [takeOp], by simp [takeOp]⟩
      · right; exact ⟨l', by simp [takeOp, upd, hll, hl'], hpl'⟩
  · intro a b m ha hb hea heb
    by_cases hay : a = y <;> by_cases hby : b = y
    · rw [hay, hby]
    · exfalso
      obtain ⟨_, hb'⟩ := own b hby hb
      simp [takeOp, upd, hay] at hea
      simp [takeOp, upd, hby] at heb
      subst hea
      exact hd.vp b _ l hb' heb hlive hpl
    · exfalso
      obtain ⟨_, ha'⟩ := own a hay ha
      simp [takeOp, upd, hby] at heb
      simp [takeOp, upd, hay] at hea
      subst heb
      exact hd.vp a _ l ha' hea hlive hpl
    · obtain ⟨_, ha'⟩ := own a hay ha
      obtain ⟨_, hb'⟩ := own b hby hb
      simp [takeOp, upd, hay] at hea
      simp [takeOp, upd, hby] at heb
      exact hd.vv a b m ha' hb' hea heb
  · intro a m l' ha hea hl' hpl'
    obtain ⟨hll, hl''⟩ := alive l' hl'
    by_cases hay : a = y
    · simp [takeOp, upd, hay] at hea
      subst hea
      exact hll (hd.pp l' l _ hl'' hlive hpl' hpl)
    · obtain ⟨_, ha'⟩ := own a hay ha
      simp [takeOp, upd, hay] at hea
      exact hd.vp a m l' ha' hea hl'' hpl'
  · intro m m' q h1 h2 h3 h4
    exact hd.pp m m' q (alive m h1).2 (alive m' h2).2 h3 h4
  · intro m h
    exact hd.fresh m (alive m h).2
  · intro z hz
    by_cases hzy : z = y
    · rw [hzy]; exact hyN
    · exact hd.bound z (own z hzy hz).2

end

/-! ## 语句、语句列表、`match` -/

section
variable {Γ : Var → Ty} {D : List Bool} {N : Nat}

theorem stepS {σ σ' : SEnv} {s : St} {t : Stmt}
    (hc : checkS Γ D N σ t = some σ') (hc0 : Compat σ s.flag) (hd : DInv Γ D N s) :
    ∃ s', execS s t = some s' ∧ Compat σ' s'.flag ∧ DInv Γ D N s' := by
  cases t with
  | alloc x =>
    simp only [checkS] at hc
    split at hc
    · rename_i h
      obtain ⟨hΓ, hx, hxN⟩ := h
      cases hc
      refine ⟨newOp x 0 s, rfl, ?_, dinv_new hd (hc0.no x hx) hxN ?_⟩
      · exact compat_upd hc0 (fun _ => rfl) (fun h => by cases h)
      · simp [hΓ, Shape]
    · contradiction
  | free x =>
    simp only [checkS] at hc
    split at hc
    · rename_i h
      obtain ⟨hΓ, hx⟩ := h
      cases hc
      have hfx := hc0.yes x hx
      obtain ⟨l, hl, hlive, hsh⟩ := hd.owned x hfx
      rw [hΓ] at hsh
      refine ⟨killOp x l s, by simp [execS, look, hl, hlive], ?_, dinv_kill hd hfx hl hsh⟩
      exact compat_upd hc0 (fun h => by cases h) (fun _ => rfl)
    · contradiction
  | use x =>
    simp only [checkS] at hc
    split at hc
    · rename_i hx
      cases hc
      obtain ⟨l, hl, hlive, _⟩ := hd.owned x (hc0.yes x hx)
      exact ⟨s, by simp [execS, look, hl, hlive], hc0, hd⟩
    · contradiction
  | move x y =>
    simp only [checkS] at hc
    split at hc
    · rename_i h
      obtain ⟨hxy, hΓ, hx, hy, hyN⟩ := h
      cases hc
      have hfx := hc0.yes x hx
      obtain ⟨l, hl, hlive, _⟩ := hd.owned x hfx
      refine ⟨moveOp x y l s, by simp [execS, look, hl, hlive], ?_,
        dinv_move hd hxy hfx (hc0.no y hy) hyN hl hΓ⟩
      exact compat_upd (compat_upd hc0 (fun h => by cases h) (fun _ => rfl))
        (fun _ => rfl) (fun h => by cases h)
    · contradiction
  | mk x i o =>
    cases o with
    | none =>
      simp only [checkS] at hc
      split at hc
      · rename_i h
        obtain ⟨hΓ, hx, hxN, hi, hpay⟩ := h
        cases hc
        refine ⟨newOp x i s, rfl, ?_, dinv_new hd (hc0.no x hx) hxN ?_⟩
        · exact compat_upd hc0 (fun _ => rfl) (fun h => by cases h)
        · simp [hΓ, Shape, hi, hpay]
      · contradiction
    | some y =>
      simp only [checkS] at hc
      split at hc
      · rename_i h
        obtain ⟨hΓx, hΓy, hxy, hx, hy, hxN, hi, hpay⟩ := h
        cases hc
        have hfy := hc0.yes y hy
        obtain ⟨p, hp, hplive, _⟩ := hd.owned y hfy
        refine ⟨wrapOp x i y p s, by simp [execS, look, hp, hplive], ?_,
          dinv_wrap hd hxy (hc0.no x hx) hxN hfy hp hplive hΓy ?_⟩
        · exact compat_upd (compat_upd hc0 (fun h => by cases h) (fun _ => rfl))
            (fun _ => rfl) (fun h => by cases h)
        · simp [hΓx, Shape, hi, hpay]
      · contradiction

theorem listSound (ts : List Stmt) :
    ∀ {σ σ' : SEnv} {s : St}, checkList Γ D N σ ts = some σ' → Compat σ s.flag → DInv Γ D N s →
      ∃ s', execList s ts = some s' ∧ Compat σ' s'.flag ∧ DInv Γ D N s' := by
  induction ts with
  | nil =>
    intro σ σ' s hc hc0 hd
    simp [checkList] at hc
    subst hc
    exact ⟨s, by simp [execList], hc0, hd⟩
  | cons t ts ih =>
    intro σ σ' s hc hc0 hd
    simp only [checkList] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hc₁, hd₁⟩ := stepS h₁ hc0 hd
      obtain ⟨s₂, he₂, hc₂, hd₂⟩ := ih hc hc₁ hd₁
      exact ⟨s₂, by simp [execList, he₁, he₂], hc₂, hd₂⟩
    · contradiction

/-- 检查通过的每个分支都有一个结束状态，并且在合并的列表里。 -/
theorem arms_get (start : Nat → SEnv) (arms : List (List Stmt)) :
    ∀ (i : Nat) {L : List SEnv}, checkArms Γ D N start i arms = some L →
      ∀ j a, arms[j]? = some a → ∃ σj, checkList Γ D N (start (i + j)) a = some σj ∧ σj ∈ L := by
  induction arms with
  | nil => intro i L _ j a ha; simp at ha
  | cons a0 as ih =>
    intro i L hc j a ha
    simp only [checkArms] at hc
    split at hc
    · rename_i σ0 l h0 hl
      cases hc
      cases j with
      | zero =>
        simp at ha
        subst ha
        exact ⟨σ0, by simpa using h0, by simp⟩
      | succ j =>
        simp at ha
        obtain ⟨σj, hj, hm⟩ := ih (i + 1) hl j a ha
        have e : i + 1 + j = i + (j + 1) := by omega
        rw [e] at hj
        exact ⟨σj, hj, by simp [hm]⟩
    · contradiction

theorem compat_arm_none {σ : SEnv} {f : Var → Bool} {x y : Var} (h : Compat σ f)
    (hxy : x ≠ y) (hfy : f y = false) :
    Compat (upd (upd σ x .no) y .no) (upd f x false) := by
  have e : upd (upd f x false) y false = upd f x false := by
    funext z
    by_cases hzy : z = y
    · rw [hzy]; simp [upd, Ne.symm hxy, hfy]
    · simp [upd, hzy]
  rw [← e]
  exact compat_upd (compat_upd h (fun h => by cases h) (fun _ => rfl))
    (fun h => by cases h) (fun _ => rfl)

theorem itemSound {σ σ' : SEnv} {s : St} {it : Item}
    (hc : checkItem Γ D N σ it = some σ') (hc0 : Compat σ s.flag) (hd : DInv Γ D N s) :
    ∃ s', execItem s it = some s' ∧ Compat σ' s'.flag ∧ DInv Γ D N s' := by
  cases it with
  | stmt t =>
    simp only [checkItem] at hc
    obtain ⟨s', h1, h2, h3⟩ := stepS hc hc0 hd
    exact ⟨s', by simp [execItem, h1], h2, h3⟩
  | mat x y arms =>
    simp only [checkItem] at hc
    split at hc
    · rename_i h
      obtain ⟨hΓx, hΓy, hxy, hyN, hx, hy, hlen⟩ := h
      cases hL : checkArms Γ D N (armStart D σ x y) 0 arms with
      | none => rw [hL] at hc; simp at hc
      | some L =>
        rw [hL] at hc
        simp at hc
        have hfx := hc0.yes x hx
        have hfy := hc0.no y hy
        obtain ⟨l, hl, hlive, hsh⟩ := hd.owned x hfx
        rw [hΓx] at hsh
        obtain ⟨htl, hps⟩ := hsh
        have htl' : s.tag l < arms.length := by rw [hlen]; exact htl
        have ha : arms[s.tag l]? = some arms[s.tag l] := List.getElem?_eq_getElem htl'
        obtain ⟨σt, hct, hmem⟩ := arms_get (armStart D σ x y) arms 0 hL (s.tag l) _ ha
        rw [Nat.zero_add] at hct
        cases hp : s.pay l with
        | none =>
          have hh : hasPay D (s.tag l) = false := by simpa [hp] using hps.symm
          have hst : armStart D σ x y (s.tag l) = upd (upd σ x .no) y .no := by
            simp [armStart, hh]
          rw [hst] at hct
          obtain ⟨s', he, hc', hd'⟩ :=
            listSound _ hct (compat_arm_none hc0 hxy hfy) (dinv_kill hd hfx hl hp)
          refine ⟨s', by simp [execItem, look, hl, hlive, ha, hp, he], ?_, hd'⟩
          rw [← hc]
          exact compat_joinAll hmem hc'
        | some p =>
          have hh : hasPay D (s.tag l) = true := by simpa [hp] using hps.symm
          have hst : armStart D σ x y (s.tag l) = upd (upd σ x .no) y .yes := by
            simp [armStart, hh]
          rw [hst] at hct
          have hcomp : Compat (upd (upd σ x .no) y .yes) (takeOp x y l p s).flag :=
            compat_upd (compat_upd hc0 (fun h => by cases h) (fun _ => rfl))
              (fun _ => rfl) (fun h => by cases h)
          obtain ⟨s', he, hc', hd'⟩ :=
            listSound _ hct hcomp (dinv_take hd hxy hfx hl hlive hp hfy hyN hΓy)
          refine ⟨s', by simp [execItem, look, hl, hlive, ha, hp, he], ?_, hd'⟩
          rw [← hc]
          exact compat_joinAll hmem hc'
    · contradiction

theorem itemsSound (its : List Item) :
    ∀ {σ σ' : SEnv} {s : St}, checkItems Γ D N σ its = some σ' →
      Compat σ s.flag → DInv Γ D N s →
      ∃ s', execItems s its = some s' ∧ Compat σ' s'.flag ∧ DInv Γ D N s' := by
  induction its with
  | nil =>
    intro σ σ' s hc hc0 hd
    simp [checkItems] at hc
    subst hc
    exact ⟨s, by simp [execItems], hc0, hd⟩
  | cons it its ih =>
    intro σ σ' s hc hc0 hd
    simp only [checkItems] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hc₁, hd₁⟩ := itemSound h₁ hc0 hd
      obtain ⟨s₂, he₂, hc₂, hd₂⟩ := ih hc hc₁ hd₁
      exact ⟨s₂, by simp [execItems, he₁, he₂], hc₂, hd₂⟩
    · contradiction

/-! ## 作用域结束：按 drop flag 和运行时标签析构 -/

theorem dropOne_sound {s : St} (x : Var) (hd : DInv Γ D N s) :
    ∃ s', dropOne Γ D x s = some s' ∧ DInv Γ D N s' ∧ s'.flag x = false ∧
      ∀ y, y ≠ x → s'.flag y = s.flag y := by
  by_cases hf : s.flag x = true
  · obtain ⟨l, hl, hlive, hsh⟩ := hd.owned x hf
    have hlk : look s x = some l := by simp [look, hl, hlive]
    cases hΓ : Γ x with
    | box =>
      rw [hΓ] at hsh
      refine ⟨killOp x l s, by simp [dropOne, hf, hlk, hΓ], dinv_kill hd hf hl hsh,
        by simp [killOp], ?_⟩
      intro y hy
      simp [killOp, upd, hy]
    | enum =>
      rw [hΓ] at hsh
      obtain ⟨_, hps⟩ := hsh
      cases hp : s.pay l with
      | none =>
        have hh : hasPay D (s.tag l) = false := by simpa [hp] using hps.symm
        refine ⟨killOp x l s, by simp [dropOne, hf, hlk, hΓ, hh], dinv_kill hd hf hl hp,
          by simp [killOp], ?_⟩
        intro y hy
        simp [killOp, upd, hy]
      | some p =>
        have hh : hasPay D (s.tag l) = true := by simpa [hp] using hps.symm
        have hpl := (hd.payok l p hlive hp).1
        refine ⟨killOp x l (killLoc p s), by simp [dropOne, hf, hlk, hΓ, hh, hp, hpl],
          dinv_kill2 hd hf hl hlive hp, by simp [killOp], ?_⟩
        intro y hy
        simp [killOp, killLoc, upd, hy]
  · exact ⟨s, by simp [dropOne, hf], hd, by simpa using hf, fun _ _ => rfl⟩

theorem dropAll_sound {s : St} (hd : DInv Γ D N s) :
    ∀ n, ∃ s', dropAll Γ D s n = some s' ∧ DInv Γ D N s' ∧ ∀ y, y < n → s'.flag y = false := by
  intro n
  induction n with
  | zero => exact ⟨s, by simp [dropAll], hd, fun y h => absurd h (Nat.not_lt_zero y)⟩
  | succ n ih =>
    obtain ⟨s₁, he₁, hd₁, hf₁⟩ := ih
    obtain ⟨s₂, he₂, hd₂, hfn, hrest⟩ := dropOne_sound n hd₁
    refine ⟨s₂, by simp only [dropAll, he₁, he₂], hd₂, ?_⟩
    intro y hy
    by_cases hyn : y = n
    · rw [hyn]; exact hfn
    · rw [hrest y hyn]
      exact hf₁ y (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hy) hyn)

end

/-! ## 主定理 -/

/-- **`Datatypes.Enum` 主定理。** 检查器接受的程序（`match` 穷尽、按移动拆开），
执行和作用域结束时按 drop flag、按运行时标签的析构都不会出错，并且结束时堆上没有活着的值。 -/
theorem safety_and_no_leak (Γ : Var → Ty) (D : List Bool) (N : Nat) (its : List Item)
    (σ' : SEnv) (h : checkItems Γ D N (fun _ => .no) its = some σ') :
    ∃ s', (execItems St.empty its).bind (fun s => dropAll Γ D s N) = some s' ∧
      ∀ l, s'.live l = false := by
  obtain ⟨s₁, he₁, _, hd₁⟩ := itemsSound its h compat_empty (dinv_empty Γ D N)
  obtain ⟨s₂, he₂, hd₂, hf₂⟩ := dropAll_sound hd₁ N
  refine ⟨s₂, by rw [he₁]; exact he₂, ?_⟩
  have noflag : ∀ x, s₂.flag x = true → False := by
    intro x hx
    rw [hf₂ x (hd₂.bound x hx)] at hx
    contradiction
  intro l
  cases hl : s₂.live l with
  | false => rfl
  | true =>
    exfalso
    rcases hd₂.held l hl with ⟨x, hx, _⟩ | ⟨l', hl', hpl'⟩
    · exact noflag x hx
    · rcases hd₂.held l' hl' with ⟨x, hx, _⟩ | ⟨l'', hl'', hpl''⟩
      · exact noflag x hx
      · rw [(hd₂.payok l'' l' hl'' hpl'').2] at hpl'
        contradiction

/-! ## 例子

`enum Opt { Some(Box<I64>), None }`：`D = [true, false]`。变量 0 是 `Opt`，1、2 是 `Box`。 -/

def Dx : List Bool := [true, false]
def Γx : Var → Ty := fun x => if x = 0 then .enum else .box

def chk (its : List Item) : Bool := (checkItems Γx Dx 3 (fun _ => .no) its).isSome
def run (its : List Item) : Bool :=
  ((execItems St.empty its).bind (fun s => dropAll Γx Dx s 3)).isSome

/-- `x1 = box; x0 = .Some(x1); match x0 { .Some(x2) => free(x2), .None => {} }` -/
def demo : List Item :=
  [.stmt (.alloc 1), .stmt (.mk 0 0 (some 1)), .mat 0 2 [[.free 2], []]]

example : chk demo = true := rfl
example : run demo = true := rfl

/-- 漏掉 `.None` 分支：拒绝。 -/
example : chk [.stmt (.alloc 1), .stmt (.mk 0 0 (some 1)), .mat 0 2 [[.free 2]]] = false := rfl

/-- 不经检查执行：值是 `.None`，没有对应分支，卡住。穷尽性是安全的必要条件。 -/
example : (execItems St.empty [.stmt (.mk 0 1 none), .mat 0 2 [[.free 2]]]).isNone = true := rfl

/-- 载荷移进枚举之后，`x1` 不能再用。 -/
example : chk [.stmt (.alloc 1), .stmt (.mk 0 0 (some 1)), .stmt (.use 1)] = false := rfl

/-- `match` 之后 `x0` 已被拆开，不能再用。 -/
example : chk (demo ++ [.stmt (.use 0)]) = false := rfl

/-- 一个分支拿到载荷、另一个没有：合并后 `x2` 是 `maybe`，不能用，但作用域结束时按 drop flag 析构。 -/
def demo2 : List Item := [.stmt (.alloc 1), .stmt (.mk 0 0 (some 1)), .mat 0 2 [[], []]]
example : chk demo2 = true := rfl
example : run demo2 = true := rfl
example : chk (demo2 ++ [.stmt (.use 2)]) = false := rfl

/-- 不 `match`，作用域结束时按运行时标签析构：`.Some` 先释放载荷，`.None` 直接释放。 -/
example : run [.stmt (.alloc 1), .stmt (.mk 0 0 (some 1))] = true := rfl
example : run [.stmt (.mk 0 1 none)] = true := rfl

/-- 构造时标签和载荷必须匹配：`.None` 不能带载荷，`.Some` 必须带。 -/
example : chk [.stmt (.alloc 1), .stmt (.mk 0 1 (some 1))] = false := rfl
example : chk [.stmt (.mk 0 0 none)] = false := rfl

end Core.Datatypes.Enum
