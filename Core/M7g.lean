import Core.M7c

/-!
# M7（五·上）：CFG 上的数据流检查（所有权 + 线性值）

真实编译器在控制流图（CFG）上做检查，而不是在结构化程序上。这一轮直接在 CFG 上证明健全性，
不经过结构化检查器（数据流迭代到不动点，比结构化检查器的两轮循环更宽，二者不能互相归约）。

**CFG**：节点列表。每个节点有一条可选命令（M7（二）的所有权、投影、调用、线性值命令）和后继列表；
后继为空表示出口。执行时由选择序列 `cs` 决定走哪个后继（`pick`）。

**检查分两步**：
- 推断 `infer`：从入口出发反复沿边传播、在汇合点合并（`joinS`），迭代固定轮数，得到每个节点入口的状态注解；
- 验证 `cfgOk`：对注解逐节点检查——命令通过，沿每条边走到的状态不比后继的注解强（`leS`），
  出口处没有未消费的线性值。

健全性只依赖验证这一步：**任何注解只要通过验证，程序就安全**，推断算法本身不需要证明。
注解在使用前先截断到前 `N` 个变量（`trunc`），这样比较只需看前 `N` 个变量。

**主定理** `safety_and_no_leak`：通过验证的 CFG，无论燃料多少、怎么选边，执行都不出错；
到达出口时，按 drop flag 释放后堆上没有活着的值，所有线性值都已被消费。
-/

namespace Core.M7g
open Core.M2b (Own SEnv dropAll)
open Core.M2L (leN leN_sound)
open Core.M4C (subL subL_sound good_weak)
open Core.M7b (C SS St checkC execC joinS Good BB Res stepC boundedC)

structure Node where
  c    : Option C      -- `none`：空操作（例如循环头、汇合点）
  succ : List Nat      -- 后继；空表示出口

abbrev CFG := List Node

/-- 按选择序列选一个后继：每个布尔值决定“走当前这条，还是看下一条”。 -/
def pick : List Nat → List Bool → Option (Nat × List Bool)
  | [],           _  => none
  | [t],          cs => some (t, cs)
  | t :: u :: ts, cs => if cs.headD false = true then some (t, cs.tail) else pick (u :: ts) cs.tail

/-! ## 动态语义 -/

def stepN (s : St) : Option C → Option St
  | none   => some s
  | some c => execC s c

def run (g : CFG) : Nat → Nat → St → List Bool → Res
  | 0,     _,  _, _  => .oof
  | n + 1, pc, s, cs =>
    match g[pc]? with
    | none    => .err
    | some nd =>
      match stepN s nd.c with
      | none    => .err
      | some s' =>
        match pick nd.succ cs with
        | none          => .ok s' cs
        | some (t, cs') => run g n t s' cs'

/-! ## 验证 -/

def trunc (N : Nat) (s : SS) : SS :=
  ⟨fun x => if x < N then s.σ x else .no, s.ps, fun x => if x < N then s.Λ x else false⟩

def checkN (N : Nat) (s : SS) : Option C → Option SS
  | none   => some s
  | some c => checkC N s c

/-- 沿边从状态 `a` 走到注解 `b` 合法：`b` 不比 `a` 强（所有权只会变成“可能”，锁表只会变少，
锁表里的源对象在 `b` 中确实拥有），线性值完全相同。 -/
def leS (N : Nat) (a b : SS) : Bool :=
  leN N a.σ b.σ && (subL b.ps a.ps &&
    (b.ps.all (fun e => decide (b.σ e.2 = .yes)) && Core.M6.eqN N a.Λ b.Λ))

def nodeOk (N : Nat) (g : CFG) (A : Nat → Option SS) (pc : Nat) : Bool :=
  match A pc with
  | none   => true     -- 走不到的节点
  | some a =>
    match g[pc]? with
    | none    => false
    | some nd =>
      match checkN N (trunc N a) nd.c with
      | none    => false
      | some s' =>
        (!nd.succ.isEmpty || Core.M6.allOff N s'.Λ) &&
        nd.succ.all (fun t =>
          match A t with
          | some b => decide (t < g.length) && leS N s' (trunc N b)
          | none   => false)

def cfgOk (N : Nat) (g : CFG) (A : Nat → Option SS) : Bool :=
  decide (0 < g.length) &&
  ((match A 0 with
    | some a => leS N SS.empty (trunc N a)
    | none   => false) &&
   (List.range g.length).all (nodeOk N g A))

/-! ## 推断：沿边传播、在汇合点合并，迭代固定轮数 -/

def joinA (N : Nat) : Option SS → SS → Option SS
  | none,   s => some s
  | some a, s =>
    match joinS N a s with
    | some j => some j
    | none   => some a      -- 合并失败：保留原注解，验证时会拒绝

def round (N : Nat) (g : CFG) (A : Nat → Option SS) : Nat → Option SS :=
  (List.range g.length).foldl (fun B pc =>
    match A pc, g[pc]? with
    | some a, some nd =>
      match checkN N (trunc N a) nd.c with
      | some s' => nd.succ.foldl (fun B t => upd B t (joinA N (B t) s')) B
      | none    => B
    | _, _ => B) A

def iter (N : Nat) (g : CFG) : Nat → (Nat → Option SS) → (Nat → Option SS)
  | 0,     A => A
  | k + 1, A => iter N g k (round N g A)

def infer (N : Nat) (g : CFG) : Nat → Option SS :=
  iter N g (2 * (g.length + N) + 2) (upd (fun _ => none) 0 (some SS.empty))

def accepts (N : Nat) (g : CFG) : Bool := cfgOk N g (infer N g)

/-! ## 引理 -/

theorem pick_mem : ∀ {ts : List Nat} {cs : List Bool} {t : Nat} {cs' : List Bool},
    pick ts cs = some (t, cs') → t ∈ ts
  | [], _, _, _, h => by simp [pick] at h
  | [_], _, _, _, h => by
    simp only [pick] at h
    cases h
    simp
  | _ :: u :: ts, cs, _, _, h => by
    simp only [pick] at h
    split at h
    · cases h
      simp
    · exact List.mem_cons_of_mem _ (pick_mem h)

theorem pick_none : ∀ {ts : List Nat} {cs : List Bool}, pick ts cs = none → ts = []
  | [], _, _ => rfl
  | [_], _, h => by simp [pick] at h
  | _ :: u :: ts, cs, h => by
    simp only [pick] at h
    split at h
    · cases h
    · cases pick_none h

theorem bb_trunc (N : Nat) (a : SS) : BB N (trunc N a) :=
  ⟨fun x hx => by simp [trunc, Nat.not_lt.mpr hx], fun x hx => by simp [trunc, Nat.not_lt.mpr hx]⟩

theorem stepN_sound {N : Nat} {s s' : SS} {st : St} {c : Option C}
    (hc : checkN N s c = some s') (hg : Good N s st) :
    ∃ st', stepN st c = some st' ∧ Good N s' st' := by
  cases c with
  | none =>
    simp only [checkN] at hc
    cases hc
    exact ⟨st, rfl, hg⟩
  | some c => exact stepC hc hg

theorem boundedN {N : Nat} {s s' : SS} {c : Option C}
    (hc : checkN N s c = some s') (hb : BB N s) : BB N s' := by
  cases c with
  | none =>
    simp only [checkN] at hc
    cases hc
    exact hb
  | some c => exact boundedC hc hb

theorem leS_sound {N : Nat} {a b : SS} {st : St} (h : leS N a b = true)
    (ha : BB N a) (hb : BB N b) (g : Good N a st) : Good N b st := by
  simp only [leS, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hy : ∀ e ∈ b.ps, b.σ e.2 = .yes := fun e he => by
    simpa using List.all_eq_true.mp h3 e he
  have hΛ : a.Λ = b.Λ := Core.M6.eqN_sound h4 ha.2 hb.2
  exact ⟨good_weak (leN_sound h1 ha.1 hb.1) (subL_sound h2) hy g.o, by rw [← hΛ]; exact g.l⟩

/-! ## 健全性 -/

def RG (N : Nat) : Res → Prop
  | .ok st _ => ∃ s, Good N s st ∧ ∀ x, s.Λ x = false
  | .err     => False
  | .oof     => True

theorem run_sound {N : Nat} {g : CFG} {A : Nat → Option SS}
    (h : (List.range g.length).all (nodeOk N g A) = true) (n : Nat) :
    ∀ (pc : Nat) (a : SS) (st : St) (cs : List Bool), pc < g.length → A pc = some a →
      Good N (trunc N a) st → RG N (run g n pc st cs) := by
  induction n with
  | zero =>
    intro pc a st cs _ _ _
    simp only [run, RG]
  | succ n ih =>
    intro pc a st cs hpc ha hgd
    have hn := List.all_eq_true.mp h pc (List.mem_range.mpr hpc)
    cases hg : g[pc]? with
    | none => simp [nodeOk, ha, hg] at hn
    | some nd =>
      cases hc : checkN N (trunc N a) nd.c with
      | none => simp [nodeOk, ha, hg, hc] at hn
      | some s' =>
        simp only [nodeOk, ha, hg, hc, Bool.and_eq_true] at hn
        obtain ⟨hexit, hedges⟩ := hn
        have hbs : BB N s' := boundedN hc (bb_trunc N a)
        obtain ⟨st', hst, g'⟩ := stepN_sound hc hgd
        cases hp : pick nd.succ cs with
        | none =>
          have hnil := pick_none hp
          have hoff : Core.M6.allOff N s'.Λ = true := by simpa [hnil] using hexit
          simp only [run, hg, hst, hp, RG]
          refine ⟨s', g', ?_⟩
          intro x
          by_cases hx : x < N
          · have := List.all_eq_true.mp hoff x (List.mem_range.mpr hx)
            simpa using this
          · exact hbs.2 x (Nat.le_of_not_lt hx)
        | some tc =>
          obtain ⟨t, cs'⟩ := tc
          have hmem := pick_mem hp
          have he := List.all_eq_true.mp hedges t hmem
          cases hA : A t with
          | none => simp [hA] at he
          | some b =>
            simp only [hA, Bool.and_eq_true, decide_eq_true_eq] at he
            simp only [run, hg, hst, hp]
            exact ih t b st' cs' he.1 hA (leS_sound he.2 hbs (bb_trunc N b) g')

/-! ## 主定理 -/

/-- **M7（五·上）主定理。** 通过验证的 CFG（任意注解 `A`），无论燃料多少、怎么选边，执行都不出错；
到达出口时，按 drop flag 释放不出错且堆上没有活着的值，所有线性值都已被消费。 -/
theorem safety_and_no_leak (N : Nat) (g : CFG) (A : Nat → Option SS) (h : cfgOk N g A = true)
    (fuel : Nat) (cs : List Bool) :
    run g fuel 0 St.empty cs ≠ .err ∧
    ∀ st cs', run g fuel 0 St.empty cs = .ok st cs' →
      (∃ b, dropAll st.o.b N = some b ∧ ∀ l, b.live l = false) ∧ ∀ l, st.l.live l = false := by
  simp only [cfgOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, h0, hall⟩ := h
  cases hA : A 0 with
  | none => simp [hA] at h0
  | some a =>
    simp only [hA] at h0
    have hb0 : BB N SS.empty := ⟨Core.M2L.bounded_empty N, fun _ _ => rfl⟩
    have g0 : Good N (trunc N a) St.empty :=
      leS_sound h0 hb0 (bb_trunc N a) (Core.M7b.good_empty N)
    have r := run_sound hall fuel 0 a St.empty cs hlen hA g0
    refine ⟨fun he => ?_, fun st cs' he => ?_⟩
    · rw [he] at r
      simp only [RG] at r
    · rw [he] at r
      simp only [RG] at r
      obtain ⟨s, gs, hoff⟩ := r
      exact ⟨Core.M7c.heap_clean gs.o, Core.M6e.no_live_ok gs.l hoff⟩

/-- 推断得到的注解通过验证时，同样安全。 -/
theorem accepts_safe (N : Nat) (g : CFG) (h : accepts N g = true) (fuel : Nat) (cs : List Bool) :
    run g fuel 0 St.empty cs ≠ .err :=
  (safety_and_no_leak N g (infer N g) h fuel cs).1

/-! ## 例子（变量 0 拥有堆内存，变量 1 是线性值） -/

def isErr : Res → Bool
  | .err => true
  | _    => false

def alloc0 : C := .own (.c (.base (.alloc 0)))
def use0   : C := .own (.c (.base (.use 0)))
def free0  : C := .own (.c (.base (.free 0)))

/-- `let v = alloc(); while … { use v }; free v`：接受。 -/
def loopUse : CFG :=
  [⟨some alloc0, [1]⟩, ⟨none, [2, 3]⟩, ⟨some use0, [1]⟩, ⟨some free0, []⟩]
example : accepts 2 loopUse = true := rfl
example : isErr (run loopUse 50 0 St.empty [true, true, false]) = false := rfl

/-- 循环里释放：第二轮会重复释放。合并后变量 0 是“可能拥有”，`free` 被拒绝。 -/
def loopFree : CFG :=
  [⟨some alloc0, [1]⟩, ⟨some free0, [2, 3]⟩, ⟨none, [1]⟩, ⟨none, []⟩]
example : accepts 2 loopFree = false := rfl
/-- 跳过检查直接执行：第二轮释放出错。 -/
example : isErr (run loopFree 50 0 St.empty [true, false]) = true := rfl

/-- `let t = new(); while … { }; consume t`：接受。 -/
def linLoop : CFG :=
  [⟨some (.lin (.lnew 1)), [1]⟩, ⟨none, [2, 3]⟩, ⟨none, [1]⟩, ⟨some (.lin (.consume 1)), []⟩]
example : accepts 2 linLoop = true := rfl

/-- 一个分支消费线性值、另一个分支不消费：汇合时线性值不一致，拒绝。 -/
def linBranch : CFG :=
  [⟨some (.lin (.lnew 1)), [1, 2]⟩, ⟨some (.lin (.consume 1)), [3]⟩, ⟨none, [3]⟩, ⟨none, []⟩]
example : accepts 2 linBranch = false := rfl

/-- 出口处线性值还没消费：拒绝。 -/
def linLeak : CFG := [⟨some (.lin (.lnew 1)), []⟩]
example : accepts 2 linLeak = false := rfl

end Core.M7g
