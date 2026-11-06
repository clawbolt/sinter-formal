import Core.M7e
import Core.M7g

/-!
# M7（五·下）：CFG 加入区域与 errdefer

在 M7（五·上）的 CFG 上加入：
- **区域**：节点操作 `enter`（进入区域，深度加一）、`leave`（离开区域，归还整块，深度减一），
  以及 M7（四·上）的引用命令。注解里每个节点同时记录**深度**和状态（所有权、锁表、线性值、引用变量表）；
  沿边走时深度必须相同。
- **errdefer**：在 CFG 里，`errdefer` 被展开成显式的清理代码。出错路径就是普通的边：
  先走到清理节点（例如 `consume t`），再到一个**出错出口**（`raise = true`）。
  所以 CFG 不需要专门的 `guard`：出错出口和正常出口一样，要求深度为 0、所有线性值都已消费。

**主定理** `safety_and_no_leak`：通过验证的 CFG（任意注解），执行不出错；无论从正常出口还是出错出口离开，
堆上没有活着的值、线性值都已被消费、没有区域残留。
-/

namespace Core.M7h
open Core.M2L (leN)
open Core.M7d (C4 S4 St Res checkC4 execC4 join4 leaveS enterSt leaveSt leV G B4 Clean
  bv_restrict leV_sound good_weakV stepC4 boundC4 regions_clean)
open Core.M7g (pick pick_mem pick_none trunc)

inductive Op
  | nop
  | cmd   (c : C4)
  | enter
  | leave

structure Node where
  op    : Op
  succ  : List Nat     -- 后继；空表示出口
  raise : Bool         -- 出口类型：`true` 为出错出口

abbrev CFG := List Node

/-! ## 动态语义 -/

def stepOp (s : St) : Op → Option St
  | .nop   => some s
  | .cmd c => execC4 s c
  | .enter => some (enterSt s)
  | .leave => some (leaveSt (s.r.rs.d - 1) s)

def run (g : CFG) : Nat → Nat → St → List Bool → Res
  | 0,     _,  _, _  => .oof
  | n + 1, pc, s, cs =>
    match g[pc]? with
    | none    => .err
    | some nd =>
      match stepOp s nd.op with
      | none    => .err
      | some s' =>
        match pick nd.succ cs with
        | none =>
          match nd.raise with
          | true  => .exn s' cs
          | false => .ok s' cs
        | some (t, cs') => run g n t s' cs'

/-! ## 验证 -/

def trunc4 (N : Nat) (s : S4) : S4 :=
  ⟨trunc N s.b, { s.r with v := fun x => if x < N then s.r.v x else none }⟩

def checkOp (N d : Nat) (s : S4) : Op → Option (Nat × S4)
  | .nop   => some (d, s)
  | .cmd c =>
    match checkC4 N d s c with
    | some s' => some (d, s')
    | none    => none
  | .enter => some (d + 1, s)
  | .leave =>
    match d with
    | 0      => none
    | d' + 1 => some (d', leaveS d' s)

/-- 沿边从 `(d1, a)` 走到注解 `(d2, b)` 合法：深度相同，`b` 不比 `a` 强。 -/
def leS4 (N d1 : Nat) (a : S4) (d2 : Nat) (b : S4) : Bool :=
  decide (d1 = d2) && (Core.M7g.leS N a.b b.b && leV N a.r.v b.r.v)

def nodeOk (N : Nat) (g : CFG) (A : Nat → Option (Nat × S4)) (pc : Nat) : Bool :=
  match A pc with
  | none        => true
  | some (d, a) =>
    match g[pc]? with
    | none    => false
    | some nd =>
      match checkOp N d (trunc4 N a) nd.op with
      | none          => false
      | some (d', s') =>
        (!nd.succ.isEmpty || (decide (d' = 0) && Core.M6.allOff N s'.b.Λ)) &&
        nd.succ.all (fun t =>
          match A t with
          | some (dt, b) => decide (t < g.length) && leS4 N d' s' dt (trunc4 N b)
          | none         => false)

def cfgOk (N : Nat) (g : CFG) (A : Nat → Option (Nat × S4)) : Bool :=
  decide (0 < g.length) &&
  ((match A 0 with
    | some (d, a) => decide (d = 0) && leS4 N 0 S4.empty d (trunc4 N a)
    | none        => false) &&
   (List.range g.length).all (nodeOk N g A))

/-! ## 推断 -/

def joinA (N : Nat) : Option (Nat × S4) → Nat × S4 → Option (Nat × S4)
  | none,         x      => some x
  | some (da, a), (d, s) =>
    if da = d then
      match join4 N a s with
      | some j => some (da, j)
      | none   => some (da, a)
    else some (da, a)          -- 深度不一致：保留原注解，验证时会拒绝

def round (N : Nat) (g : CFG) (A : Nat → Option (Nat × S4)) : Nat → Option (Nat × S4) :=
  (List.range g.length).foldl (fun B pc =>
    match B pc, g[pc]? with
    | some (d, a), some nd =>
      match checkOp N d (trunc4 N a) nd.op with
      | some x => nd.succ.foldl (fun B t => upd B t (joinA N (B t) x)) B
      | none   => B
    | _, _ => B) A

def iter (N : Nat) (g : CFG) : Nat → (Nat → Option (Nat × S4)) → (Nat → Option (Nat × S4))
  | 0,     A => A
  | k + 1, A => iter N g k (round N g A)

def infer (N : Nat) (g : CFG) : Nat → Option (Nat × S4) :=
  iter N g (g.length + 2) (upd (fun _ => none) 0 (some (0, S4.empty)))

def accepts (N : Nat) (g : CFG) : Bool := cfgOk N g (infer N g)

/-! ## 引理 -/

theorem b4_trunc (N : Nat) (a : S4) : B4 N (trunc4 N a) :=
  ⟨Core.M7g.bb_trunc N a.b, fun x hx => by simp [trunc4, Nat.not_lt.mpr hx]⟩

theorem stepOp_sound {N d d' : Nat} {s s' : S4} {st : St} {op : Op}
    (hc : checkOp N d s op = some (d', s')) (hg : G N d s st) :
    ∃ st', stepOp st op = some st' ∧ G N d' s' st' := by
  cases op with
  | nop =>
    simp only [checkOp] at hc
    cases hc
    exact ⟨st, rfl, hg⟩
  | cmd c =>
    simp only [checkOp] at hc
    split at hc
    · rename_i s₁ h₁
      cases hc
      exact stepC4 h₁ hg
    · contradiction
  | enter =>
    simp only [checkOp] at hc
    cases hc
    exact ⟨enterSt st, rfl, ⟨hg.m, Core.M5b.enter_good hg.r⟩⟩
  | leave =>
    cases d with
    | zero => simp [checkOp] at hc
    | succ d =>
      simp only [checkOp, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨h1, h2⟩ := hc
      subst h1
      subst h2
      have hd : st.r.rs.d = d + 1 := hg.r.stk.depth
      refine ⟨leaveSt d st, ?_, ⟨hg.m, Core.M5b.leave_good hg.r⟩⟩
      simp [stepOp, hd]

theorem boundOp {N d d' : Nat} {s s' : S4} {op : Op}
    (hc : checkOp N d s op = some (d', s')) (hb : B4 N s) : B4 N s' := by
  cases op with
  | nop =>
    simp only [checkOp] at hc
    cases hc
    exact hb
  | cmd c =>
    simp only [checkOp] at hc
    split at hc
    · rename_i s₁ h₁
      cases hc
      exact boundC4 h₁ hb
    · contradiction
  | enter =>
    simp only [checkOp] at hc
    cases hc
    exact hb
  | leave =>
    cases d with
    | zero => simp [checkOp] at hc
    | succ d =>
      simp only [checkOp] at hc
      cases hc
      exact ⟨hb.1, bv_restrict hb.2⟩

theorem leS4_sound {N d1 d2 : Nat} {a b : S4} {st : St} (h : leS4 N d1 a d2 b = true)
    (ha : B4 N a) (hb : B4 N b) (g : G N d1 a st) : G N d2 b st := by
  simp only [leS4, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1
  exact ⟨Core.M7g.leS_sound h2 ha.1 hb.1 g.m, good_weakV (leV_sound h3 hb.2) g.r⟩

/-! ## 健全性 -/

def RG (N : Nat) : Res → Prop
  | .ok st _  => ∃ s, G N 0 s st ∧ ∀ x, s.b.Λ x = false
  | .exn st _ => ∃ s, G N 0 s st ∧ ∀ x, s.b.Λ x = false
  | .err      => False
  | .oof      => True

theorem run_sound {N : Nat} {g : CFG} {A : Nat → Option (Nat × S4)}
    (h : (List.range g.length).all (nodeOk N g A) = true) (n : Nat) :
    ∀ (pc d : Nat) (a : S4) (st : St) (cs : List Bool), pc < g.length → A pc = some (d, a) →
      G N d (trunc4 N a) st → RG N (run g n pc st cs) := by
  induction n with
  | zero =>
    intro pc d a st cs _ _ _
    simp only [run, RG]
  | succ n ih =>
    intro pc d a st cs hpc ha hgd
    have hn := List.all_eq_true.mp h pc (List.mem_range.mpr hpc)
    cases hg : g[pc]? with
    | none => simp [nodeOk, ha, hg] at hn
    | some nd =>
      cases hc : checkOp N d (trunc4 N a) nd.op with
      | none => simp [nodeOk, ha, hg, hc] at hn
      | some x =>
        obtain ⟨d', s'⟩ := x
        simp only [nodeOk, ha, hg, hc, Bool.and_eq_true] at hn
        obtain ⟨hexit, hedges⟩ := hn
        have hbs : B4 N s' := boundOp hc (b4_trunc N a)
        obtain ⟨st', hst, g'⟩ := stepOp_sound hc hgd
        cases hp : pick nd.succ cs with
        | none =>
          have hnil := pick_none hp
          have hex : d' = 0 ∧ Core.M6.allOff N s'.b.Λ = true := by simpa [hnil] using hexit
          obtain ⟨hd0, hoff⟩ := hex
          subst hd0
          have hall : ∀ x, s'.b.Λ x = false := by
            intro x
            by_cases hx : x < N
            · have := List.all_eq_true.mp hoff x (List.mem_range.mpr hx)
              simpa using this
            · exact hbs.1.2 x (Nat.le_of_not_lt hx)
          cases hr : nd.raise <;> simp only [run, hg, hst, hp, hr, RG] <;> exact ⟨s', g', hall⟩
        | some tc =>
          obtain ⟨t, cs'⟩ := tc
          have hmem := pick_mem hp
          have he := List.all_eq_true.mp hedges t hmem
          cases hA : A t with
          | none => simp [hA] at he
          | some y =>
            obtain ⟨dt, b⟩ := y
            simp only [hA, Bool.and_eq_true, decide_eq_true_eq] at he
            simp only [run, hg, hst, hp]
            exact ih t dt b st' cs' he.1 hA (leS4_sound he.2 hbs (b4_trunc N b) g')

/-! ## 主定理 -/

/-- **M7（五·下）主定理。** 通过验证的 CFG（任意注解 `A`），无论燃料多少、怎么选边，执行都不出错；
无论从正常出口还是出错出口离开，堆上没有活着的值、所有线性值都已被消费、没有区域残留。 -/
theorem safety_and_no_leak (N : Nat) (g : CFG) (A : Nat → Option (Nat × S4))
    (h : cfgOk N g A = true) (fuel : Nat) (cs : List Bool) :
    run g fuel 0 St.empty cs ≠ .err ∧
    (∀ st cs', run g fuel 0 St.empty cs = .ok st cs' → Clean N st) ∧
    (∀ st cs', run g fuel 0 St.empty cs = .exn st cs' → Clean N st) := by
  simp only [cfgOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, h0, hall⟩ := h
  cases hA : A 0 with
  | none => simp [hA] at h0
  | some y =>
    obtain ⟨d0, a⟩ := y
    simp only [hA, Bool.and_eq_true, decide_eq_true_eq] at h0
    obtain ⟨hd0, h0⟩ := h0
    subst hd0
    have hb0 : B4 N S4.empty := ⟨⟨Core.M2L.bounded_empty N, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    have g0 : G N 0 S4.empty St.empty := ⟨Core.M7b.good_empty N, Core.M5b.good_empty⟩
    have g1 := leS4_sound h0 hb0 (b4_trunc N a) g0
    have r := run_sound hall fuel 0 0 a St.empty cs hlen hA g1
    refine ⟨fun he => ?_, fun st cs' he => ?_, fun st cs' he => ?_⟩
    · rw [he] at r
      simp only [RG] at r
    · rw [he] at r
      simp only [RG] at r
      obtain ⟨s, gs, hoff⟩ := r
      exact ⟨Core.M7c.heap_clean gs.m.o, Core.M6e.no_live_ok gs.m.l hoff, regions_clean gs.r⟩
    · rw [he] at r
      simp only [RG] at r
      obtain ⟨s, gs, hoff⟩ := r
      exact ⟨Core.M7c.heap_clean gs.m.o, Core.M6e.no_live_ok gs.m.l hoff, regions_clean gs.r⟩

/-! ## 例子（线性值用 1，引用变量用 3） -/

def isErr : Res → Bool
  | .err => true
  | _    => false

def isExn : Res → Bool
  | .exn _ _ => true
  | _        => false

/-- 出错退出时第 0 个线性值还活着。 -/
def linLeftExn : Res → Bool
  | .exn s _ => s.m.l.live 0
  | _        => false

def rdecl (x k : Nat) : Op := .cmd (.reg (.decl x k))
def ralloc (x k : Nat) : Op := .cmd (.reg (.ralloc x k))
def rread (x : Nat) : Op := .cmd (.reg (.read x))
def lnew (x : Nat) : Op := .cmd (.base (.lin (.lnew x)))
def consume (x : Nat) : Op := .cmd (.base (.lin (.consume x)))

/-- 区域里声明引用，循环里每轮分配再读，最后离开区域：接受。 -/
def regionLoop : CFG :=
  [⟨.enter, [1], false⟩, ⟨rdecl 3 0, [2], false⟩, ⟨.nop, [3, 5], false⟩,
   ⟨ralloc 3 0, [4], false⟩, ⟨rread 3, [2], false⟩, ⟨.leave, [6], false⟩, ⟨.nop, [], false⟩]
set_option maxRecDepth 100000 in
example : accepts 5 regionLoop = true := rfl
example : isErr (run regionLoop 50 0 St.empty [true, true, false]) = false := rfl

/-- `let t = new(); errdefer consume t; if bad { fail }; consume t` 展开后的 CFG：
出错路径先走清理节点 `consume t` 再到出错出口。接受；出错路径干净。 -/
def errdeferCfg : CFG :=
  [⟨lnew 1, [1, 2], false⟩, ⟨consume 1, [], true⟩, ⟨consume 1, [], false⟩]
example : accepts 5 errdeferCfg = true := rfl
example : isExn (run errdeferCfg 50 0 St.empty [true]) = true := rfl
example : linLeftExn (run errdeferCfg 50 0 St.empty [true]) = false := rfl

/-- 忘了清理：出错出口处线性值还没消费，拒绝。 -/
def noCleanup : CFG :=
  [⟨lnew 1, [1, 2], false⟩, ⟨.nop, [], true⟩, ⟨consume 1, [], false⟩]
example : accepts 5 noCleanup = false := rfl
/-- 跳过检查直接执行：出错退出时线性值泄漏。 -/
example : linLeftExn (run noCleanup 50 0 St.empty [true]) = true := rfl

/-- 区域没有离开就到了出口：拒绝。 -/
def noLeave : CFG := [⟨.enter, [1], false⟩, ⟨.nop, [], false⟩]
example : accepts 5 noLeave = false := rfl

/-- 离开区域之后读其中的引用：拒绝。 -/
def readAfter : CFG :=
  [⟨.enter, [1], false⟩, ⟨rdecl 3 0, [2], false⟩, ⟨ralloc 3 0, [3], false⟩,
   ⟨.leave, [4], false⟩, ⟨rread 3, [], false⟩]
set_option maxRecDepth 100000 in
example : accepts 5 readAfter = false := rfl

end Core.M7h
