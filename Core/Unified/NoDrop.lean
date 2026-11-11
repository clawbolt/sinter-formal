import Core.Unified.RegionProofs

/-!
# 合并演算里的 D4

在 `Unified.RegionDefs` 的合并演算上加一条命令 `rstore x k`：把 `x` 的值移进区域 `k`。
区域结束时整块归还、**不运行析构**，所以移进区域的值如果拥有堆内存（带 `Drop`）或者是 `linear` 值，
就再也没人释放或消费它。

**D4 是类型规则**：带 `Drop` / `linear` 的类型不能分配进区域。类型检查覆盖每一个表达式，
包括走不到的代码，所以这里把 D4 写成对整个程序的语法检查 `noStore`（程序里没有 `rstore`），
然后照常运行 `Unified.RegionDefs` 的检查器。

- **主定理** `safety_and_no_leak`：D4 规则下被接受的程序，执行不出错；无论正常结束还是出错退出，
  堆、线性值、区域都是干净的。证明：没有 `rstore` 的程序和它在 `Unified.RegionDefs` 里的对应程序执行完全相同
  （`exec_erase`），再用 `Unified.RegionDefs` 的主定理。
- **反例**：违反 D4 的规则（`D4Rule.noD4`，把 `rstore` 当作一次移出，`x` 不再是拥有者 / 线性值已处理）
  接受 `leakHeap`、`leakLin`，但执行结束时堆上仍有活着的内存、线性值没有被消费。
-/

namespace Core.Unified.NoDrop
open Core.Ownership.Branch (Own SEnv)
open Core.Ownership.Loop (leN)
open Core.Projection.Branches (subL)
open Core.Linearity.Errdefer (covers)
open Core.Unified.RegionDefs (C4 Q S4 St Res checkC4 join4 joinO head4 leaveS enterSt leaveSt execC4 Clean leV)

inductive C5
  | c4     (c : C4)
  | rstore (x : Var) (k : Nat)   -- 把 `x` 的值移进区域 `k`

inductive Q5
  | skip
  | cmd    (c : C5)
  | seq    (p q : Q5)
  | branch (p q : Q5)
  | loop   (b : Q5)
  | fail
  | guard  (x : Var) (p : Q5)
  | block  (p : Q5)

/-- 程序里没有 `rstore`。 -/
def noStore : Q5 → Bool
  | .skip              => true
  | .cmd (.c4 _)       => true
  | .cmd (.rstore _ _) => false
  | .seq p q           => noStore p && noStore q
  | .branch p q        => noStore p && noStore q
  | .loop b            => noStore b
  | .fail              => true
  | .guard _ p         => noStore p
  | .block p           => noStore p

/-- 去掉 `rstore` 得到 `Unified.RegionDefs` 的程序（只在 `noStore` 成立时使用）。 -/
def erase : Q5 → Q
  | .skip              => .skip
  | .cmd (.c4 c)       => .cmd c
  | .cmd (.rstore _ _) => .skip
  | .seq p q           => .seq (erase p) (erase q)
  | .branch p q        => .branch (erase p) (erase q)
  | .loop b            => .loop (erase b)
  | .fail              => .fail
  | .guard x p         => .guard x (erase p)
  | .block p           => .block (erase p)

/-! ## 违反 D4 的检查器：`rstore` 被当作一次移出 -/

def owns (σ : SEnv) (x : Var) : Bool :=
  match σ x with
  | .yes => true
  | _    => false

def checkC5 (N d : Nat) (s : S4) : C5 → Option S4
  | .c4 c => checkC4 N d s c
  | .rstore x k =>
    if x < N ∧ k < d ∧ (owns s.b.σ x = true ∨ s.b.Λ x = true) then
      some ⟨⟨upd s.b.σ x .no, s.b.ps, upd s.b.Λ x false⟩, s.r⟩
    else none

def check5 (N : Nat) : Nat → List Var → Q5 → S4 → Option (Option S4)
  | _, _, .skip, s => some (some s)
  | d, _, .cmd c, s =>
    match checkC5 N d s c with
    | some s' => some (some s')
    | none    => none
  | d, E, .seq p q, s =>
    match check5 N d E p s with
    | some (some s₁) => check5 N d E q s₁
    | some none      => some none
    | none           => none
  | d, E, .branch p q, s =>
    match check5 N d E p s, check5 N d E q s with
    | some oa, some ob => joinO N oa ob
    | _, _             => none
  | d, E, .loop b, s =>
    match check5 N d E b s with
    | none           => none
    | some none      => some (some s)
    | some (some sb) =>
      if Core.Linearity.Linear.eqN N sb.b.Λ s.b.Λ = true then
        match check5 N d E b (head4 s sb) with
        | some (some s2) =>
          if leN N s2.b.σ (head4 s sb).b.σ = true ∧ subL (head4 s sb).b.ps s2.b.ps = true ∧
              Core.Linearity.Linear.eqN N s2.b.Λ s.b.Λ = true ∧ leV N s2.r.v (head4 s sb).r.v = true then
            some (some (head4 s sb))
          else none
        | some none => none
        | none      => none
      else none
  | _, E, .fail, s => if covers N s.b.Λ E = true then some none else none
  | d, E, .guard x p, s =>
    if s.b.Λ x = true ∧ x ∉ E ∧ x < N then check5 N d (x :: E) p s else none
  | d, E, .block p, s =>
    match check5 N (d + 1) E p s with
    | some (some s₁) => some (some (leaveS d s₁))
    | some none      => some none
    | none           => none

inductive D4Rule | d4 | noD4

def accepts5 : D4Rule → Nat → Q5 → Bool
  | .d4,   N, p => noStore p && Core.Unified.RegionDefs.accepts N (erase p)
  | .noD4, N, p =>
    match check5 N 0 [] p S4.empty with
    | some (some s) => Core.Linearity.Linear.allOff N s.b.Λ
    | some none     => true
    | none          => false

/-! ## 动态语义：区域接管这个值，drop flag 清掉，线性值的指针清掉；区域结束时不运行析构 -/

def execC5 (s : St) : C5 → Option St
  | .c4 c => execC4 s c
  | .rstore x _ =>
    some ⟨⟨⟨{ s.m.o.b with flag := upd s.m.o.b.flag x false }, s.m.o.pr⟩,
            { s.m.l with ptr := upd s.m.l.ptr x none }⟩, s.r⟩

def exec5 : Nat → Q5 → St → List Bool → Res
  | 0,     _,           _, _  => .oof
  | _ + 1, .skip,       s, cs => .ok s cs
  | _ + 1, .cmd c,      s, cs =>
    match execC5 s c with
    | some s' => .ok s' cs
    | none    => .err
  | n + 1, .seq p q,    s, cs =>
    match exec5 n p s cs with
    | .ok s₁ cs₁  => exec5 n q s₁ cs₁
    | .exn s₁ cs₁ => .exn s₁ cs₁
    | .err        => .err
    | .oof        => .oof
  | n + 1, .branch p q, s, cs =>
    if cs.headD false = true then exec5 n p s cs.tail else exec5 n q s cs.tail
  | n + 1, .loop b,     s, cs =>
    if cs.headD false = true then
      match exec5 n b s cs.tail with
      | .ok s₁ cs₁  => exec5 n (.loop b) s₁ cs₁
      | .exn s₁ cs₁ => .exn s₁ cs₁
      | .err        => .err
      | .oof        => .oof
    else .ok s cs.tail
  | _ + 1, .fail,       s, cs => .exn s cs
  | n + 1, .guard x p,  s, cs =>
    match exec5 n p s cs with
    | .exn s₁ cs₁ =>
      match Core.Linearity.Linear.execS s₁.m.l (.consume x) with
      | some l' => .exn ⟨⟨s₁.m.o, l'⟩, s₁.r⟩ cs₁
      | none    => .err
    | .ok s₁ cs₁ => .ok s₁ cs₁
    | .err       => .err
    | .oof       => .oof
  | n + 1, .block p,    s, cs =>
    match exec5 n p (enterSt s) cs with
    | .ok s₁ cs₁  => .ok (leaveSt s.r.rs.d s₁) cs₁
    | .exn s₁ cs₁ => .exn (leaveSt s.r.rs.d s₁) cs₁
    | .err        => .err
    | .oof        => .oof

/-! ## 没有 `rstore` 的程序和 `Unified.RegionDefs` 执行相同 -/

theorem exec_erase (n : Nat) : ∀ (p : Q5) (st : St) (cs : List Bool),
    noStore p = true → exec5 n p st cs = Core.Unified.RegionDefs.exec n (erase p) st cs := by
  induction n with
  | zero =>
    intro p st cs _
    cases p with
    | cmd c => cases c <;> rfl
    | _ => rfl
  | succ n ih =>
    intro p st cs hs
    cases p with
    | skip => rfl
    | cmd c =>
      cases c with
      | c4 c =>
        show (match execC4 st c with
              | some s' => Res.ok s' cs
              | none    => Res.err) =
             (match execC4 st c with
              | some s' => Res.ok s' cs
              | none    => Res.err)
        rfl
      | rstore x k => simp [noStore] at hs
    | seq p q =>
      simp only [noStore, Bool.and_eq_true] at hs
      simp only [exec5, erase, Core.Unified.RegionDefs.exec, ih p st cs hs.1]
      all_goals
        cases h : Core.Unified.RegionDefs.exec n (erase p) st cs with
        | ok s₁ cs₁ => exact ih q s₁ cs₁ hs.2
        | exn => rfl
        | err => rfl
        | oof => rfl
    | branch p q =>
      simp only [noStore, Bool.and_eq_true] at hs
      simp only [exec5, erase, Core.Unified.RegionDefs.exec]
      rw [ih p _ _ hs.1, ih q _ _ hs.2]
    | loop b =>
      have hb : noStore b = true := hs
      simp only [exec5, erase, Core.Unified.RegionDefs.exec]
      by_cases hc : cs.headD false = true
      · rw [ite_eq_left hc, ite_eq_left hc, ih b _ _ hb]
        cases h : Core.Unified.RegionDefs.exec n (erase b) st cs.tail with
        | ok s₁ cs₁ => exact ih (.loop b) s₁ cs₁ hs
        | exn => rfl
        | err => rfl
        | oof => rfl
      · rw [ite_eq_right hc, ite_eq_right hc]
    | fail => rfl
    | guard x p =>
      have hp : noStore p = true := hs
      simp only [exec5, erase, Core.Unified.RegionDefs.exec, ih p st cs hp]
      all_goals
        cases h : Core.Unified.RegionDefs.exec n (erase p) st cs <;> rfl
    | block p =>
      have hp : noStore p = true := hs
      simp only [exec5, erase, Core.Unified.RegionDefs.exec, ih p (enterSt st) cs hp]
      all_goals
        cases h : Core.Unified.RegionDefs.exec n (erase p) (enterSt st) cs <;> rfl

/-! ## 主定理 -/

/-- **`Unified.NoDrop` 主定理。** D4 规则下被接受的程序执行不出错；无论正常结束还是出错退出，
堆上没有活着的值、所有线性值都已被消费、没有区域残留。 -/
theorem safety_and_no_leak (N : Nat) (p : Q5) (h : accepts5 .d4 N p = true)
    (fuel : Nat) (cs : List Bool) :
    exec5 fuel p St.empty cs ≠ .err ∧
    (∀ st cs', exec5 fuel p St.empty cs = .ok st cs' → Clean N st) ∧
    (∀ st cs', exec5 fuel p St.empty cs = .exn st cs' → Clean N st) := by
  simp only [accepts5, Bool.and_eq_true] at h
  rw [exec_erase fuel p St.empty cs h.1]
  exact Core.Unified.RegionDefs.safety_and_no_leak N (erase p) h.2 fuel cs

/-! ## 反例 -/

def seqs : List Q5 → Q5
  | []      => .skip
  | p :: ps => .seq p (seqs ps)

/-- 结束时（先按 drop flag 析构所有拥有者）堆上第 0 块内存还活着。 -/
def heapLeft (r : Res) : Bool :=
  match r with
  | .ok s _ =>
    match Core.Ownership.Branch.dropAll s.m.o.b 5 with
    | some b => b.live 0
    | none   => false
  | _ => false

/-- 结束时第 0 个线性值还没有被消费。 -/
def linLeft (r : Res) : Bool :=
  match r with
  | .ok s _ => s.m.l.live 0
  | _       => false

/-- `let v = alloc(); 把 v 移进区域`：拥有堆内存的值进了区域。 -/
def leakHeap : Q5 := .block (seqs
  [.cmd (.c4 (.base (.own (.c (.base (.alloc 0)))))), .cmd (.rstore 0 0)])
example : accepts5 .noD4 5 leakHeap = true := rfl
example : heapLeft (exec5 50 leakHeap Core.Unified.RegionDefs.St.empty []) = true := rfl
example : accepts5 .d4 5 leakHeap = false := rfl

/-- `let t = new(); 把 t 移进区域`：线性值进了区域。 -/
def leakLin : Q5 := .block (seqs
  [.cmd (.c4 (.base (.lin (.lnew 1)))), .cmd (.rstore 1 0)])
example : accepts5 .noD4 5 leakLin = true := rfl
example : linLeft (exec5 50 leakLin Core.Unified.RegionDefs.St.empty []) = true := rfl
example : accepts5 .d4 5 leakLin = false := rfl

/-- 区域里只放普通引用：D4 规则接受。 -/
def plain : Q5 := .block (seqs
  [.cmd (.c4 (.reg (.decl 3 0))), .cmd (.c4 (.reg (.ralloc 3 0))), .cmd (.c4 (.reg (.read 3)))])
example : accepts5 .d4 5 plain = true := rfl

end Core.Unified.NoDrop
