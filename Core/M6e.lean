import Core.M6

/-!
# M6（二）：`errdefer` 与出错退出

在 M6（一）上加入出错退出：
- `fail`：出错，沿着调用链一路向外退出；
- `guard x p`：`errdefer consume x; p`。执行 `p`，如果 `p` 出错退出，先消费 `x`，再继续向外退出；
  如果 `p` 正常结束，什么也不做。

**静态检查**多了一个参数 `E`：当前所有生效的 `errdefer` 会消费的变量。
- `fail` 处要求：持有线性值的变量恰好就是 `E` 里的变量（`covers`）。
  多了就会在出错路径上被遗漏；少了，`errdefer` 就会消费一个已经消费过的值。
- `guard x p` 要求 `x` 此刻持有线性值，并且不在 `E` 里；检查 `p` 时把 `x` 加入 `E`。
- 检查结果多了一种“不会正常结束”（`none`）：`fail` 之后的代码走不到，
  分支汇合时这一边不参与比较（`joinO`）。

**主定理** `safety_and_no_leak`：被接受的程序，无论燃料多少、分支怎么走、循环跑几轮，
执行都不会出错（`errdefer` 不会重复消费）；**无论正常结束还是出错退出**，
所有线性值都已被消费。

**例子**：常见写法 `let x = new(); errdefer consume x; if bad { fail }; consume x` 被接受，
两条路径都干净；去掉 `errdefer` 后，出错路径会遗漏 `x`；在 `errdefer` 的作用范围里先手动消费再出错，
`errdefer` 会重复消费。后两种都被拒绝。
-/

namespace Core.M6e
open Core.M6 (Stmt LEnv varsOk checkS eqN allOff St execS LInv Bounded consume_ok stepS
  bounded_checkS eqN_sound linv_empty)

inductive Q
  | skip
  | stmt   (t : Stmt)
  | seq    (p q : Q)
  | branch (p q : Q)
  | loop   (b : Q)
  | fail
  | guard  (x : Var) (p : Q)

/-- 正常结束时的状态；`none` 表示不会正常结束。 -/
abbrev Out := Option LEnv

/-! ## 静态检查 -/

def joinO (N : Nat) : Out → Out → Option Out
  | none,   b      => some b
  | some a, none   => some (some a)
  | some a, some b => if eqN N a b = true then some (some a) else none

/-- 出错处：持有线性值的变量恰好就是 `errdefer` 会消费的变量。 -/
def covers (N : Nat) (Λ : LEnv) (E : List Var) : Bool :=
  (List.range N).all (fun x => Λ x == decide (x ∈ E))

def check (N : Nat) : List Var → Q → LEnv → Option Out
  | _, .skip, Λ => some (some Λ)
  | _, .stmt t, Λ =>
    if varsOk N t = true then
      match checkS Λ t with
      | some Λ' => some (some Λ')
      | none    => none
    else none
  | E, .seq p q, Λ =>
    match check N E p Λ with
    | some (some Λ₁) => check N E q Λ₁
    | some none      => some none
    | none           => none
  | E, .branch p q, Λ =>
    match check N E p Λ, check N E q Λ with
    | some oa, some ob => joinO N oa ob
    | _, _             => none
  | E, .loop b, Λ =>
    match check N E b Λ with
    | some (some Λ₁) => if eqN N Λ₁ Λ = true then some (some Λ) else none
    | some none      => some (some Λ)
    | none           => none
  | E, .fail, Λ => if covers N Λ E = true then some none else none
  | E, .guard x p, Λ =>
    if Λ x = true ∧ x ∉ E ∧ x < N then check N (x :: E) p Λ else none

/-- 被接受：检查通过，并且正常结束时没有未消费的线性值。 -/
def accepts (N : Nat) (p : Q) : Bool :=
  match check N [] p (fun _ => false) with
  | some (some L) => allOff N L
  | some none     => true
  | none          => false

/-! ## 动态语义 -/

inductive Res
  | ok  (s : St) (cs : List Bool)
  | exn (s : St) (cs : List Bool)    -- 出错退出
  | err                              -- 内存错误（重复消费）
  | oof

def exec : Nat → Q → St → List Bool → Res
  | 0,     _,           _, _  => .oof
  | _ + 1, .skip,       s, cs => .ok s cs
  | _ + 1, .stmt t,     s, cs =>
    match execS s t with
    | some s' => .ok s' cs
    | none    => .err
  | n + 1, .seq p q,    s, cs =>
    match exec n p s cs with
    | .ok s₁ cs₁  => exec n q s₁ cs₁
    | .exn s₁ cs₁ => .exn s₁ cs₁
    | .err        => .err
    | .oof        => .oof
  | n + 1, .branch p q, s, cs =>
    if cs.headD false = true then exec n p s cs.tail else exec n q s cs.tail
  | n + 1, .loop b,     s, cs =>
    if cs.headD false = true then
      match exec n b s cs.tail with
      | .ok s₁ cs₁  => exec n (.loop b) s₁ cs₁
      | .exn s₁ cs₁ => .exn s₁ cs₁
      | .err        => .err
      | .oof        => .oof
    else .ok s cs.tail
  | _ + 1, .fail,       s, cs => .exn s cs
  | n + 1, .guard x p,  s, cs =>
    match exec n p s cs with
    | .exn s₁ cs₁ =>
      match execS s₁ (.consume x) with
      | some s₂ => .exn s₂ cs₁
      | none    => .err
    | .ok s₁ cs₁ => .ok s₁ cs₁
    | .err       => .err
    | .oof       => .oof

/-- 正常结束：状态符合检查结果；出错退出：持有线性值的变量恰好是外层 `errdefer` 会消费的。 -/
def GoodR (o : Out) (E : List Var) : Res → Prop
  | .ok s _  => ∃ L, o = some L ∧ LInv L s
  | .exn s _ => ∃ L, LInv L s ∧ ∀ x, L x = true ↔ x ∈ E
  | .err     => False
  | .oof     => True

def BoundedO (N : Nat) (o : Out) : Prop := ∀ L, o = some L → Bounded N L

/-! ## 引理 -/

theorem covers_sound {N : Nat} {Λ : LEnv} {E : List Var} (h : covers N Λ E = true)
    (hb : Bounded N Λ) (hE : ∀ y ∈ E, y < N) : ∀ x, Λ x = true ↔ x ∈ E := by
  intro x
  by_cases hx : x < N
  · have h2 : (Λ x == decide (x ∈ E)) = true := List.all_eq_true.mp h x (List.mem_range.mpr hx)
    cases hΛ : Λ x <;> by_cases hm : x ∈ E <;> simp [hΛ, hm] at h2 ⊢
  · rw [hb x (Nat.le_of_not_lt hx)]
    constructor
    · intro h'
      cases h'
    · intro hm
      exact absurd (hE x hm) hx

theorem joinO_bounded {N : Nat} {oa ob o : Out} (h : joinO N oa ob = some o)
    (ha : BoundedO N oa) (hb : BoundedO N ob) : BoundedO N o := by
  cases oa with
  | none =>
    simp only [joinO] at h
    cases h
    exact hb
  | some a =>
    cases ob with
    | none =>
      simp only [joinO] at h
      cases h
      exact ha
    | some b =>
      simp only [joinO] at h
      split at h
      · cases h
        exact ha
      · contradiction

theorem join_left_ok {N : Nat} {oa ob o : Out} (h : joinO N oa ob = some o) :
    ∀ L, oa = some L → o = some L := by
  intro L hL
  subst hL
  cases ob with
  | none =>
    simp only [joinO] at h
    cases h
    rfl
  | some b =>
    simp only [joinO] at h
    split at h
    · cases h
      rfl
    · contradiction

theorem join_right_ok {N : Nat} {oa ob o : Out} (h : joinO N oa ob = some o)
    (ha : BoundedO N oa) (hb : BoundedO N ob) : ∀ L, ob = some L → o = some L := by
  intro L hL
  subst hL
  cases oa with
  | none =>
    simp only [joinO] at h
    cases h
    rfl
  | some a =>
    simp only [joinO] at h
    split at h
    · rename_i heq
      cases h
      rw [eqN_sound heq (ha a rfl) (hb L rfl)]
    · contradiction

theorem goodR_of {o o' : Out} {E : List Var} {r : Res} (hok : ∀ L, o = some L → o' = some L) :
    GoodR o E r → GoodR o' E r := by
  cases r with
  | ok s cs =>
    intro g
    simp only [GoodR] at g ⊢
    obtain ⟨L, hL, hinv⟩ := g
    exact ⟨L, hok L hL, hinv⟩
  | exn s cs => intro g; exact g
  | err => intro g; exact g
  | oof => intro g; exact g

theorem bounded_check (N : Nat) (p : Q) : ∀ {E : List Var} {Λ : LEnv} {o : Out},
    check N E p Λ = some o → Bounded N Λ → BoundedO N o := by
  induction p with
  | skip =>
    intro E Λ o hc hb
    simp only [check] at hc
    cases hc
    intro L hL
    cases hL
    exact hb
  | stmt t =>
    intro E Λ o hc hb
    simp only [check] at hc
    split at hc
    · rename_i hv
      split at hc
      · rename_i Λ₁ h₁
        cases hc
        intro L hL
        cases hL
        exact bounded_checkS hv h₁ hb
      · contradiction
    · contradiction
  | seq p q ihp ihq =>
    intro E Λ o hc hb
    simp only [check] at hc
    split at hc
    · rename_i Λ₁ h₁
      exact ihq hc (ihp h₁ hb Λ₁ rfl)
    · cases hc
      intro L hL
      cases hL
    · contradiction
  | branch p q ihp ihq =>
    intro E Λ o hc hb
    simp only [check] at hc
    split at hc
    · rename_i oa ob hpa hpb
      exact joinO_bounded hc (ihp hpa hb) (ihq hpb hb)
    · contradiction
  | loop b ih =>
    intro E Λ o hc hb
    simp only [check] at hc
    split at hc
    · split at hc
      · cases hc
        intro L hL
        cases hL
        exact hb
      · contradiction
    · cases hc
      intro L hL
      cases hL
      exact hb
    · contradiction
  | fail =>
    intro E Λ o hc hb
    simp only [check] at hc
    split at hc
    · cases hc
      intro L hL
      cases hL
    · contradiction
  | guard x p ih =>
    intro E Λ o hc hb
    simp only [check] at hc
    split at hc
    · exact ih hc hb
    · contradiction

/-! ## 主引理 -/

theorem sound (N : Nat) (n : Nat) :
    ∀ (p : Q) {E : List Var} {Λ : LEnv} {o : Out} {s : St} (cs : List Bool),
      check N E p Λ = some o → Bounded N Λ → (∀ y ∈ E, y < N) → LInv Λ s →
      GoodR o E (exec n p s cs) := by
  induction n with
  | zero =>
    intro p E Λ o s cs _ _ _ _
    simp [exec, GoodR]
  | succ n ih =>
    intro p E Λ o s cs hc hb hE h
    have hc0 := hc
    cases p with
    | skip =>
      simp only [check] at hc
      cases hc
      simp only [exec, GoodR]
      exact ⟨Λ, rfl, h⟩
    | stmt t =>
      simp only [check] at hc
      split at hc
      · split at hc
        · rename_i Λ₁ h₁
          cases hc
          obtain ⟨s', he, h'⟩ := stepS h₁ h
          simp only [exec, he, GoodR]
          exact ⟨Λ₁, rfl, h'⟩
        · contradiction
      · contradiction
    | seq p q =>
      simp only [check] at hc
      split at hc
      · rename_i Λ₁ h₁
        have g₁ := ih p cs h₁ hb hE h
        have hb₁ := bounded_check N p h₁ hb Λ₁ rfl
        cases he₁ : exec n p s cs with
        | ok s₁ cs₁ =>
          rw [he₁] at g₁
          simp only [GoodR] at g₁
          obtain ⟨L, hL, hinv⟩ := g₁
          cases hL
          simp only [exec, he₁]
          exact ih q cs₁ hc hb₁ hE hinv
        | exn s₁ cs₁ =>
          rw [he₁] at g₁
          simp only [exec, he₁]
          simp only [GoodR] at g₁ ⊢
          exact g₁
        | err => rw [he₁] at g₁; simp [GoodR] at g₁
        | oof => simp only [exec, he₁, GoodR]
      · rename_i h₁
        cases hc
        have g₁ := ih p cs h₁ hb hE h
        cases he₁ : exec n p s cs with
        | ok s₁ cs₁ => rw [he₁] at g₁; simp [GoodR] at g₁
        | exn s₁ cs₁ =>
          rw [he₁] at g₁
          simp only [exec, he₁]
          simp only [GoodR] at g₁ ⊢
          exact g₁
        | err => rw [he₁] at g₁; simp [GoodR] at g₁
        | oof => simp only [exec, he₁, GoodR]
      · contradiction
    | branch p q =>
      simp only [check] at hc
      split at hc
      · rename_i oa ob hpa hpb
        have hba := bounded_check N p hpa hb
        have hbb := bounded_check N q hpb hb
        by_cases hcs : cs.headD false = true
        · simp only [exec, hcs, ite_true]
          exact goodR_of (join_left_ok hc) (ih p cs.tail hpa hb hE h)
        · simp only [exec, hcs]
          simp only [ite_false, Bool.false_eq_true] at *
          exact goodR_of (join_right_ok hc hba hbb) (ih q cs.tail hpb hb hE h)
      · contradiction
    | loop b =>
      -- 两种情况（循环体正常结束、或循环体不会正常结束）下，循环的检查结果都是 `some Λ`
      have key : ∀ {Λ₁ : Out}, check N E b Λ = some Λ₁ → (∀ L, Λ₁ = some L → L = Λ) →
          o = some Λ → GoodR o E (exec (n + 1) (.loop b) s cs) := by
        intro Λ₁ h₁ hL ho
        subst ho
        by_cases hcs : cs.headD false = true
        · have g := ih b cs.tail h₁ hb hE h
          cases he : exec n b s cs.tail with
          | ok s₁ cs₁ =>
            rw [he] at g
            simp only [GoodR] at g
            obtain ⟨L, hL1, hinv⟩ := g
            rw [hL L hL1] at hinv
            simp only [exec, hcs, ite_true, he]
            exact ih (.loop b) cs₁ hc0 hb hE hinv
          | exn s₁ cs₁ =>
            rw [he] at g
            simp only [exec, hcs, ite_true, he]
            simp only [GoodR] at g ⊢
            exact g
          | err => rw [he] at g; simp [GoodR] at g
          | oof => simp only [exec, hcs, ite_true, he, GoodR]
        · simp only [exec, hcs]
          simp only [ite_false, Bool.false_eq_true] at *
          simp only [GoodR]
          exact ⟨Λ, rfl, h⟩
      simp only [check] at hc
      split at hc
      · rename_i Λ₁ h₁
        split at hc
        · rename_i heq
          cases hc
          have h1 : Λ₁ = Λ := eqN_sound heq (bounded_check N b h₁ hb Λ₁ rfl) hb
          exact key h₁ (fun L hL => by cases hL; exact h1) rfl
        · contradiction
      · rename_i h₁
        cases hc
        exact key h₁ (fun L hL => by cases hL) rfl
      · contradiction
    | fail =>
      simp only [check] at hc
      split at hc
      · rename_i hcov
        cases hc
        simp only [exec, GoodR]
        exact ⟨Λ, h, covers_sound hcov hb hE⟩
      · contradiction
    | guard x p =>
      simp only [check] at hc
      split at hc
      · rename_i hcond
        obtain ⟨_, hxE, hxN⟩ := hcond
        have hE' : ∀ y ∈ x :: E, y < N := by
          intro y hy
          rcases List.mem_cons.mp hy with hyx | hy'
          · rw [hyx]; exact hxN
          · exact hE y hy'
        have g := ih p cs hc hb hE' h
        cases he : exec n p s cs with
        | ok s₁ cs₁ =>
          rw [he] at g
          simp only [exec, he]
          simp only [GoodR] at g ⊢
          exact g
        | exn s₁ cs₁ =>
          rw [he] at g
          simp only [GoodR] at g
          obtain ⟨L, hL, hiff⟩ := g
          have hLx : L x = true := (hiff x).mpr (by simp)
          obtain ⟨l, hl, hlv⟩ := hL.owned x hLx
          simp only [exec, he, execS, hl, hlv, ite_true, GoodR]
          refine ⟨upd L x false, consume_ok hL hLx hl, ?_⟩
          intro z
          by_cases hzx : z = x
          · rw [hzx, upd_same]
            simp [hxE]
          · rw [upd_other L false hzx, hiff z]
            simp [hzx]
        | err => rw [he] at g; simp [GoodR] at g
        | oof => simp only [exec, he, GoodR]
      · contradiction

/-! ## 主定理 -/

theorem no_live_ok {s : St} {L : LEnv} (hinv : LInv L s) (hoff : ∀ x, L x = false) :
    ∀ l, s.live l = false := by
  intro l
  cases hl : s.live l with
  | false => rfl
  | true =>
    obtain ⟨x, hx, _⟩ := hinv.only l hl
    rw [hoff x] at hx
    cases hx

theorem no_live_exn {s : St} {L : LEnv} (hinv : LInv L s)
    (hiff : ∀ x, L x = true ↔ x ∈ ([] : List Var)) : ∀ l, s.live l = false := by
  intro l
  cases hl : s.live l with
  | false => rfl
  | true =>
    obtain ⟨x, hx, _⟩ := hinv.only l hl
    exact absurd ((hiff x).mp hx) (by simp)

/-- **M6（二）主定理。** 被接受的程序执行不出错（`errdefer` 不会重复消费）；
无论正常结束还是出错退出，结束时都没有未消费的线性值。 -/
theorem safety_and_no_leak (N : Nat) (p : Q) (h : accepts N p = true)
    (fuel : Nat) (cs : List Bool) :
    exec fuel p St.empty cs ≠ .err ∧
    (∀ s cs', exec fuel p St.empty cs = .ok s cs' → ∀ l, s.live l = false) ∧
    (∀ s cs', exec fuel p St.empty cs = .exn s cs' → ∀ l, s.live l = false) := by
  unfold accepts at h
  have hE0 : ∀ y ∈ ([] : List Var), y < N := fun _ hy => by cases hy
  split at h
  · rename_i L hc
    have hb' := bounded_check N p hc (fun _ _ => rfl) L rfl
    have hoff : ∀ x, L x = false := by
      intro x
      by_cases hx : x < N
      · have := List.all_eq_true.mp h x (List.mem_range.mpr hx)
        simpa using this
      · exact hb' x (Nat.le_of_not_lt hx)
    have g := sound N fuel p cs hc (fun _ _ => rfl) hE0 linv_empty
    refine ⟨?_, ?_, ?_⟩
    · intro he
      rw [he] at g
      simp [GoodR] at g
    · intro s cs' he
      rw [he] at g
      simp only [GoodR] at g
      obtain ⟨L', hL', hinv⟩ := g
      cases hL'
      exact no_live_ok hinv hoff
    · intro s cs' he
      rw [he] at g
      simp only [GoodR] at g
      obtain ⟨L', hinv, hiff⟩ := g
      exact no_live_exn hinv hiff
  · rename_i hc
    have g := sound N fuel p cs hc (fun _ _ => rfl) hE0 linv_empty
    refine ⟨?_, ?_, ?_⟩
    · intro he
      rw [he] at g
      simp [GoodR] at g
    · intro s cs' he
      rw [he] at g
      simp [GoodR] at g
    · intro s cs' he
      rw [he] at g
      simp only [GoodR] at g
      obtain ⟨L', hinv, hiff⟩ := g
      exact no_live_exn hinv hiff
  · contradiction

/-! ## 例子 -/

/-- 结束时（正常或出错）变量 0 的线性值是否已被消费；内存错误或燃料耗尽算作否。 -/
def clean (r : Res) : Bool :=
  match r with
  | .ok s _  => !s.live 0
  | .exn s _ => !s.live 0
  | _        => false

def isErr : Res → Bool
  | .err => true
  | _    => false

/-- `let x = new(); errdefer consume x; if bad { fail }; consume x`：接受，两条路径都干净。 -/
def pattern : Q := .seq (.stmt (.lnew 0))
  (.seq (.guard 0 (.branch .fail .skip)) (.stmt (.consume 0)))
example : accepts 1 pattern = true := rfl
example : clean (exec 20 pattern Core.M6.St.empty [true]) = true := rfl
example : clean (exec 20 pattern Core.M6.St.empty [false]) = true := rfl

/-- 去掉 `errdefer`：拒绝；不经检查走出错路径，`x` 被遗漏。 -/
def noGuard : Q := .seq (.stmt (.lnew 0))
  (.seq (.branch .fail .skip) (.stmt (.consume 0)))
example : accepts 1 noGuard = false := rfl
example : clean (exec 20 noGuard Core.M6.St.empty [true]) = false := rfl

/-- 在 `errdefer` 范围内先手动消费再出错：拒绝；不经检查执行，`errdefer` 重复消费，出错。 -/
def doubleClean : Q := .seq (.stmt (.lnew 0)) (.guard 0 (.seq (.stmt (.consume 0)) .fail))
example : accepts 1 doubleClean = false := rfl
example : isErr (exec 20 doubleClean Core.M6.St.empty []) = true := rfl

end Core.M6e
