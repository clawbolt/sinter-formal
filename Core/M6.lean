import Core.Basic

/-!
# M6（一）：`linear` 值

`linear` 值不能被隐式丢弃：作用域结束时不会自动释放，必须显式 `consume`，并且只能消费一次。

**命令**：`lnew x` 创建线性值；`consume x` 消费它；`lmove x y` 把它移到 `y`。

**静态检查**：每个变量要么持有一个未消费的线性值（`true`），要么没有（`false`）。
没有 drop flag 那样的“可能已移走”：
- 分支汇合时，两边的状态必须完全一致（`Join.strict`）；
- 循环体结束时的状态必须和进入时一致，也就是循环体不能消费循环之外的线性值；
- 程序结束时，所有变量都不能再持有线性值（`accepts`）。

**动态语义**：用燃料保证终止（和 M2L 相同）。`consume` 一个已经消费过的值就出错。

**主定理** `safety_and_no_leak`：检查器接受的程序，无论燃料多少、分支怎么走、循环跑几轮，
执行都不会出错（没有重复消费）；正常结束时，所有创建过的线性值都已被消费（没有遗漏）。
两条合起来就是“每个线性值恰好被消费一次”。

**反例**：如果分支汇合时只看一边（`Join.left`），一边消费、另一边不消费的程序会被接受，
走另一边时线性值被遗漏。见文件末尾的 `halfConsumed`。

线性值不能移进区域（D4 的 `linear` 部分）：移进区域就等于再也不会被消费，
反例和 M5（三）的 `leak` 完全相同，这里不再重复。
-/

namespace Core.M6

inductive Stmt
  | lnew    (x : Var)
  | consume (x : Var)
  | lmove   (x y : Var)

inductive P
  | skip
  | stmt   (t : Stmt)
  | seq    (p q : P)
  | branch (p q : P)
  | loop   (b : P)

inductive Join | strict | left

abbrev LEnv := Var → Bool

/-! ## 静态检查 -/

def varsOk (N : Nat) : Stmt → Bool
  | .lnew x    => decide (x < N)
  | .consume x => decide (x < N)
  | .lmove x y => decide (x < N) && decide (y < N)

def checkS (Λ : LEnv) : Stmt → Option LEnv
  | .lnew x    => if Λ x = false then some (upd Λ x true) else none
  | .consume x => if Λ x = true then some (upd Λ x false) else none
  | .lmove x y =>
    if x ≠ y ∧ Λ x = true ∧ Λ y = false then some (upd (upd Λ x false) y true) else none

/-- 在前 `N` 个变量上比较两个状态。 -/
def eqN (N : Nat) (a b : LEnv) : Bool := (List.range N).all (fun x => a x == b x)

def check (j : Join) (N : Nat) : P → LEnv → Option LEnv
  | .skip,       Λ => some Λ
  | .stmt t,     Λ => if varsOk N t = true then checkS Λ t else none
  | .seq p q,    Λ =>
    match check j N p Λ with
    | some Λ₁ => check j N q Λ₁
    | none    => none
  | .branch p q, Λ =>
    match check j N p Λ, check j N q Λ with
    | some Λa, some Λb =>
      match j with
      | .strict => if eqN N Λa Λb = true then some Λa else none
      | .left   => some Λa
    | _, _ => none
  | .loop b,     Λ =>
    match check j N b Λ with
    | some Λ₁ => if eqN N Λ₁ Λ = true then some Λ else none
    | none    => none

def allOff (N : Nat) (Λ : LEnv) : Bool := (List.range N).all (fun x => !Λ x)

/-- 程序被接受：检查通过，并且结束时没有未消费的线性值。 -/
def accepts (j : Join) (N : Nat) (p : P) : Bool :=
  match check j N p (fun _ => false) with
  | some Λ' => allOff N Λ'
  | none    => false

/-! ## 动态语义 -/

structure St where
  ptr  : Var → Option Nat
  live : Nat → Bool       -- 线性值是否还未被消费
  next : Nat

def St.empty : St := ⟨fun _ => none, fun _ => false, 0⟩

def execS (s : St) : Stmt → Option St
  | .lnew x => some ⟨upd s.ptr x (some s.next), upd s.live s.next true, s.next + 1⟩
  | .consume x =>
    match s.ptr x with
    | some l => if s.live l = true then some { s with live := upd s.live l false } else none
    | none   => none
  | .lmove x y => some { s with ptr := upd s.ptr y (s.ptr x) }

inductive Res
  | ok  (s : St) (cs : List Bool)
  | err
  | oof

def exec : Nat → P → St → List Bool → Res
  | 0,     _,            _, _  => .oof
  | _ + 1, .skip,        s, cs => .ok s cs
  | _ + 1, .stmt t,      s, cs =>
    match execS s t with
    | some s' => .ok s' cs
    | none    => .err
  | n + 1, .seq p q,     s, cs =>
    match exec n p s cs with
    | .ok s₁ cs₁ => exec n q s₁ cs₁
    | .err       => .err
    | .oof       => .oof
  | n + 1, .branch p q,  s, cs =>
    if cs.headD false = true then exec n p s cs.tail else exec n q s cs.tail
  | n + 1, .loop b,      s, cs =>
    if cs.headD false = true then
      match exec n b s cs.tail with
      | .ok s₁ cs₁ => exec n (.loop b) s₁ cs₁
      | .err       => .err
      | .oof       => .oof
    else .ok s cs.tail

/-! ## 不变式 -/

structure LInv (Λ : LEnv) (s : St) : Prop where
  owned : ∀ x, Λ x = true → ∃ l, s.ptr x = some l ∧ s.live l = true
  uniq  : ∀ x y l, Λ x = true → Λ y = true → s.ptr x = some l → s.ptr y = some l → x = y
  fresh : ∀ x l, s.ptr x = some l → l < s.next
  only  : ∀ l, s.live l = true → ∃ x, Λ x = true ∧ s.ptr x = some l

def Bounded (N : Nat) (Λ : LEnv) : Prop := ∀ x, N ≤ x → Λ x = false

def GoodR (Λ : LEnv) : Res → Prop
  | .ok s _ => LInv Λ s
  | .err    => False
  | .oof    => True

theorem off_true {Λ : LEnv} {x a : Var} (h : upd Λ x false a = true) : Λ a = true ∧ a ≠ x := by
  by_cases hax : a = x
  · rw [hax, upd_same] at h
    cases h
  · rw [upd_other Λ false hax] at h
    exact ⟨h, hax⟩

theorem eqN_sound {N : Nat} {a b : LEnv} (h : eqN N a b = true)
    (ha : Bounded N a) (hb : Bounded N b) : a = b := by
  funext x
  by_cases hx : x < N
  · have := List.all_eq_true.mp h x (List.mem_range.mpr hx)
    simpa using this
  · have hx' : N ≤ x := Nat.le_of_not_lt hx
    rw [ha x hx', hb x hx']

/-! ## 三条命令保持不变式 -/

theorem lnew_ok {Λ : LEnv} {s : St} {x : Var} (h : LInv Λ s) (hx : Λ x = false) :
    LInv (upd Λ x true) ⟨upd s.ptr x (some s.next), upd s.live s.next true, s.next + 1⟩ := by
  constructor
  · intro y hy
    change upd Λ x true y = true at hy
    by_cases hyx : y = x
    · refine ⟨s.next, ?_, ?_⟩
      · show upd s.ptr x (some s.next) y = some s.next
        rw [hyx, upd_same]
      · show upd s.live s.next true s.next = true
        rw [upd_same]
    · rw [upd_other Λ true hyx] at hy
      obtain ⟨l, hl, hlv⟩ := h.owned y hy
      have hln : l ≠ s.next := Nat.ne_of_lt (h.fresh y l hl)
      refine ⟨l, ?_, ?_⟩
      · show upd s.ptr x (some s.next) y = some l
        rw [upd_other s.ptr (some s.next) hyx]
        exact hl
      · show upd s.live s.next true l = true
        rw [upd_other s.live true hln]
        exact hlv
  · intro a b l ha hb hpa hpb
    change upd Λ x true a = true at ha
    change upd Λ x true b = true at hb
    change upd s.ptr x (some s.next) a = some l at hpa
    change upd s.ptr x (some s.next) b = some l at hpb
    by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · exfalso
      rw [hax, upd_same] at hpa
      rw [upd_other s.ptr (some s.next) hbx] at hpb
      cases hpa
      exact Nat.lt_irrefl _ (h.fresh b _ hpb)
    · exfalso
      rw [hbx, upd_same] at hpb
      rw [upd_other s.ptr (some s.next) hax] at hpa
      cases hpb
      exact Nat.lt_irrefl _ (h.fresh a _ hpa)
    · rw [upd_other Λ true hax] at ha
      rw [upd_other Λ true hbx] at hb
      rw [upd_other s.ptr (some s.next) hax] at hpa
      rw [upd_other s.ptr (some s.next) hbx] at hpb
      exact h.uniq a b l ha hb hpa hpb
  · intro y l hp
    change upd s.ptr x (some s.next) y = some l at hp
    show l < s.next + 1
    by_cases hyx : y = x
    · rw [hyx, upd_same] at hp
      cases hp
      exact Nat.lt_succ_self _
    · rw [upd_other s.ptr (some s.next) hyx] at hp
      exact Nat.lt_succ_of_lt (h.fresh y l hp)
  · intro l hl
    change upd s.live s.next true l = true at hl
    by_cases hln : l = s.next
    · refine ⟨x, ?_, ?_⟩
      · show upd Λ x true x = true
        rw [upd_same]
      · show upd s.ptr x (some s.next) x = some l
        rw [upd_same, hln]
    · rw [upd_other s.live true hln] at hl
      obtain ⟨y, hy, hp⟩ := h.only l hl
      have hyx : y ≠ x := by
        intro he
        rw [he, hx] at hy
        cases hy
      refine ⟨y, ?_, ?_⟩
      · show upd Λ x true y = true
        rw [upd_other Λ true hyx]
        exact hy
      · show upd s.ptr x (some s.next) y = some l
        rw [upd_other s.ptr (some s.next) hyx]
        exact hp

theorem consume_ok {Λ : LEnv} {s : St} {x : Var} {l : Nat} (h : LInv Λ s)
    (hx : Λ x = true) (hl : s.ptr x = some l) :
    LInv (upd Λ x false) { s with live := upd s.live l false } := by
  constructor
  · intro y hy
    obtain ⟨hy', hyx⟩ := off_true hy
    obtain ⟨l', hl', hlv⟩ := h.owned y hy'
    have hne : l' ≠ l := by
      intro he
      rw [he] at hl'
      exact hyx (h.uniq y x l hy' hx hl' hl)
    refine ⟨l', hl', ?_⟩
    show upd s.live l false l' = true
    rw [upd_other s.live false hne]
    exact hlv
  · intro a b l' ha hb hpa hpb
    exact h.uniq a b l' (off_true ha).1 (off_true hb).1 hpa hpb
  · intro y l' hp
    exact h.fresh y l' hp
  · intro l' hl'
    change upd s.live l false l' = true at hl'
    by_cases hll : l' = l
    · rw [hll, upd_same] at hl'
      cases hl'
    · rw [upd_other s.live false hll] at hl'
      obtain ⟨y, hy, hp⟩ := h.only l' hl'
      have hyx : y ≠ x := by
        intro he
        rw [he, hl] at hp
        cases hp
        exact hll rfl
      refine ⟨y, ?_, hp⟩
      show upd Λ x false y = true
      rw [upd_other Λ false hyx]
      exact hy

theorem lmove_ok {Λ : LEnv} {s : St} {x y : Var} (h : LInv Λ s)
    (_hxy : x ≠ y) (hx : Λ x = true) (hy : Λ y = false) :
    LInv (upd (upd Λ x false) y true) { s with ptr := upd s.ptr y (s.ptr x) } := by
  have own : ∀ z, upd (upd Λ x false) y true z = true → z = y ∨ (z ≠ y ∧ z ≠ x ∧ Λ z = true) := by
    intro z hz
    by_cases hzy : z = y
    · exact Or.inl hzy
    · rw [upd_other (upd Λ x false) true hzy] at hz
      obtain ⟨h1, h2⟩ := off_true hz
      exact Or.inr ⟨hzy, h2, h1⟩
  constructor
  · intro z hz
    rcases own z hz with hzy | ⟨hzy, _, hz'⟩
    · obtain ⟨l, hl, hlv⟩ := h.owned x hx
      refine ⟨l, ?_, hlv⟩
      show upd s.ptr y (s.ptr x) z = some l
      rw [hzy, upd_same]
      exact hl
    · obtain ⟨l, hl, hlv⟩ := h.owned z hz'
      refine ⟨l, ?_, hlv⟩
      show upd s.ptr y (s.ptr x) z = some l
      rw [upd_other s.ptr (s.ptr x) hzy]
      exact hl
  · intro a b l ha hb hpa hpb
    change upd s.ptr y (s.ptr x) a = some l at hpa
    change upd s.ptr y (s.ptr x) b = some l at hpb
    rcases own a ha with hay | ⟨hay, hax, ha'⟩ <;> rcases own b hb with hby | ⟨hby, hbx, hb'⟩
    · rw [hay, hby]
    · exfalso
      rw [hay, upd_same] at hpa
      rw [upd_other s.ptr (s.ptr x) hby] at hpb
      exact hbx (h.uniq b x l hb' hx hpb hpa)
    · exfalso
      rw [hby, upd_same] at hpb
      rw [upd_other s.ptr (s.ptr x) hay] at hpa
      exact hax (h.uniq a x l ha' hx hpa hpb)
    · rw [upd_other s.ptr (s.ptr x) hay] at hpa
      rw [upd_other s.ptr (s.ptr x) hby] at hpb
      exact h.uniq a b l ha' hb' hpa hpb
  · intro z l hp
    change upd s.ptr y (s.ptr x) z = some l at hp
    by_cases hzy : z = y
    · rw [hzy, upd_same] at hp
      exact h.fresh x l hp
    · rw [upd_other s.ptr (s.ptr x) hzy] at hp
      exact h.fresh z l hp
  · intro l hl
    obtain ⟨z, hz, hp⟩ := h.only l hl
    by_cases hzx : z = x
    · refine ⟨y, ?_, ?_⟩
      · show upd (upd Λ x false) y true y = true
        rw [upd_same]
      · show upd s.ptr y (s.ptr x) y = some l
        rw [upd_same, ← hzx]
        exact hp
    · have hzy : z ≠ y := by
        intro he
        rw [he, hy] at hz
        cases hz
      refine ⟨z, ?_, ?_⟩
      · show upd (upd Λ x false) y true z = true
        rw [upd_other (upd Λ x false) true hzy, upd_other Λ false hzx]
        exact hz
      · show upd s.ptr y (s.ptr x) z = some l
        rw [upd_other s.ptr (s.ptr x) hzy]
        exact hp

/-! ## 单步 -/

theorem bounded_checkS {N : Nat} {Λ Λ' : LEnv} {t : Stmt}
    (hv : varsOk N t = true) (hc : checkS Λ t = some Λ') (hb : Bounded N Λ) : Bounded N Λ' := by
  cases t with
  | lnew x =>
    simp only [checkS] at hc
    split at hc
    · cases hc
      simp only [varsOk, decide_eq_true_eq] at hv
      intro z hz
      have hzx : z ≠ x := by
        intro he
        rw [he] at hz
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hv hz)
      rw [upd_other Λ true hzx]
      exact hb z hz
    · contradiction
  | consume x =>
    simp only [checkS] at hc
    split at hc
    · cases hc
      intro z hz
      by_cases hzx : z = x
      · rw [hzx, upd_same]
      · rw [upd_other Λ false hzx]
        exact hb z hz
    · contradiction
  | lmove x y =>
    simp only [checkS] at hc
    split at hc
    · cases hc
      simp only [varsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
      intro z hz
      have hzy : z ≠ y := by
        intro he
        rw [he] at hz
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hv.2 hz)
      rw [upd_other (upd Λ x false) true hzy]
      by_cases hzx : z = x
      · rw [hzx, upd_same]
      · rw [upd_other Λ false hzx]
        exact hb z hz
    · contradiction

theorem stepS {Λ Λ' : LEnv} {s : St} {t : Stmt}
    (hc : checkS Λ t = some Λ') (h : LInv Λ s) :
    ∃ s', execS s t = some s' ∧ LInv Λ' s' := by
  cases t with
  | lnew x =>
    simp only [checkS] at hc
    split at hc
    · rename_i hx
      cases hc
      exact ⟨_, rfl, lnew_ok h hx⟩
    · contradiction
  | consume x =>
    simp only [checkS] at hc
    split at hc
    · rename_i hx
      cases hc
      obtain ⟨l, hl, hlv⟩ := h.owned x hx
      exact ⟨{ s with live := upd s.live l false }, by simp [execS, hl, hlv], consume_ok h hx hl⟩
    · contradiction
  | lmove x y =>
    simp only [checkS] at hc
    split at hc
    · rename_i hcond
      obtain ⟨hxy, hx, hy⟩ := hcond
      cases hc
      exact ⟨_, rfl, lmove_ok h hxy hx hy⟩
    · contradiction

theorem bounded_check (N : Nat) (p : P) :
    ∀ {Λ Λ' : LEnv}, check .strict N p Λ = some Λ' → Bounded N Λ → Bounded N Λ' := by
  induction p with
  | skip =>
    intro Λ Λ' hc hb
    simp only [check] at hc
    cases hc
    exact hb
  | stmt t =>
    intro Λ Λ' hc hb
    simp only [check] at hc
    split at hc
    · rename_i hv
      exact bounded_checkS hv hc hb
    · contradiction
  | seq p q ihp ihq =>
    intro Λ Λ' hc hb
    simp only [check] at hc
    split at hc
    · rename_i Λ₁ h₁
      exact ihq hc (ihp h₁ hb)
    · contradiction
  | branch p q ihp ihq =>
    intro Λ Λ' hc hb
    simp only [check] at hc
    split at hc
    · rename_i Λa Λb hpa hpb
      split at hc
      · cases hc
        exact ihp hpa hb
      · contradiction
    · contradiction
  | loop b ih =>
    intro Λ Λ' hc hb
    simp only [check] at hc
    split at hc
    · split at hc
      · cases hc
        exact hb
      · contradiction
    · contradiction

/-! ## 主引理 -/

theorem sound (N : Nat) (n : Nat) :
    ∀ (p : P) {Λ Λ' : LEnv} {s : St} (cs : List Bool),
      check .strict N p Λ = some Λ' → Bounded N Λ → LInv Λ s →
      GoodR Λ' (exec n p s cs) := by
  induction n with
  | zero =>
    intro p Λ Λ' s cs _ _ _
    simp [exec, GoodR]
  | succ n ih =>
    intro p Λ Λ' s cs hc hb h
    have hc0 := hc
    cases p with
    | skip =>
      simp only [check] at hc
      cases hc
      simp only [exec, GoodR]
      exact h
    | stmt t =>
      simp only [check] at hc
      split at hc
      · obtain ⟨s', he, h'⟩ := stepS hc h
        simp only [exec, he, GoodR]
        exact h'
      · contradiction
    | seq p q =>
      simp only [check] at hc
      split at hc
      · rename_i Λ₁ h₁
        have hb₁ := bounded_check N p h₁ hb
        have g₁ := ih p cs h₁ hb h
        cases he₁ : exec n p s cs with
        | ok s₁ cs₁ =>
          rw [he₁] at g₁
          simp only [GoodR] at g₁
          simp only [exec, he₁]
          exact ih q cs₁ hc hb₁ g₁
        | err => rw [he₁] at g₁; simp [GoodR] at g₁
        | oof => simp only [exec, he₁, GoodR]
      · contradiction
    | branch p q =>
      simp only [check] at hc
      split at hc
      · rename_i Λa Λb hpa hpb
        split at hc
        · rename_i heq
          cases hc
          have hab := eqN_sound heq (bounded_check N p hpa hb) (bounded_check N q hpb hb)
          by_cases hcs : cs.headD false = true
          · simp only [exec, hcs, ite_true]
            exact ih p cs.tail hpa hb h
          · simp only [exec, hcs]
            simp only [ite_false, Bool.false_eq_true] at *
            have g := ih q cs.tail hpb hb h
            rw [← hab] at g
            exact g
        · contradiction
      · contradiction
    | loop b =>
      simp only [check] at hc
      split at hc
      · rename_i Λ₁ h₁
        split at hc
        · rename_i heq
          cases hc
          have h1 : Λ₁ = Λ := eqN_sound heq (bounded_check N b h₁ hb) hb
          by_cases hcs : cs.headD false = true
          · have g := ih b cs.tail h₁ hb h
            cases he : exec n b s cs.tail with
            | ok s₁ cs₁ =>
              rw [he] at g
              simp only [GoodR] at g
              rw [h1] at g
              simp only [exec, hcs, ite_true, he]
              exact ih (.loop b) cs₁ hc0 hb g
            | err => rw [he] at g; simp [GoodR] at g
            | oof => simp only [exec, hcs, ite_true, he, GoodR]
          · simp only [exec, hcs]
            simp only [ite_false, Bool.false_eq_true] at *
            simp only [GoodR]
            exact h
        · contradiction
      · contradiction

/-! ## 主定理 -/

theorem linv_empty : LInv (fun _ => false) St.empty :=
  ⟨(fun _ h => by simp at h), (fun _ _ _ h => by simp at h), (fun _ _ h => by simp [St.empty] at h),
   (fun _ h => by simp [St.empty] at h)⟩

/-- **M6（一）主定理。** 被接受的程序，无论燃料多少、分支怎么走、循环跑几轮，
执行都不会出错（没有重复消费）；正常结束时没有未消费的线性值（没有遗漏）。 -/
theorem safety_and_no_leak (N : Nat) (p : P) (h : accepts .strict N p = true)
    (fuel : Nat) (cs : List Bool) :
    exec fuel p St.empty cs ≠ .err ∧
    ∀ s cs', exec fuel p St.empty cs = .ok s cs' → ∀ l, s.live l = false := by
  unfold accepts at h
  split at h
  · rename_i Λ' hc
    have hb' := bounded_check N p hc (fun _ _ => rfl)
    have hoff : ∀ x, Λ' x = false := by
      intro x
      by_cases hx : x < N
      · have := List.all_eq_true.mp h x (List.mem_range.mpr hx)
        simpa using this
      · exact hb' x (Nat.le_of_not_lt hx)
    have g := sound N fuel p cs hc (fun _ _ => rfl) linv_empty
    constructor
    · intro he
      rw [he] at g
      simp [GoodR] at g
    · intro s cs' he l
      rw [he] at g
      simp only [GoodR] at g
      cases hl : s.live l with
      | false => rfl
      | true =>
        obtain ⟨x, hx, _⟩ := g.only l hl
        rw [hoff x] at hx
        cases hx
  · contradiction

/-! ## 例子 -/

def isErr : Res → Bool
  | .err => true
  | _    => false

def leaked (r : Res) (l : Nat) : Bool :=
  match r with
  | .ok s _ => s.live l
  | _       => false

/-- 两个分支都消费了线性值（一边直接消费，一边移走后消费）：接受。 -/
def ok1 : P := .seq (.stmt (.lnew 0))
  (.branch (.stmt (.consume 0)) (.seq (.stmt (.lmove 0 1)) (.stmt (.consume 1))))
example : accepts .strict 2 ok1 = true := rfl

/-- 每轮创建并消费一个线性值：接受，跑三轮不出错。 -/
def loopOk : P := .loop (.seq (.stmt (.lnew 0)) (.stmt (.consume 0)))
example : accepts .strict 1 loopOk = true := rfl
example : isErr (exec 10 loopOk St.empty [true, true, true, false]) = false := rfl

/-- 忘了消费：拒绝。 -/
def forgot : P := .stmt (.lnew 0)
example : accepts .strict 1 forgot = false := rfl

/-- 消费两次：拒绝；不经检查执行，出错。 -/
def twice : P := .seq (.stmt (.lnew 0)) (.seq (.stmt (.consume 0)) (.stmt (.consume 0)))
example : accepts .strict 1 twice = false := rfl
example : isErr (exec 10 twice St.empty []) = true := rfl

/-- 循环体消费循环之外的线性值：拒绝；不经检查跑两轮，第二轮重复消费，出错。 -/
def loopBad : P := .seq (.stmt (.lnew 0)) (.loop (.stmt (.consume 0)))
example : accepts .strict 1 loopBad = false := rfl
example : isErr (exec 10 loopBad St.empty [true, true, false]) = true := rfl

/-- 反例：一个分支消费，另一个分支不消费。 -/
def halfConsumed : P := .seq (.stmt (.lnew 0)) (.branch (.stmt (.consume 0)) .skip)
/-- 汇合时只看一边，检查器接受…… -/
example : accepts .left 1 halfConsumed = true := rfl
/-- ……但走另一边时，线性值没有被消费。 -/
example : leaked (exec 10 halfConsumed St.empty [false]) 0 = true := rfl
/-- 严格汇合拒绝它。 -/
example : accepts .strict 1 halfConsumed = false := rfl

end Core.M6
