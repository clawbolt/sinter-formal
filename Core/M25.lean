import Core.M10

/-!
# M25：泛型 impl 的查找

C56 允许 `impl<T: ToStr> ToStr for Vec<T> { … }`。于是“类型 `t` 实现了 trait `tr` 吗”不再是查表，
而是递归的查找：找到头部能匹配 `t` 的 impl，再对匹配出的类型实参逐个查它们的约束。
泛型函数里，类型参数 `T` 的约束 `T: tr` 是已知的假设 `A`。

编译器对每个 impl 要求（`WF`）：头部不是单独的类型参数（不能 `impl<T> Tr for T`）；约束只写在出现在头部的类型参数上。
对同一个 trait 的任意两个 impl 要求头部不相容（`Coherent`，`compat` 是保守的语法检查：没有类型同时是两者的实例）。

类型是一阶的项：类型参数 `var`、类型名 `con`、类型构造的应用 `app`（`Result<A, B>` 是 `app (app (con R) A) B`）。

**定理**：
- `solve_sound`：查找成功，就有一个推导 `Derives`（每一步用一个 impl，约束都有推导）；
- `solve_complete`：在 `WF`、`Coherent` 下，有推导，查找（深度给到类型的大小）就成功——
  约束里的类型实参都是 `t` 的真子项，所以查找一定会停；
- `impl_unique`：`Coherent` 时，一个类型对一个 trait 至多有一个 impl 适用，所以实例 `方法<t>` 是唯一确定的；
- `instance_resolves`：泛型函数在定义处（假设 `A`）查得到 `t: tr`，类型参数换成满足 `A` 的具体类型 `θ` 以后，
  `θ(t): tr` 也查得到。这就是 M10 的 `RespectsT` 在泛型 impl 下仍然成立的原因：单态化不会因为找不到 impl 而失败。

泛型 impl 的方法是以 impl 的类型参数为类型参数、以 impl 的约束为约束的泛型函数，`Self` 换成头部；
它的实例就是把匹配出的类型实参代进去，由 M9、M10 保证实例通过检查。

**默认方法**（trait 里写了函数体的方法）是带一个类型参数 `Self`、约束 `Self: Tr` 的泛型函数，在 trait 处按泛型检查一次；
某个 impl 没写这个方法时，用的就是它对实现类型的实例。这正是 M10 的情形，不需要新的推理。
-/

namespace Core.M25

inductive Ty
  | var (n : Nat)
  | con (c : Nat)
  | app (f a : Ty)
  deriving DecidableEq, Repr

/-- 代入。 -/
def ap (σ : Nat → Ty) : Ty → Ty
  | .var n => σ n
  | .con c => .con c
  | .app f a => .app (ap σ f) (ap σ a)

def fv : Ty → List Nat
  | .var n => [n]
  | .con _ => []
  | .app f a => fv f ++ fv a

def sz : Ty → Nat
  | .var _ => 1
  | .con _ => 1
  | .app f a => sz f + sz a + 1

def isVar : Ty → Bool
  | .var _ => true
  | _ => false

/-! ## 匹配：impl 的头部（模式）对一个类型 -/

abbrev Sb := List (Nat × Ty)

def look : Sb → Nat → Option Ty
  | [], _ => none
  | (m, u) :: σ, n => if m = n then some u else look σ n

def toFn (σ : Sb) (n : Nat) : Ty := (look σ n).getD (.var n)

/-- 头部 `p` 的类型参数可以对应任何类型（同一个参数出现两次时要对应同一个）；
被匹配的类型 `t` 里的类型参数（泛型函数的）当作普通的类型名。 -/
def mtch : Ty → Ty → Sb → Option Sb
  | .var n, t, σ =>
    match look σ n with
    | some u => if u = t then some σ else none
    | none => some ((n, t) :: σ)
  | .con c, .con d, σ => if c = d then some σ else none
  | .app f a, .app g b, σ =>
    match mtch f g σ with
    | some σ' => mtch a b σ'
    | none => none
  | .con _, .var _, _ => none
  | .con _, .app _ _, _ => none
  | .app _ _, .var _, _ => none
  | .app _ _, .con _, _ => none

def Ext (σ σ' : Sb) : Prop := ∀ n u, look σ n = some u → look σ' n = some u

def Cons (σ : Sb) (τ : Nat → Ty) : Prop := ∀ n u, look σ n = some u → τ n = u

theorem mtch_ext : ∀ (p t : Ty) (σ σ' : Sb), mtch p t σ = some σ' → Ext σ σ'
  | .var n, t, σ, σ', h => by
    cases hl : look σ n with
    | some u =>
      simp [mtch, hl] at h
      obtain ⟨_, rfl⟩ := h
      exact fun _ _ x => x
    | none =>
      simp [mtch, hl] at h
      subst h
      intro m u hm
      simp only [look]
      by_cases e : n = m
      · subst e; rw [hl] at hm; cases hm
      · simp [e, hm]
  | .con c, .con d, σ, σ', h => by
    simp [mtch] at h
    obtain ⟨_, rfl⟩ := h
    exact fun _ _ x => x
  | .app f a, .app g b, σ, σ', h => by
    cases h1 : mtch f g σ with
    | none => simp [mtch, h1] at h
    | some σ1 =>
      simp [mtch, h1] at h
      exact fun n u hn => mtch_ext a b σ1 σ' h n u (mtch_ext f g σ σ1 h1 n u hn)
  | .con _, .var _, _, _, h => by simp [mtch] at h
  | .con _, .app _ _, _, _, h => by simp [mtch] at h
  | .app _ _, .var _, _, _, h => by simp [mtch] at h
  | .app _ _, .con _, _, _, h => by simp [mtch] at h

/-- 匹配成功时，代入匹配出的类型实参（或者更多），头部就是这个类型。 -/
theorem mtch_sound : ∀ (p t : Ty) (σ σ' : Sb), mtch p t σ = some σ' →
    ∀ σ'', Ext σ' σ'' → ap (toFn σ'') p = t
  | .var n, t, σ, σ', h, σ'', he => by
    cases hl : look σ n with
    | some u =>
      simp [mtch, hl] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [ap, toFn, he n _ hl]
    | none =>
      simp [mtch, hl] at h
      subst h
      have : look ((n, t) :: σ) n = some t := by simp [look]
      simp [ap, toFn, he n t this]
  | .con c, .con d, σ, σ', h, _, _ => by
    simp [mtch] at h
    simp [ap, h.1]
  | .app f a, .app g b, σ, σ', h, σ'', he => by
    cases h1 : mtch f g σ with
    | none => simp [mtch, h1] at h
    | some σ1 =>
      simp [mtch, h1] at h
      have e1 := mtch_sound f g σ σ1 h1 σ'' (fun n u x => he n u (mtch_ext a b σ1 σ' h n u x))
      have e2 := mtch_sound a b σ1 σ' h σ'' he
      simp [ap, e1, e2]
  | .con _, .var _, _, _, h, _, _ => by simp [mtch] at h
  | .con _, .app _ _, _, _, h, _, _ => by simp [mtch] at h
  | .app _ _, .var _, _, _, h, _, _ => by simp [mtch] at h
  | .app _ _, .con _, _, _, h, _, _ => by simp [mtch] at h

/-- 匹配成功时，头部的每个类型参数都有对应的类型。 -/
theorem mtch_vars : ∀ (p t : Ty) (σ σ' : Sb), mtch p t σ = some σ' →
    ∀ n ∈ fv p, ∃ u, look σ' n = some u
  | .var n, t, σ, σ', h, m, hm => by
    simp [fv] at hm
    rw [hm]
    cases hl : look σ n with
    | some u =>
      simp [mtch, hl] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨u, hl⟩
    | none =>
      simp [mtch, hl] at h
      subst h
      exact ⟨t, by simp [look]⟩
  | .con _, .con _, _, _, _, _, hm => by simp [fv] at hm
  | .app f a, .app g b, σ, σ', h, n, hm => by
    cases h1 : mtch f g σ with
    | none => simp [mtch, h1] at h
    | some σ1 =>
      simp [mtch, h1] at h
      simp [fv] at hm
      rcases hm with hm | hm
      · obtain ⟨u, hu⟩ := mtch_vars f g σ σ1 h1 n hm
        exact ⟨u, mtch_ext a b σ1 σ' h n u hu⟩
      · exact mtch_vars a b σ1 σ' h n hm
  | .con _, .var _, _, _, h, _, _ => by simp [mtch] at h
  | .con _, .app _ _, _, _, h, _, _ => by simp [mtch] at h
  | .app _ _, .var _, _, _, h, _, _ => by simp [mtch] at h
  | .app _ _, .con _, _, _, h, _, _ => by simp [mtch] at h

/-- 类型是头部的某个实例时，匹配一定成功，匹配出的就是这个实例的类型实参。 -/
theorem mtch_complete (τ : Nat → Ty) : ∀ (p : Ty) (σ : Sb), Cons σ τ →
    ∃ σ', mtch p (ap τ p) σ = some σ' ∧ Cons σ' τ
  | .var n, σ, hc => by
    cases hl : look σ n with
    | some u =>
      have e := hc n u hl
      exact ⟨σ, by simp [mtch, ap, hl, e], hc⟩
    | none =>
      refine ⟨(n, τ n) :: σ, by simp [mtch, ap, hl], ?_⟩
      intro m u hm
      simp only [look] at hm
      by_cases e : n = m
      · subst e; simpa using hm
      · simp [e] at hm; exact hc m u hm
  | .con c, σ, hc => ⟨σ, by simp [mtch, ap], hc⟩
  | .app f a, σ, hc => by
    obtain ⟨σ1, h1, c1⟩ := mtch_complete τ f σ hc
    obtain ⟨σ2, h2, c2⟩ := mtch_complete τ a σ1 c1
    exact ⟨σ2, by simp [mtch, ap, h1, h2], c2⟩

/-! ## impl 和查找 -/

/-- `impl<…> tr for head`，约束 `bnds`：(头部里的类型参数, trait)。 -/
structure Impl where
  tr : Nat
  head : Ty
  bnds : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- 第一个头部能匹配 `t` 的 `tr` 的 impl。 -/
def pick (tr : Nat) (t : Ty) : List Impl → Option (Impl × Sb)
  | [] => none
  | a :: I =>
    if a.tr = tr then
      match mtch a.head t [] with
      | some σ => some (a, σ)
      | none => pick tr t I
    else pick tr t I

/-- 泛型函数里的类型参数：查假设。 -/
def hypOk (A : List (Nat × Nat)) (tr : Nat) : Ty → Bool
  | .var n => decide ((n, tr) ∈ A)
  | _ => false

/-- 查找 `t: tr`，深度至多 `k`。 -/
def solve (I : List Impl) (A : List (Nat × Nat)) : Nat → Nat → Ty → Bool
  | 0, _, _ => false
  | k + 1, tr, t =>
    hypOk A tr t ||
      match pick tr t I with
      | some (a, σ) => a.bnds.all (fun b => (look σ b.1).elim false (fun u => solve I A k b.2 u))
      | none => false

/-- `t: tr` 的推导。 -/
inductive Derives (I : List Impl) (A : List (Nat × Nat)) : Nat → Ty → Prop
  | hyp {n tr} : (n, tr) ∈ A → Derives I A tr (.var n)
  | inst {a tr σ t} : a ∈ I → a.tr = tr → ap σ a.head = t →
      (∀ b ∈ a.bnds, Derives I A b.2 (σ b.1)) → Derives I A tr t

def WF (a : Impl) : Prop := isVar a.head = false ∧ ∀ b ∈ a.bnds, b.1 ∈ fv a.head

/-- 两个头部可能有共同的实例（保守：类型参数和什么都相容）。 -/
def compat : Ty → Ty → Bool
  | .var _, _ => true
  | .con _, .var _ => true
  | .app _ _, .var _ => true
  | .con c, .con d => decide (c = d)
  | .app f a, .app g b => compat f g && compat a b
  | .con _, .app _ _ => false
  | .app _ _, .con _ => false

def Coherent (I : List Impl) : Prop :=
  I.Pairwise (fun a b => a.tr = b.tr → compat a.head b.head = false)

theorem pick_some {tr : Nat} {t : Ty} : ∀ {I : List Impl} {a : Impl} {σ : Sb}, pick tr t I = some (a, σ) →
    a ∈ I ∧ a.tr = tr ∧ mtch a.head t [] = some σ
  | [], _, _, h => by simp [pick] at h
  | b :: I, a, σ, h => by
    by_cases e : b.tr = tr
    · cases hm : mtch b.head t [] with
      | some σ1 =>
        simp [pick, e, hm] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp, e, hm⟩
      | none =>
        simp [pick, e, hm] at h
        obtain ⟨h1, h2, h3⟩ := pick_some h
        exact ⟨by simp [h1], h2, h3⟩
    · simp [pick, e] at h
      obtain ⟨h1, h2, h3⟩ := pick_some h
      exact ⟨by simp [h1], h2, h3⟩

theorem pick_none {tr : Nat} {t : Ty} : ∀ {I : List Impl}, pick tr t I = none →
    ∀ a ∈ I, a.tr = tr → mtch a.head t [] = none
  | [], _, _, ha, _ => by simp at ha
  | b :: I, h, a, ha, e => by
    simp at ha
    by_cases eb : b.tr = tr
    · cases hm : mtch b.head t [] with
      | some σ1 => simp [pick, eb, hm] at h
      | none =>
        simp [pick, eb, hm] at h
        rcases ha with rfl | ha
        · exact hm
        · exact pick_none h a ha e
    · simp [pick, eb] at h
      rcases ha with rfl | ha
      · exact absurd e eb
      · exact pick_none h a ha e

theorem solve_sound (I : List Impl) (A : List (Nat × Nat)) :
    ∀ (k tr : Nat) (t : Ty), solve I A k tr t = true → Derives I A tr t
  | 0, _, _, h => by simp [solve] at h
  | k + 1, tr, t, h => by
    simp only [solve, Bool.or_eq_true] at h
    rcases h with h | h
    · cases t with
      | var n => exact .hyp (by simpa [hypOk] using h)
      | con _ => simp [hypOk] at h
      | app _ _ => simp [hypOk] at h
    · cases hp : pick tr t I with
      | none => simp [hp] at h
      | some p =>
        obtain ⟨a, σ⟩ := p
        obtain ⟨ha, htr, hm⟩ := pick_some hp
        simp only [hp, List.all_eq_true] at h
        refine .inst (σ := toFn σ) ha htr (mtch_sound _ _ _ _ hm σ (fun _ _ x => x)) ?_
        intro b hb
        have hb' := h b hb
        cases hl : look σ b.1 with
        | none => simp [hl] at hb'
        | some u =>
          simp [hl] at hb'
          have e : toFn σ b.1 = u := by simp [toFn, hl]
          rw [e]
          exact solve_sound I A k b.2 u hb'

theorem sz_le : ∀ (p : Ty) (σ : Nat → Ty) (n : Nat), n ∈ fv p → sz (σ n) ≤ sz (ap σ p)
  | .var m, σ, n, h => by
    simp [fv] at h
    subst h
    simp [ap]
  | .con _, _, _, h => by simp [fv] at h
  | .app f a, σ, n, h => by
    simp [fv] at h
    rcases h with h | h
    · have := sz_le f σ n h
      simp only [ap, sz]
      omega
    · have := sz_le a σ n h
      simp only [ap, sz]
      omega

/-- 头部不是单独的类型参数时，匹配出的类型实参比被匹配的类型小。 -/
theorem sz_lt (p : Ty) (σ : Nat → Ty) (n : Nat) (hv : isVar p = false) (h : n ∈ fv p) :
    sz (σ n) < sz (ap σ p) := by
  cases p with
  | var _ => simp [isVar] at hv
  | con _ => simp [fv] at h
  | app f a =>
    simp [fv] at h
    rcases h with h | h
    · have := sz_le f σ n h
      simp only [ap, sz]
      omega
    · have := sz_le a σ n h
      simp only [ap, sz]
      omega

/-- `compat` 是保守的：两个头部有共同的实例，`compat` 就为真。 -/
theorem compat_sound (σ τ : Nat → Ty) : ∀ (p q : Ty), ap σ p = ap τ q → compat p q = true
  | .var _, _, _ => by simp [compat]
  | .con _, .var _, _ => by simp [compat]
  | .app _ _, .var _, _ => by simp [compat]
  | .con c, .con d, h => by
    simp [ap] at h
    simp [compat, h]
  | .app f a, .app g b, h => by
    simp only [ap, Ty.app.injEq] at h
    simp [compat, compat_sound σ τ f g h.1, compat_sound σ τ a b h.2]
  | .con _, .app _ _, h => by simp [ap] at h
  | .app _ _, .con _, h => by simp [ap] at h

theorem pairwise_mem {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ {a b : α},
    a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => by simp at ha
  | x :: l, h, a, b, ha, hb => by
    rw [List.pairwise_cons] at h
    simp at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact .inl rfl
    · exact .inr (.inl (h.1 _ hb))
    · exact .inr (.inr (h.1 _ ha))
    · exact pairwise_mem h.2 ha hb

/-- 至多一个 impl 适用。 -/
theorem impl_unique {I : List Impl} (hc : Coherent I) {a b : Impl} {σ τ : Nat → Ty} {t : Ty}
    (ha : a ∈ I) (hb : b ∈ I) (e : a.tr = b.tr) (h1 : ap σ a.head = t) (h2 : ap τ b.head = t) :
    a = b := by
  rcases pairwise_mem hc ha hb with h | h | h
  · exact h
  · have := compat_sound σ τ a.head b.head (h1.trans h2.symm)
    simp [h e] at this
  · have := compat_sound τ σ b.head a.head (h2.trans h1.symm)
    simp [h e.symm] at this

theorem solve_complete {I : List Impl} {A : List (Nat × Nat)} (hw : ∀ a ∈ I, WF a) (hc : Coherent I)
    {tr : Nat} {t : Ty} (hd : Derives I A tr t) : ∀ k, sz t < k → solve I A k tr t = true := by
  induction hd with
  | hyp hn =>
    intro k hk
    cases k with
    | zero => simp [sz] at hk
    | succ k => simp [solve, hypOk, hn]
  | @inst a tr σ t ha htr hh hb ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      simp only [solve, Bool.or_eq_true]
      right
      obtain ⟨σ1, hm1, c1⟩ := mtch_complete σ a.head [] (fun _ _ h => by simp [look] at h)
      rw [hh] at hm1
      cases hp : pick tr t I with
      | none => exact absurd (pick_none hp a ha htr) (by simp [hm1])
      | some p =>
        obtain ⟨a', σ'⟩ := p
        obtain ⟨ha', htr', hm'⟩ := pick_some hp
        have e1 := mtch_sound _ _ _ _ hm' σ' (fun _ _ x => x)
        have ea : a' = a := impl_unique hc ha' ha (htr'.trans htr.symm) e1 hh
        subst ea
        rw [hm1] at hm'
        cases hm'
        simp only [List.all_eq_true]
        intro b hbm
        have hv := (hw _ ha).2 b hbm
        obtain ⟨u, hu⟩ := mtch_vars _ _ _ _ hm1 b.1 hv
        have eu : σ b.1 = u := c1 _ _ hu
        have hs := sz_lt _ σ b.1 (hw _ ha).1 hv
        rw [hh] at hs
        have hr := ih b hbm k (by omega)
        rw [eu] at hr
        simp [hu, hr]

theorem ap_comp (σ θ : Nat → Ty) : ∀ p : Ty, ap θ (ap σ p) = ap (fun n => ap θ (σ n)) p
  | .var _ => rfl
  | .con _ => rfl
  | .app f a => by simp [ap, ap_comp σ θ f, ap_comp σ θ a]

/-- 推导在代入下保持：假设 `A` 换成它们在 `θ` 下的推导。 -/
theorem derives_ap {I : List Impl} {A B : List (Nat × Nat)} {θ : Nat → Ty}
    (hθ : ∀ p ∈ A, Derives I B p.2 (θ p.1)) {tr : Nat} {t : Ty} (hd : Derives I A tr t) :
    Derives I B tr (ap θ t) := by
  induction hd with
  | hyp hn => exact hθ _ hn
  | @inst a tr σ t ha htr hh hb ih =>
    exact .inst (σ := fun n => ap θ (σ n)) ha htr (by rw [← hh, ap_comp]) ih

/-- **主定理**：定义处查得到，实例也查得到。 -/
theorem instance_resolves {I : List Impl} {A : List (Nat × Nat)} (hw : ∀ a ∈ I, WF a) (hc : Coherent I)
    {θ : Nat → Ty} (hθ : ∀ p ∈ A, solve I [] (sz (θ p.1) + 1) p.2 (θ p.1) = true)
    {tr : Nat} {t : Ty} (h : solve I A (sz t + 1) tr t = true) :
    solve I [] (sz (ap θ t) + 1) tr (ap θ t) = true :=
  solve_complete hw hc
    (derives_ap (fun p hp => solve_sound I [] _ _ _ (hθ p hp)) (solve_sound I A _ _ _ h)) _ (by omega)

/-! ## 例子：trait 0 是 ToStr；类型 0 是 I64，1 是 Vec，2 是 Str -/

def iI64 : Impl := ⟨0, .con 0, []⟩
/-- `impl<T: ToStr> ToStr for Vec<T>` -/
def iVec : Impl := ⟨0, .app (.con 1) (.var 0), [(0, 0)]⟩

example : Coherent [iI64, iVec] := by unfold Coherent; decide
example : solve [iI64, iVec] [] 10 0 (.app (.con 1) (.app (.con 1) (.con 0))) = true := by decide
-- `Vec<Str>`：Str 没有实现。
example : solve [iI64, iVec] [] 10 0 (.app (.con 1) (.con 2)) = false := by decide
-- 泛型函数里有 `T: ToStr`（T 是 5）：`Vec<T>` 也实现了。
example : solve [iI64, iVec] [(5, 0)] 10 0 (.app (.con 1) (.var 5)) = true := by decide
-- 再加 `impl ToStr for Vec<I64>` 就和 `iVec` 重叠，被拒绝。
example : compat iVec.head (.app (.con 1) (.con 0)) = true := by decide

end Core.M25
