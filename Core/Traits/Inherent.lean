import Core.Traits.ImplSearch

/-!
# 类型自己的方法

`impl 类型 { fn m(self: 类型, …) … }` 给一个类型加方法，类型可以是内建的（`Str`、`Vec<T>`），也可以是具体的实例
（`impl Vec<I64> { fn sum… }` 和 `impl Vec<F64> { fn sum… }` 并存）。每个方法编译成一个普通函数 `fn`，
头部的类型参数是它的类型参数。

方法调用 `x.m(args)`，`x` 的类型是 `t`，在定义处查找：
1. 名字是 `m`、头部能匹配 `t` 的方法 → 调用 `fn<σ>(x, args)`，`σ` 是匹配出的类型实参；
2. 没有的话，约束里查得到 `t: tr`、并且声明了方法 `m` 的 trait，恰好一个 → 调用 `tr` 的方法；
3. 否则报错（没有这个方法，或者两个 trait 都有这个名字）。

全局函数不参与查找，所以 trait 的方法名不再占用全局名字。展开后就是一次普通调用，所有权、区域的检查照旧。

编译器对同名的任意两个方法要求头部不相容（`CoherentM`，和 `ImplSearch.Coherent` 用同一个 `compat`）。

**定理**：
- `resolve_inh`：查到方法，它的头部代入匹配出的类型实参就是 `t`；
- `resolve_complete`：`CoherentM` 下，头部能匹配 `t` 的方法一定被查到，和方法的书写顺序无关；
- `resolve_tra`：落到 trait 时，有 `t: tr` 的推导，并且没有同名方法能匹配 `t`；
- `resolve_tra_instance`：落到 trait 时，类型参数换成满足约束的具体类型以后 impl 也查得到——单态化不会失败；
- `resolve_stable`：查到方法时，类型参数换成什么，查到的都是同一个函数。

落到 trait 的调用在单态化以后**不**重新查找：`resolve_stable` 只对查到方法的情形成立，
例子里 `T: Show` 时 `x.show()` 是 trait 的方法，`T` 换成 `I64` 后重新查会查到 `impl I64` 的 `show`。
所以规则是在定义处查一次，实例沿用定义处的结果。

**反例**：两个 `len` 的头部 `Vec<T>`、`Vec<I64>` 重叠时 `CoherentM` 不成立，`Vec<I64>` 的 `v.len()`
按书写顺序会查到不同的函数。
-/

namespace Core.Traits.Inherent

open Core.Traits.ImplSearch

/-- `impl head { fn name … }`，编译成函数 `fn`。 -/
structure Meth where
  name : Nat
  head : Ty
  fn : Nat
  deriving DecidableEq, Repr

/-- trait `tr` 声明了方法 `name`。 -/
structure TMeth where
  tr : Nat
  name : Nat
  deriving DecidableEq, Repr

def CoherentM (M : List Meth) : Prop :=
  M.Pairwise (fun a b => a.name = b.name → compat a.head b.head = false)

/-- 第一个名字是 `n`、头部能匹配 `t` 的方法。 -/
def pickM (n : Nat) (t : Ty) : List Meth → Option (Meth × Sb)
  | [] => none
  | a :: M =>
    if a.name = n then
      match mtch a.head t [] with
      | some σ => some (a, σ)
      | none => pickM n t M
    else pickM n t M

inductive Res
  | inh (f : Nat) (σ : Sb)
  | tra (tr : Nat)
  | err
  deriving DecidableEq, Repr

/-- 约束里查得到 `t: tr`、声明了方法 `n` 的 trait。 -/
def cands (I : List Impl) (A : List (Nat × Nat)) (k : Nat) (T : List TMeth) (n : Nat) (t : Ty) : List TMeth :=
  T.filter (fun m => decide (m.name = n) && solve I A k m.tr t)

def fallback : List TMeth → Res
  | [m] => .tra m.tr
  | [] => .err
  | _ :: _ :: _ => .err

def resolve (M : List Meth) (T : List TMeth) (I : List Impl) (A : List (Nat × Nat)) (k n : Nat) (t : Ty) : Res :=
  match pickM n t M with
  | some p => .inh p.1.fn p.2
  | none => fallback (cands I A k T n t)

theorem pickM_some {n : Nat} {t : Ty} : ∀ {M : List Meth} {a : Meth} {σ : Sb}, pickM n t M = some (a, σ) →
    a ∈ M ∧ a.name = n ∧ mtch a.head t [] = some σ
  | [], _, _, h => by simp [pickM] at h
  | b :: M, a, σ, h => by
    by_cases e : b.name = n
    · cases hm : mtch b.head t [] with
      | some σ1 =>
        simp [pickM, e, hm] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp, e, hm⟩
      | none =>
        simp [pickM, e, hm] at h
        obtain ⟨h1, h2, h3⟩ := pickM_some h
        exact ⟨by simp [h1], h2, h3⟩
    · simp [pickM, e] at h
      obtain ⟨h1, h2, h3⟩ := pickM_some h
      exact ⟨by simp [h1], h2, h3⟩

theorem pickM_none {n : Nat} {t : Ty} : ∀ {M : List Meth}, pickM n t M = none →
    ∀ a ∈ M, a.name = n → mtch a.head t [] = none
  | [], _, _, ha, _ => by simp at ha
  | b :: M, h, a, ha, e => by
    simp at ha
    by_cases eb : b.name = n
    · cases hm : mtch b.head t [] with
      | some σ1 => simp [pickM, eb, hm] at h
      | none =>
        simp [pickM, eb, hm] at h
        rcases ha with rfl | ha
        · exact hm
        · exact pickM_none h a ha e
    · simp [pickM, eb] at h
      rcases ha with rfl | ha
      · exact absurd e eb
      · exact pickM_none h a ha e

/-- 同名的方法至多一个适用。 -/
theorem meth_unique {M : List Meth} (hc : CoherentM M) {a b : Meth} {σ τ : Nat → Ty} {t : Ty}
    (ha : a ∈ M) (hb : b ∈ M) (e : a.name = b.name) (h1 : ap σ a.head = t) (h2 : ap τ b.head = t) :
    a = b := by
  rcases pairwise_mem hc ha hb with h | h | h
  · exact h
  · have := compat_sound σ τ a.head b.head (h1.trans h2.symm)
    simp [h e] at this
  · have := compat_sound τ σ b.head a.head (h2.trans h1.symm)
    simp [h e.symm] at this

theorem pickM_complete {M : List Meth} (hc : CoherentM M) {a : Meth} {n : Nat} {σ : Nat → Ty} {t : Ty}
    (ha : a ∈ M) (hn : a.name = n) (hh : ap σ a.head = t) : ∃ σ', pickM n t M = some (a, σ') := by
  obtain ⟨σ1, hm1, _⟩ := mtch_complete σ a.head [] (fun _ _ h => by simp [look] at h)
  rw [hh] at hm1
  cases hp : pickM n t M with
  | none => exact absurd (pickM_none hp a ha hn) (by simp [hm1])
  | some p =>
    obtain ⟨b, σ'⟩ := p
    obtain ⟨hb, hbn, hm'⟩ := pickM_some hp
    have e1 := mtch_sound _ _ _ _ hm' σ' (fun _ _ x => x)
    have eb : b = a := meth_unique hc hb ha (hbn.trans hn.symm) e1 hh
    subst eb
    exact ⟨σ', rfl⟩

theorem fallback_ne_inh {c : List TMeth} {f : Nat} {σ : Sb} : fallback c ≠ .inh f σ := by
  cases c with
  | nil => simp [fallback]
  | cons m c => cases c <;> simp [fallback]

theorem fallback_tra {c : List TMeth} {tr : Nat} (h : fallback c = .tra tr) : ∃ m, c = [m] ∧ m.tr = tr := by
  cases c with
  | nil => simp [fallback] at h
  | cons m c =>
    cases c with
    | nil =>
      simp [fallback] at h
      exact ⟨m, rfl, h⟩
    | cons _ _ => simp [fallback] at h

theorem resolve_inh {M : List Meth} {T : List TMeth} {I : List Impl} {A : List (Nat × Nat)} {k n f : Nat}
    {t : Ty} {σ : Sb} (h : resolve M T I A k n t = .inh f σ) :
    ∃ a ∈ M, a.name = n ∧ a.fn = f ∧ ap (toFn σ) a.head = t := by
  cases hp : pickM n t M with
  | none => simp [resolve, hp, fallback_ne_inh] at h
  | some p =>
    obtain ⟨a, σ1⟩ := p
    simp [resolve, hp] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ha, hn, hm⟩ := pickM_some hp
    exact ⟨a, ha, hn, rfl, mtch_sound _ _ _ _ hm _ (fun _ _ x => x)⟩

/-- 能匹配的方法一定被查到；约束、trait、书写顺序都不影响。 -/
theorem resolve_complete {M : List Meth} (hc : CoherentM M) (T : List TMeth) (I : List Impl)
    (A : List (Nat × Nat)) (k : Nat) {a : Meth} {n : Nat} {σ : Nat → Ty} {t : Ty}
    (ha : a ∈ M) (hn : a.name = n) (hh : ap σ a.head = t) :
    ∃ σ', resolve M T I A k n t = .inh a.fn σ' := by
  obtain ⟨σ', hp⟩ := pickM_complete hc ha hn hh
  exact ⟨σ', by simp [resolve, hp]⟩

theorem resolve_tra {M : List Meth} {T : List TMeth} {I : List Impl} {A : List (Nat × Nat)} {k n tr : Nat}
    {t : Ty} (h : resolve M T I A k n t = .tra tr) :
    Derives I A tr t ∧ (∃ m ∈ T, m.tr = tr ∧ m.name = n) ∧ (∀ a ∈ M, a.name = n → mtch a.head t [] = none) := by
  cases hp : pickM n t M with
  | some p =>
    obtain ⟨a, σ1⟩ := p
    simp [resolve, hp] at h
  | none =>
    simp only [resolve, hp] at h
    obtain ⟨m, hc, rfl⟩ := fallback_tra h
    have hmem : m ∈ cands I A k T n t := by rw [hc]; simp
    have hf := List.mem_filter.mp hmem
    have h2 := hf.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact ⟨solve_sound I A k m.tr t h2.2, ⟨m, hf.1, rfl, h2.1⟩, fun a ha hn => pickM_none hp a ha hn⟩

/-- 落到 trait 时，实例里 impl 查得到。 -/
theorem resolve_tra_instance {M : List Meth} {T : List TMeth} {I : List Impl} {A : List (Nat × Nat)}
    (hw : ∀ a ∈ I, WF a) (hcI : Coherent I) {θ : Nat → Ty}
    (hθ : ∀ p ∈ A, solve I [] (sz (θ p.1) + 1) p.2 (θ p.1) = true) {n tr : Nat} {t : Ty}
    (h : resolve M T I A (sz t + 1) n t = .tra tr) :
    solve I [] (sz (ap θ t) + 1) tr (ap θ t) = true := by
  obtain ⟨hd, _, _⟩ := resolve_tra h
  exact solve_complete hw hcI (derives_ap (fun p hp => solve_sound I [] _ _ _ (hθ p hp)) hd) _ (by omega)

/-- **主定理**：查到方法时，类型参数换成什么都查到同一个函数。 -/
theorem resolve_stable {M : List Meth} (hc : CoherentM M) {T : List TMeth} {I : List Impl}
    {A : List (Nat × Nat)} {k n f : Nat} {t : Ty} {σ : Sb} (h : resolve M T I A k n t = .inh f σ)
    (θ : Nat → Ty) (T' : List TMeth) (I' : List Impl) (A' : List (Nat × Nat)) (k' : Nat) :
    ∃ σ', resolve M T' I' A' k' n (ap θ t) = .inh f σ' := by
  obtain ⟨a, ha, hn, rfl, hh⟩ := resolve_inh h
  have e : ap (fun x => ap θ (toFn σ x)) a.head = ap θ t := by rw [← hh, ap_comp]
  exact resolve_complete hc T' I' A' k' ha hn e

/-! ## 例子：类型 0 是 I64，1 是 Vec，2 是 Str，3 是 F64；方法名 0 是 sum，1 是 len，2 是 show -/

def vecOf (t : Ty) : Ty := .app (.con 1) t

/-- `impl Vec<I64> { fn sum }`、`impl Vec<F64> { fn sum }` -/
def mSumI : Meth := ⟨0, vecOf (.con 0), 10⟩
def mSumF : Meth := ⟨0, vecOf (.con 3), 11⟩

example : CoherentM [mSumI, mSumF] := by unfold CoherentM; decide
example : resolve [mSumI, mSumF] [] [] [] 10 0 (vecOf (.con 3)) = .inh 11 [] := by decide
-- `Vec<Str>` 没有 `sum`。
example : resolve [mSumI, mSumF] [] [] [] 10 0 (vecOf (.con 2)) = .err := by decide

/-- 反例：`impl<T> Vec<T> { fn len }` 和 `impl Vec<I64> { fn len }` 重叠。 -/
def mLenT : Meth := ⟨1, vecOf (.var 0), 20⟩
def mLenI : Meth := ⟨1, vecOf (.con 0), 21⟩

example : ¬ CoherentM [mLenT, mLenI] := by unfold CoherentM; decide
-- 同一个调用，书写顺序不同就查到不同的函数。
example : resolve [mLenT, mLenI] [] [] [] 10 1 (vecOf (.con 0)) = .inh 20 [(0, .con 0)] := by decide
example : resolve [mLenI, mLenT] [] [] [] 10 1 (vecOf (.con 0)) = .inh 21 [] := by decide

/-- trait 0 是 Show，声明方法 `show`；`impl Show for I64`；另有 `impl I64 { fn show }`。 -/
def iShow : Impl := ⟨0, .con 0, []⟩
def mShowI : Meth := ⟨2, .con 0, 30⟩

-- 泛型函数里 `T: Show`（T 是 5）：`x.show()` 是 trait 的方法。
example : resolve [mShowI] [⟨0, 2⟩] [iShow] [(5, 0)] 10 2 (.var 5) = .tra 0 := by decide
-- `T` 换成 `I64` 后重新查会查到 `impl I64` 的方法，所以落到 trait 的调用不在实例里重新查。
example : resolve [mShowI] [⟨0, 2⟩] [iShow] [] 10 2 (.con 0) = .inh 30 [] := by decide
-- 两个 trait 都有 `show`、`T` 两个都满足：报错。
example : resolve [] [⟨0, 2⟩, ⟨1, 2⟩] [] [(5, 0), (5, 1)] 10 2 (.var 5) = .err := by decide
-- 只声明了 trait，`T` 没有这个约束：报错，不落到全局函数。
example : resolve [] [⟨0, 2⟩] [iShow] [] 10 2 (.var 5) = .err := by decide

end Core.Traits.Inherent
