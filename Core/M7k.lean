import Core.M7j

/-!
# M7（七·下）：降级正确——`lower` 满足嵌入关系

证明 M7（六）的翻译 `lw` 产生的节点表满足 M7（七·上）的嵌入关系 `Emb`，合起来得到：

**主定理** `lowering_correct`：结构化程序 `p` 的执行只要没有耗尽燃料，降级后的 CFG `lower p`
用足够的燃料执行，得到**同一个结果**（同一个结束状态、同一个剩余选择序列）。

`lw` 的不变式 `Good`：
- 节点表只增长；
- 已有的节点不变（循环头的占位节点是在循环体翻译之后才改写的，它的下标不在已有节点里）；
- 对任何在新节点上和翻译结果一致的 CFG，嵌入关系成立。
  最后一条只要求“新节点一致”，所以后面再追加节点、或者改写更早的节点（循环头、入口节点 0），都不影响它。
-/

namespace Core.M7j
open Core.M7d (Q St exec)
open Core.M7h (Op Node CFG run)
open Core.M7i (LS emit lw lowerS lower)

/-! ## 列表引理 -/

theorem ga_left {l m : List Node} {j : Nat} (hj : j < l.length) : (l ++ m)[j]? = l[j]? :=
  List.getElem?_append_left hj

theorem ga_last {l : List Node} {x : Node} : (l ++ [x])[l.length]? = some x := by simp

theorem ga_left2 {l : List Node} {x y : Node} {j : Nat} (hj : j < l.length) :
    (l ++ [x] ++ [y])[j]? = l[j]? := by
  rw [ga_left (by simp; omega), ga_left hj]

theorem ga_mid {l : List Node} {x y : Node} : (l ++ [x] ++ [y])[l.length]? = some x := by
  rw [ga_left (by simp)]
  exact ga_last

theorem ga_mid2 {l : List Node} {x y : Node} : (l ++ [x] ++ [y])[l.length + 1]? = some y := by
  have h : l.length + 1 = (l ++ [x]).length := by simp
  rw [h]
  exact ga_last

theorem gs_ne {l : List Node} {h j : Nat} {x : Node} (hj : h ≠ j) : (l.set h x)[j]? = l[j]? := by
  simp [hj]

theorem gs_eq {l : List Node} {h : Nat} {x : Node} (hh : h < l.length) : (l.set h x)[h]? = some x := by
  simp [hh]

theorem emit_fst (s : LS) (n : Node) : (emit s n).1 = s.ns.length := rfl
theorem emit_ns (s : LS) (n : Node) : (emit s n).2.ns = s.ns ++ [n] := rfl

/-! ## `lw` 的不变式 -/

abbrev Good (q : Q) (k e : Nat) (s : LS) (r : Nat × LS) : Prop :=
  s.ns.length ≤ r.2.ns.length ∧
  (∀ j, j < s.ns.length → r.2.ns[j]? = s.ns[j]?) ∧
  (∀ g : CFG, (∀ j, s.ns.length ≤ j → j < r.2.ns.length → g[j]? = r.2.ns[j]?) → Emb g q r.1 k e)

theorem lw_good (q : Q) : ∀ (k e : Nat) (E : List Var) (s : LS), Good q k e s (lw q k e E s) := by
  induction q with
  | skip => intro k e E s; exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => .skip⟩
  | cmd c =>
    intro k e E s
    simp only [Good, lw, emit_fst, emit_ns, List.length_append, List.length_singleton]
    refine ⟨by omega, fun j hj => ga_left hj, fun g hg => .cmd ?_⟩
    rw [hg s.ns.length (Nat.le_refl _) (by omega)]
    exact ga_last
  | seq p q ihp ihq =>
    intro k e E s
    have a := ihq k e E s
    simp only [Good, lw]
    have b := ihp (lw q k e E s).1 e E (lw q k e E s).2
    simp only [Good] at a b
    generalize lw q k e E s = r1 at a b ⊢
    generalize lw p r1.1 e E r1.2 = r2 at b ⊢
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    refine ⟨Nat.le_trans a1 b1, fun j hj => (b2 j (Nat.lt_of_lt_of_le hj a1)).trans (a2 j hj),
      fun g hg => .seq (a3 g ?_) (b3 g ?_)⟩
    · intro j h1 h2
      rw [hg j h1 (Nat.lt_of_lt_of_le h2 b1)]
      exact b2 j h2
    · intro j h1 h2
      exact hg j (Nat.le_trans a1 h1) h2
  | branch p q ihp ihq =>
    intro k e E s
    have a := ihp k e E s
    simp only [Good, lw]
    have b := ihq k e E (lw p k e E s).2
    simp only [Good] at a b
    generalize lw p k e E s = r1 at a b ⊢
    generalize lw q k e E r1.2 = r2 at b ⊢
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    simp only [emit_fst, emit_ns, List.length_append, List.length_singleton]
    refine ⟨by omega, fun j hj => ?_, fun g hg => .branch (a3 g ?_) (b3 g ?_) ?_⟩
    · rw [ga_left (show j < r2.2.ns.length by omega)]
      exact (b2 j (by omega)).trans (a2 j hj)
    · intro j h1 h2
      rw [hg j h1 (by omega), ga_left (show j < r2.2.ns.length by omega)]
      exact b2 j h2
    · intro j h1 h2
      rw [hg j (by omega) (by omega), ga_left (show j < r2.2.ns.length by omega)]
    · rw [hg r2.2.ns.length (by omega) (by omega)]
      exact ga_last
  | loop b ih =>
    intro k e E s
    simp only [Good, lw]
    have a := ih s.ns.length e E { s with ns := s.ns ++ [⟨.nop, [], false⟩] }
    simp only [Good] at a
    generalize lw b s.ns.length e E { s with ns := s.ns ++ [⟨.nop, [], false⟩] } = rb at a ⊢
    obtain ⟨a1, a2, a3⟩ := a
    simp only [List.length_append, List.length_singleton, List.length_set] at a1 a2 a3 ⊢
    refine ⟨by omega, fun j hj => ?_, fun g hg => .loop ?_ (a3 g ?_)⟩
    · rw [gs_ne (show s.ns.length ≠ j by omega), a2 j (by omega), ga_left hj]
    · rw [hg s.ns.length (Nat.le_refl _) (by omega)]
      exact gs_eq (by omega)
    · intro j h1 h2
      rw [hg j (by omega) h2, gs_ne (show s.ns.length ≠ j by omega)]
  | fail => intro k e E s; exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => .fail⟩
  | guard x p ih =>
    intro k e E s
    simp only [Good, lw]
    have a := ih k (emit s ⟨.cmd (.base (.lin (.consume x))), [e], false⟩).1 (x :: E)
      (emit s ⟨.cmd (.base (.lin (.consume x))), [e], false⟩).2
    simp only [Good] at a
    generalize lw p k (emit s ⟨.cmd (.base (.lin (.consume x))), [e], false⟩).1 (x :: E)
      (emit s ⟨.cmd (.base (.lin (.consume x))), [e], false⟩).2 = r at a ⊢
    obtain ⟨a1, a2, a3⟩ := a
    simp only [emit_fst, emit_ns, List.length_append, List.length_singleton] at a1 a2 a3 ⊢
    refine ⟨by omega, fun j hj => ?_, fun g hg => .guard ?_ (a3 g ?_) ?_⟩
    · rw [ga_left (show j < r.2.ns.length by omega), a2 j (by omega), ga_left hj]
    · rw [hg s.ns.length (Nat.le_refl _) (by omega),
        ga_left (show s.ns.length < r.2.ns.length by omega), a2 s.ns.length (by omega)]
      exact ga_last
    · intro j h1 h2
      rw [hg j (by omega) (by omega), ga_left (show j < r.2.ns.length by omega)]
    · rw [hg r.2.ns.length (by omega) (by omega)]
      exact ga_last
  | block p ih =>
    intro k e E s
    simp only [Good, lw]
    have a := ih (emit s ⟨.leave, [k], false⟩).1
      (emit (emit s ⟨.leave, [k], false⟩).2 ⟨.leave, [e], false⟩).1 E
      (emit (emit s ⟨.leave, [k], false⟩).2 ⟨.leave, [e], false⟩).2
    simp only [Good] at a
    generalize lw p (emit s ⟨.leave, [k], false⟩).1
      (emit (emit s ⟨.leave, [k], false⟩).2 ⟨.leave, [e], false⟩).1 E
      (emit (emit s ⟨.leave, [k], false⟩).2 ⟨.leave, [e], false⟩).2 = r at a ⊢
    obtain ⟨a1, a2, a3⟩ := a
    simp only [emit_fst, emit_ns, List.length_append, List.length_singleton] at a1 a2 a3 ⊢
    refine ⟨by omega, fun j hj => ?_, fun g hg => .block ?_ ?_ (a3 g ?_) ?_⟩
    · rw [ga_left (show j < r.2.ns.length by omega), a2 j (by omega), ga_left2 hj]
    · rw [hg s.ns.length (Nat.le_refl _) (by omega),
        ga_left (show s.ns.length < r.2.ns.length by omega), a2 s.ns.length (by omega)]
      exact ga_mid
    · rw [hg (s.ns.length + 1) (by omega) (by omega),
        ga_left (show s.ns.length + 1 < r.2.ns.length by omega), a2 (s.ns.length + 1) (by omega)]
      exact ga_mid2
    · intro j h1 h2
      rw [hg j (by omega) (by omega), ga_left (show j < r.2.ns.length by omega)]
    · rw [hg r.2.ns.length (by omega) (by omega)]
      exact ga_last

/-! ## 整个程序 -/

def s0 : LS := ⟨[⟨.nop, [], false⟩, ⟨.nop, [], false⟩, ⟨.nop, [], true⟩], [], true⟩

theorem lower_emb (p : Q) :
    Emb (lower p) p (lw p 1 2 [] s0).1 1 2 ∧
    (lower p)[0]? = some ⟨.nop, [(lw p 1 2 [] s0).1], false⟩ ∧
    (lower p)[1]? = some ⟨.nop, [], false⟩ ∧ (lower p)[2]? = some ⟨.nop, [], true⟩ := by
  have hl : lower p = (lw p 1 2 [] s0).2.ns.set 0 ⟨.nop, [(lw p 1 2 [] s0).1], false⟩ := rfl
  have a := lw_good p 1 2 [] s0
  simp only [Good] at a
  rw [hl]
  generalize lw p 1 2 [] s0 = r at a ⊢
  obtain ⟨a1, a2, a3⟩ := a
  have h3 : s0.ns.length = 3 := rfl
  rw [h3] at a1 a2 a3
  refine ⟨a3 _ (fun j h1 _ => gs_ne (by omega)), gs_eq (by omega), ?_, ?_⟩
  · exact (gs_ne (by omega)).trans ((a2 1 (by omega)).trans rfl)
  · exact (gs_ne (by omega)).trans ((a2 2 (by omega)).trans rfl)

/-- **M7（七）主定理（降级正确）。** 结构化程序的执行只要没有耗尽燃料，降级后的 CFG 用足够的燃料执行，
得到同一个结果：同一个结束种类、同一个结束状态、同一个剩余选择序列。 -/
theorem lowering_correct (p : Q) (n : Nat) (st : St) (cs : List Bool)
    (hr : exec n p st cs ≠ .oof) :
    ∃ m, run (lower p) m 0 st cs = exec n p st cs := by
  obtain ⟨he, h0, h1, h2⟩ := lower_emb p
  exact sim_run he h0 h1 h2 n st cs hr

end Core.M7j
