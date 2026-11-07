-- 由 sinterc --emit=core 生成，不要手工修改。
import Core.C5
set_option maxRecDepth 100000
open Core.M7h

/-- take -/
def f0 : CFG := [
  ⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 0))))), [2], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 0))))), [3], false⟩,
  ⟨.nop, [], false⟩]

/-- make -/
def f1 : CFG := [
  ⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 0 1))))), [2], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 1))))), [3], false⟩,
  ⟨.nop, [], false⟩]

/-- main -/
def f2 : CFG := [
  ⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 0 1))))), [2], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.sink, 1⟩] []))), [3], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 2))))), [4], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 2 3))))), [5], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 4))))), [6], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 3))))), [7], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 4 3))))), [8], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 3⟩] []))), [9], false⟩,
  ⟨.nop, [10], false⟩,
  ⟨.nop, [11, 16], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 5))))), [12], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 5 6))))), [13], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 6))))), [14], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 6))))), [15], false⟩,
  ⟨.nop, [10], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 7))))), [17], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 7))))), [18], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 8))))), [19], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 8 9))))), [20], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 9))))), [21], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 9))))), [22], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 10))))), [23], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 10 11))))), [24], false⟩,
  ⟨.nop, [25, 27], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.sink, 11⟩] []))), [26], false⟩,
  ⟨.nop, [28], false⟩,
  ⟨.nop, [28], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 12))))), [29], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 12 13))))), [30], false⟩,
  ⟨.nop, [31, 33], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.sink, 13⟩] []))), [32], false⟩,
  ⟨.nop, [34], false⟩,
  ⟨.nop, [34], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 14))))), [35], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 14 15))))), [36], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.sink, 15⟩] []))), [37], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 16))))), [38], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 16 15))))), [39], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 15⟩] []))), [40], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 17))))), [41], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 17⟩] []))), [42], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 17))))), [43], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 15))))), [44], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 9))))), [45], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 3))))), [46], false⟩,
  ⟨.nop, [], false⟩]

#eval Core.C5.report [("take", 1, f0), ("make", 2, f1), ("main", 18, f2)] true
