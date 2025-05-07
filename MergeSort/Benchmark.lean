import MergeSort.ArrayGenerators
import MergeSort.Implementation
import MergeSort.PrototypeA
import MergeSort.PrototypeB
import MergeSort.PrototypeC
import MergeSort.PrototypeD
import MergeSort.PrototypeE
import MergeSort.PrototypeF
import MergeSort.PrototypeG
import MergeSort.PrototypeCA
import MergeSort.PrototypeCB

def benchmark
    {data₁ data₂}
    (makeArray : Unit → Array Nat)
    (prepare : Array Nat → data₁)
    (go : data₁ → data₂)
    (finish : data₂ → Nat)
    : IO (Nat × Nat) := do
  let data := prepare <| makeArray ()
  let start ← IO.monoNanosNow
  let result := go data
  let elapsed := (← IO.monoNanosNow) - start
  let optimizationPreventionValue := finish result
  pure (elapsed, optimizationPreventionValue)

@[specialize, inline]
def Benchmark.Array.mergeSortGeneric
    (algo : (arr : Array Nat) → arr.size < USize.size → Array Nat)
    (makeArray : Unit → Array Nat)
    : IO (Nat × Nat) :=
  benchmark makeArray prepare go finish
where
  @[specialize, inline]
  prepare (arr : Array Nat) : Unit → Array Nat :=
    if h : arr.size < USize.size then
      fun () => algo arr h
    else
      panic! "arr ≥ USize.size"
  @[specialize, inline]
  go := (· ())
  @[specialize, inline]
  finish (arr : Array Nat) : Nat :=
    match arr[0]? with
    | .none => 0
    | .some v => v

def Benchmark.Array.mergeSort (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.Array.mergeSort makeArray

def Benchmark.Array.mergeSortA (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.PrototypeA.Array.mergeSort makeArray

def Benchmark.Array.mergeSortB (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.PrototypeB.Array.mergeSort makeArray

def Benchmark.Array.mergeSortC (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.PrototypeC.Array.mergeSort makeArray

def Benchmark.Array.mergeSortD (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.PrototypeD.Array.mergeSort makeArray

def Benchmark.Array.mergeSortE (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.PrototypeE.Array.mergeSort makeArray

def Benchmark.Array.mergeSortF (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.PrototypeF.Array.mergeSort makeArray

def Benchmark.Array.mergeSortG (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  benchmark makeArray prepare go finish
where
  prepare (arr : Array Nat) : Unit → Array Nat :=
    if h : arr.size < USize.size then
      let vec := arr.toVector
      fun () => _root_.PrototypeG.Array.mergeSort vec h |>.toArray
    else
      panic! "arr ≥ USize.size"
  go := (· ())
  finish (arr : Array Nat) : Nat :=
    match arr[0]? with
    | .none => 0
    | .some v => v

def Benchmark.Array.mergeSortCA (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.PrototypeCA.Array.mergeSort makeArray

def Benchmark.Array.mergeSortCB (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  benchmark makeArray prepare go finish
where
  prepare (arr : Array Nat) : Unit → Array Nat :=
    if h : arr.size < USize.size then
      let vec := arr.toVector
      fun () => _root_.PrototypeCB.Array.mergeSort vec h |>.toArray
    else
      panic! "arr ≥ USize.size"
  go := (· ())
  finish (arr : Array Nat) : Nat :=
    match arr[0]? with
    | .none => 0
    | .some v => v

def Benchmark.Array.qsortOrd (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  benchmark makeArray prepare go finish
where
  prepare (arr : Array Nat) : Array Nat := arr
  go arr := arr.qsortOrd
  finish (arr : Array Nat) : Nat :=
    match arr[0]? with
    | .none => 0
    | .some v => v

def Benchmark.List.mergeSort (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  benchmark makeArray prepare go finish
where
  prepare (arr : Array Nat) : List Nat := arr.toList
  go (lst : List Nat) : List Nat := lst.mergeSort
  finish (lst : List Nat) : Nat :=
    match lst[0]? with
    | .none => 0
    | .some v => v

def Nat.nsToMs (ns : Nat) : Nat := ns / 10 ^ 6
def Nat.msToS (ms : Nat) : Nat := ms / 10 ^ 3

def runOnAllArrayGenerators
    (algoName : String)
    (size : Nat)
    (seed : Nat)
    (go : (Unit → Array Nat) → IO (Nat × Nat))
    : IO Unit := do
  let printResult (fnName : String) (fn : Unit → Array Nat) : IO Unit := do
    let (time₁, opv₁) ← go fn
    let (time₂, opv₂) ← go fn
    let (time₃, opv₃) ← go fn
    let time := (time₁ + time₂ + time₃) / 3
    let opv := opv₁ + opv₂ + opv₃
    -- println! s!"{opv} → {time.nsToMs.msToS}s\t\t{time.nsToMs}ms\t\t{time}ns\t\t{fnName}"
    println! s!"{time}"
  -- println! s!"Testing {algoName} using (size := {size}) (seed := {seed}) (average of 3 runs on each test)"
  printResult "mostlyAscending" fun () => Array.mostlyAscending size seed
  printResult "randomWithDuplicates" fun () => Array.randomWithDuplicates size seed
  printResult "random" fun () => Array.random size seed
  printResult "ascending" fun () => Array.ascending size
  printResult "descending" fun () => Array.descending size
  printResult "ascendingWithRandomTail" fun () => Array.ascendingWithRandomTail size seed
