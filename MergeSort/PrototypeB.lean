import Init.Data.Array.Basic
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic
import MergeSort.USize.Extras

namespace PrototypeB

variable
  {α : Type}
  {arr aux : Array α}
  {low mid high ptr₁ ptr₂ i chunkSize : USize}

@[specialize, inline]
partial def mergeAdjacentChunksIntoAux
    [Ord α]
    [Inhabited α]
    (arr : Array α)
    (low mid high : USize)
    (aux : Array α)
    : Array α :=
  let rec @[specialize] loop
      (ptr₁ ptr₂ i : USize)
      (aux : Array α)
      : Array α :=
    if ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
      match Ord.compare arr[ptr₁]! arr[ptr₂]! with
      | .lt | .eq =>
        let aux' := aux.uset i arr[ptr₁]! sorry
        loop ptr₁.succ ptr₂ i.succ aux'
      | .gt =>
        let aux' := aux.uset i arr[ptr₂]! sorry
        loop ptr₁ ptr₂.succ i.succ aux'
    else
      let rec @[specialize] loopLeft
          (ptr₁ i : USize)
          (aux : Array α)
          : Array α :=
        if ptr₁_lt_mid : ptr₁ < mid then
          let aux' := aux.uset i arr[ptr₁]! sorry
          loopLeft ptr₁.succ i.succ aux'
        else
          let rec @[specialize] loopRight
              (ptr₂ i : USize)
              (aux : Array α)
              : Array α :=
            if ptr₂_lt_high : ptr₂ < high then
              let aux' := aux.uset i arr[ptr₂]! sorry
              loopRight ptr₂.succ i.succ aux'
            else
              aux
          loopRight ptr₂ i aux
      loopLeft ptr₁ i aux
  loop (ptr₁ := low) (ptr₂ := mid) (i := low) aux

@[specialize, inline]
partial def mergeChunksIntoAux
    [Ord α]
    [Inhabited α]
    (arr : Array α)
    (chunkSize : USize)
    (aux : Array α)
    : Array α :=
  let rec @[specialize] loop
      (low : USize)
      (aux : Array α)
      : Array α :=
    if size_minus_low_gt_chunkSize : chunkSize < arr.usize - low then
      let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      let aux' := mergeAdjacentChunksIntoAux arr low mid high aux
      loop high aux'
    else
      let rec @[specialize] loopFinal
          (low : USize)
          (aux : Array α)
          : Array α :=
        if low_lt_aux_usize : low < aux.usize then
          let aux' := aux.uset low arr[low]! sorry
          loopFinal low.succ aux'
        else
          aux
      loopFinal low aux
  loop 0 aux

@[specialize, inline]
partial def Array.mergeSortWithAuxiliary
    [Ord α]
    [Inhabited α]
    (arr aux : Array α)
    : Array α :=
  let rec @[specialize] loop
      (arr aux : Array α)
      (chunkSize : USize)
      : Array α :=
    if _chunkSize_lt_arr_usize : chunkSize < arr.usize then
      let aux' := mergeChunksIntoAux arr chunkSize aux
      let chunkSize' := chunkSize + min (arr.usize - chunkSize) chunkSize
      loop aux' arr chunkSize'
    else
      arr
  loop arr aux 1

@[specialize, inline]
def Array.mergeSort
    [Inhabited α]
    [Ord α]
    (arr : Array α)
    (_arr_size_lt_usize_size : arr.size < USize.size)
    : Array α :=
  let aux := .replicate arr.size default
  mergeSortWithAuxiliary arr aux

end PrototypeB
