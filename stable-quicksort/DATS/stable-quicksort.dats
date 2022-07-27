(*
  Copyright © 2022 Barry Schwartz

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License, as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received copies of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

#define ATS_DYNLOADFLAG 0

#define ATS_PACKNAME "ats2-stable-quicksort"
#define ATS_EXTERN_PREFIX "ats2_stable_quicksort_"

#include "share/atspre_staload.hats"
staload "stable-quicksort/SATS/stable-quicksort.sats"
staload UN = "prelude/SATS/unsafe.sats"

#define DEFAULT_LIST_INSERTION_SORT_THRESHOLD 32
#define DEFAULT_ARRAY_INSERTION_SORT_THRESHOLD 32
#define ARRAY_STACK_STORAGE_THRESHOLD 256

#define NIL list_vt_nil ()
#define ::  list_vt_cons

prfn
lemma_mul_isfun
          {m1, n1 : int}
          {m2, n2 : int | m1 == m2; n1 == n2}
          ()
    :<prf> [m1 * n1 == m2 * n2]
           void =
  let
    prval pf1 = mul_make {m1, n1} ()
    prval pf2 = mul_make {m2, n2} ()
    prval () = mul_isfun {m1, n1} {m1 * n1, m2 * n2} (pf1, pf2)
  in
  end

extern praxi
array_v_takeout2 :     (* Get views for two distinct array elements.*)
  {a     : vt@ype}
  {p     : addr}
  {n     : int}
  {i, j  : nat | i < n; j < n; i != j}
  array_v (a, p, n) -<prf>
    @(a @ p + (i * sizeof a),
      a @ p + (j * sizeof a),
      (a @ p + (i * sizeof a),
       a @ p + (j * sizeof a)) -<prf,lin>
        array_v (a, p, n))

extern praxi
discard_used_contents :
  {a : vt@ype}
  {p : addr}
  {n : int}
  array_v (a?!, p, n) -<prf> array_v (a?, p, n)

extern fn
g1uint_mod_uint64 :
  {x, y : int}
  (uint64 x, uint64 y) -<> uint64 (x mod y) = "mac#%"

implement
g1uint_mod<uint64_kind> (x, y) =
  g1uint_mod_uint64 (x, y)

(*------------------------------------------------------------------*)
(* A simple linear congruential generator, for pivot selection.     *)

%{
ats2_stable_quicksort_spinlock_t ats2_stable_quicksort_seed_lock;
uint64_t ats2_stable_quicksort_seed = UINT64_C (0x1234567891234567);
%}

extern fn
random_uint64 () :<!wrt> uint64 = "mac#%"

(*------------------------------------------------------------------*)
(* A list with a pointer to its last node.                          *)

absvt@ype extensible_list_vt (a : vt@ype+, p : addr, n : int) =
  @(list_vt (a, n), ptr p, int n)
vtypedef extensible_list_vt (a : vt@ype+, n : int) =
  [p : addr] extensible_list_vt (a, p, n)
vtypedef extensible_list_vt (a : vt@ype+) =
  [n : int] extensible_list_vt (a, n)

fn {a : vt@ype}
unsafe_list_vt2extensible
          {n      : nat}
          {p      : addr}
          (lst    : list_vt (a, n),
           p_last : ptr p,
           n      : int n)
    :<> extensible_list_vt (a, p, n) =
  $UN.castvwtp0 @(lst, p_last, n)

fn {a : vt@ype}
extensible2list_vt
          {n       : nat}
          {p       : addr}
          (elst    : extensible_list_vt (a, p, n))
    :<> @(list_vt (a, n), ptr p, int n) =
  $UN.castvwtp0 elst

fn {a : vt@ype}
extensible_list_vt_nil ()
    :<> extensible_list_vt (a, 0) =
  unsafe_list_vt2extensible<a> (NIL, the_null_ptr, 0)

fn {a : vt@ype}
extensible_list_vt_finalize
          {n    : nat}
          (elst : extensible_list_vt (a, n))
    :<!wrt> @(list_vt (a, n), int n) =
  let
    val @(ls, _, n) = extensible2list_vt<a> elst
  in
    @(ls, n)
  end

fn {a : vt@ype}
extensible_list_vt_append
          {n1, n2 : nat}
          (elst1  : extensible_list_vt (a, n1),
           elst2  : extensible_list_vt (a, n2))
    :<!wrt> extensible_list_vt (a, n1 + n2) =
  let
    val @(ls1, p1, n1) = extensible2list_vt<a> elst1
  in
    if n1 = 0 then
      let
        val+ ~ NIL = ls1
      in
        elst2
      end
    else
      let
        val @(ls2, p2, n2) = extensible2list_vt<a> elst2
      in
        if n2 = 0 then
          let
            val+ ~ NIL = ls2
          in
            unsafe_list_vt2extensible<a> (ls1, p1, n1)
          end
        else
          let
            val last_node = $UN.castvwtp0{list_vt (a, 1)} p1
            val+ @ (_ :: tail) = last_node
            val+ ~ NIL = tail
            val () = tail := ls2
            prval () = fold@ last_node
            prval () = $UN.castvwtp0{void} last_node
          in
            unsafe_list_vt2extensible<a>
              ($UN.castvwtp0{list_vt (a, n1 + n2)} ls1,
               p2, n1 + n2)
          end
      end
  end

(*------------------------------------------------------------------*)
(* An insertion sort for small sublists.                            *)

(* Inserting in reverse order minimizes the work for a list already
   nearly sorted, or for stably sorting a list whose entries often
   have equal keys. It also makes the last node easy to find. *)
fun {a : vt@ype}
list_vt_insert_reverse
          {m       : nat}
          {p_xnode : addr}
          {p_x     : addr}
          {p_xs    : addr}
          .<m>.
          (pf_x  : a @ p_x,
           pf_xs : list_vt (a, 0)? @ p_xs |
           dst   : &list_vt (a, m) >> list_vt (a, m + 1),
           xnode : list_vt_cons_unfold (p_xnode, p_x, p_xs),
           p_x   : ptr p_x,
           p_xs  : ptr p_xs)
    :<!wrt> void =
  (* dst is some tail of the current (reverse-order) destination list.
     xnode is the current node in the source list.
     p_x points to the node's CAR.
     p_xs points to the node's CDR. *)
  case+ dst of
  | @ (y :: ys) =>
    if list_vt_stable_quicksort$lt<a> (!p_x, y) then
      let                     (* Move to the next destination node. *)
        val () =
          list_vt_insert_reverse (pf_x, pf_xs | ys, xnode, p_x, p_xs)
        prval () = fold@ dst
      in
      end
    else
      let                       (* Insert xnode here. *)
        prval () = fold@ dst
        val () = !p_xs := dst
        val () = dst := xnode
        prval () = fold@ dst
      in
      end
  | ~ NIL =>
    let                         (* Put xnode at the end. *)
      val () = dst := xnode
      val () = !p_xs := NIL
      prval () = fold@ dst
    in
    end

(* An insertion sort that accepts a prefix of data already sorted in
   reverse. *)
fn {a : vt@ype}
list_vt_insertion_sort
          {m, n            : int}
          (lst             : list_vt (INV(a), m),
           m               : int m,
           reversed_prefix : list_vt (INV(a), n),
           n               : int n)
    :<!wrt> extensible_list_vt (a, m + n) =
  let
    fun                         (* Create a list sorted in reverse. *)
    loop {m, n : nat}
         .<m>.
         (src : list_vt (a, m),
          dst : &list_vt (a, n) >> list_vt (a, m + n))
        :<!wrt> void =
      case+ src of
      | @ (x :: xs) =>
        let
          val tail = xs
        in
          list_vt_insert_reverse<a>
            (view@ x, view@ xs | dst, src, addr@ x, addr@ xs);
          loop (tail, dst)
        end
      | ~ NIL => ()             (* We are done. *)

    prval () = lemma_list_vt_param lst
    prval () = lemma_list_vt_param reversed_prefix
  in
    if m + n = 0 then
      let
        val+ ~ NIL = lst
        val+ ~ NIL = reversed_prefix
      in
        extensible_list_vt_nil<a> ()
      end
    else
      let
        var dst : list_vt (a, n) = reversed_prefix
        val () = loop (lst, dst)
        val p_last = $UN.castvwtp1{Ptr} dst
      in
        unsafe_list_vt2extensible (list_vt_reverse<a> dst, p_last,
                                   m + n)
      end
  end

(*------------------------------------------------------------------*)

implement {a}
list_vt_stable_quicksort$lt (x, y) =
  list_vt_stable_quicksort$cmp<a> (x, y) < 0

implement {a}
list_vt_stable_quicksort$cmp (x, y) =
  (* This default is the same as for list_vt_mergesort$cmp in the
     prelude. *)
  gcompare_ref_ref<a> (x, y)

implement {a}
list_vt_stable_quicksort$small () =
  DEFAULT_LIST_INSERTION_SORT_THRESHOLD

implement {a}
list_vt_stable_quicksort$pivot_index (lst, m) =
  list_vt_stable_quicksort_pivot_index_default<a> (lst, m)
 
implement {a}
list_vt_stable_quicksort_pivot_index_default (lst, n) =
  list_vt_stable_quicksort_pivot_index_random<a> (lst, n)
 
implement {a}
list_vt_stable_quicksort_pivot_index_random {m, n} (lst, m) =
  let
    val u64_m = $UN.cast{uint64 n} m
    val u64_rand : [i : nat] uint64 i =
      g1ofg0 ($effmask_wrt random_uint64 ())
    val u64_pivot = g1uint_mod (u64_rand, u64_m)
    val i_pivot = $UN.cast{[i : nat | i < m] int i} u64_pivot
  in
    i_pivot
  end
 
implement {a}
list_vt_stable_quicksort_pivot_index_middle (lst, m) =
  half m
 
implement {a}
list_vt_stable_quicksort_pivot_index_first (lst, m) =
  0

extern fn {a : vt@ype}
compare_with_pivot$le
          (x     : &a,
           pivot : &a)
    :<> bool

fn {a : vt@ype}
compare_head_with_pivot
          {n     : pos}
          (lst   : &list_vt (a, n),
           pivot : &a)
    :<> Bool =
  let
    val+ @ (head :: _) = lst
    val is_le = compare_with_pivot$le<a> (head, pivot)
    prval () = fold@ lst
  in
    g1ofg0 is_le
  end

fn {a : vt@ype}
list_vt_select_pivot
          {n   : pos}
          (lst : list_vt (a, n),
           n   : int n)
    :<!wrt> [n_before, n_after : nat | n_before + 1 + n_after == n]
            @(list_vt (a, n_before),
              list_vt (a, 1),
              list_vt (a, n_after),
              int n_before,
              int n_after) =
  let
    val i_pivot = list_vt_stable_quicksort$pivot_index<a> (lst, n)
    val @(left, right) = list_vt_split_at<a> (lst, i_pivot)
    val @(pivot, right) = list_vt_split_at<a> (right, 1)
  in
    @(left, pivot, right, i_pivot, pred (n - i_pivot))
  end

fn {a : vt@ype}
split_after_run
          {n     : pos}
          (lst   : list_vt (a, n),
           n     : int n,
           pivot : &a,
           sense : Bool)
    :<!wrt> [n1, n2 : int | 1 <= n1; 0 <= n2; n1 + n2 == n]
            @(extensible_list_vt (a, n1),
              list_vt (a, n2),
              int n2,
              Bool) =
  let
    fun
    loop {m : pos}
         .<m>.
         (lst1  : &list_vt (a, m) >> list_vt (a, m1),
          lst2  : &(List_vt a)? >> list_vt (a, m2),
          pivot : &a,
          m     : int m)
        :<!wrt> #[m1, m2 : int | 1 <= m1; 0 <= m2; m1 + m2 == m]
                @(int m2, Ptr, Bool) =
      let
        val+ @ (head :: tail) = lst1
      in
        case+ tail of
        | NIL =>
          let
            val () = lst2 := NIL
            prval () = fold@ lst1
            val p_last = $UN.castvwtp1{Ptr} lst1
            val arbitrary_sense = false
          in
            @(0, p_last, arbitrary_sense)
          end
        | _ :: _ =>
          let
            val new_sense = compare_head_with_pivot<a> (tail, pivot)
          in
            if new_sense = sense then
              let
                val retval = loop (tail, lst2, pivot, pred m)
                prval () = fold@ lst1
              in
                retval
              end
            else
              let
                val () = lst2 := tail
                val () = tail := NIL
                prval () = fold@ lst1
                val p_last = $UN.castvwtp1{Ptr} lst1
              in
                @(pred m, p_last, new_sense)
              end
          end
      end

    var lst1 = lst
    var lst2 : List_vt a
    val @(n2, p_last, new_sense) = loop (lst1, lst2, pivot, n)
    val elst1 = unsafe_list_vt2extensible (lst1, p_last, n - n2)
  in
    @(elst1, lst2, n2, new_sense)
  end

fn {a : vt@ype}
partition_pivot_free_list
          {n     : nat}
          (lst   : list_vt (a, n),
           n     : int n,
           pivot : &a)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n]
            @(extensible_list_vt (a, n_le),
              extensible_list_vt (a, n_ge)) =
  let
    fun
    loop {m1 : nat | m1 <= n}
         {n1, n2 : nat | m1 + n1 + n2 == n}
         .<m1>.
         (lst1    : list_vt (a, m1),
          m1      : int m1,
          pivot   : &a,
          sense   : Bool,
          elst_le : extensible_list_vt (a, n1),
          elst_ge : extensible_list_vt (a, n2))
        :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n]
                @(extensible_list_vt (a, n_le),
                  extensible_list_vt (a, n_ge)) =
      case+ lst1 of
      | ~ NIL => @(elst_le, elst_ge)
      | _ :: _ =>
        let
          macdef appd = extensible_list_vt_append<a>
          val @(elst, lst2, m2, new_sense) =
            split_after_run<a> (lst1, m1, pivot, sense)
        in
          case+ sense of
          | true =>
            let
              val elst_le = (elst_le \appd elst)
            in
              loop (lst2, m2, pivot, new_sense, elst_le, elst_ge)
            end
          | false =>
            let
              val elst_ge = (elst_ge \appd elst)
            in
              loop (lst2, m2, pivot, new_sense, elst_le, elst_ge)
            end
        end
  in
    case+ lst of
    | ~ NIL =>
      @(extensible_list_vt_nil<a> (),
        extensible_list_vt_nil<a> ())
    | _ :: _ =>
      let
        var lst = lst
        val sense = compare_head_with_pivot<a> (lst, pivot)
      in
        loop (lst, n, pivot, sense,
              extensible_list_vt_nil<a> (),
              extensible_list_vt_nil<a> ())
      end
  end

fn {a : vt@ype}
partition_list
          {n     : pos}
          (lst   : list_vt (a, n),
           n     : int n)
    :<!wrt> [n_le, n_ge : nat | n_le + 1 + n_ge == n]
            @(extensible_list_vt (a, n_le),
              extensible_list_vt (a, 1), (* The pivot. *)
              extensible_list_vt (a, n_ge)) =
  let
    macdef appd = extensible_list_vt_append<a>

    val @(lst_before, lst_pivot, lst_after, n_before, n_after) =
      list_vt_select_pivot<a> (lst, n)

    var lst_pivot = lst_pivot
    val+ @ (pivot :: _) = lst_pivot

    implement
    compare_with_pivot$le<a> (x, pivot) =
      ~list_vt_stable_quicksort$lt<a> (pivot, x)
    val @(elst1_le, elst1_ge) =
      partition_pivot_free_list<a> (lst_before, n_before, pivot)

    implement
    compare_with_pivot$le<a> (x, pivot) =
      list_vt_stable_quicksort$lt<a> (x, pivot)
    val @(elst2_le, elst2_ge) =
      partition_pivot_free_list<a> (lst_after, n_after, pivot)

    prval () = fold@ lst_pivot

    val p_pivot = $UN.castvwtp1{Ptr} lst_pivot
    val elst_pivot =
      unsafe_list_vt2extensible<a> (lst_pivot, p_pivot, 1)
    and elst_le = (elst1_le \appd elst2_le)
    and elst_ge = (elst1_ge \appd elst2_ge)
  in
    @(elst_le, elst_pivot, elst_ge)
  end

implement {a}
list_vt_stable_quicksort lst =
  let
    macdef finalize = extensible_list_vt_finalize<a>
    macdef appd = extensible_list_vt_append<a>

    fun
    recurs {m : nat}
           .<m>.
           (lst : list_vt (a, m),
            m   : int m)
        :<!wrt> extensible_list_vt (a, m) =
      if list_vt_stable_quicksort$small () < m then
        let
          val @(elst_le, elst_eq, elst_ge) =
            partition_list<a> (lst, m)
          val @(lst1, m1) = finalize elst_le
          and @(lst2, m2) = finalize elst_ge
          val elst1 = recurs (lst1, m1)
          and elst2 = recurs (lst2, m2)
        in
          ((elst1 \appd elst_eq) \appd elst2)
        end
      else if m <> 0 then
        list_vt_insertion_sort<a> (lst, m, NIL, 0)
      else
        unsafe_list_vt2extensible<a> (lst, the_null_ptr, 0)

    prval () = lemma_list_vt_param lst
    val @(lst_sorted, _) = finalize (recurs (lst, length lst))
  in
    lst_sorted
  end

(*------------------------------------------------------------------*)
(* An implementation for non-linear lists, in terms of the
   implementation for linear lists. *)

implement {a}
list_stable_quicksort$lt (x, y) =
  list_stable_quicksort$cmp<a> (x, y) < 0

implement {a}
list_stable_quicksort$cmp (x, y) =
  gcompare_val_val<a> (x, y)

implement {a}
list_stable_quicksort lst =
  let
    implement
    list_vt_stable_quicksort$lt<a> (x, y) =
      list_stable_quicksort$lt<a> (x, y)
  in
    list_vt_stable_quicksort<a> (list_copy<a> lst)
  end

(*------------------------------------------------------------------*)

fn {a : vt@ype}
array_element_lt
          {n    : int}
          {i, j : nat | i < n; j < n; i != j}
          (arr  : &array (a, n),
           i    : size_t i,
           j    : size_t j)
    :<> bool =
  let
    prval @(pf_i, pf_j, fpf) =
      array_v_takeout2 {a} {..} {n} {i, j} (view@ arr)
    val is_lt =
      array_stable_quicksort$lt<a> (!(ptr_add<a> (addr@ arr, i)),
                                    !(ptr_add<a> (addr@ arr, j)))
    prval () = view@ arr := fpf (pf_i, pf_j)
  in
    is_lt
  end

implement {a}
array_stable_quicksort$lt (x, y) =
  array_stable_quicksort$cmp<a> (x, y) < 0

implement {a}
array_stable_quicksort$cmp (x, y) =
  (* This default is the same as for array_quicksort$cmp in the
     prelude. *)
  gcompare_ref_ref<a> (x, y)

implement {a}
array_stable_quicksort$small () =
  i2sz DEFAULT_ARRAY_INSERTION_SORT_THRESHOLD

implement {a}
array_stable_quicksort$pivot_index {n} (arr, n) =
  array_stable_quicksort_pivot_index_default<a> {n} (arr, n)

implement {a}
array_stable_quicksort_pivot_index_default {n} (arr, n) =
  (* The default is random pivot, which I _highly_ recommend. *)
  array_stable_quicksort_pivot_index_random<a> {n} (arr, n)

implement {a}
array_stable_quicksort_pivot_index_random {n} (arr, n) =
  let
    val u64_n = $UN.cast{uint64 n} n
    val u64_rand : [i : nat] uint64 i =
      g1ofg0 ($effmask_wrt random_uint64 ())
    val u64_pivot = g1uint_mod (u64_rand, u64_n)
    val i_pivot = $UN.cast{[i : nat | i < n] size_t i} u64_pivot
  in
    i_pivot
  end

implement {a}
array_stable_quicksort_pivot_index_middle (arr, n) =
  half n

implement {a}
array_stable_quicksort_pivot_index_median_of_three {n} (arr, n) =
  if n <= 2 then
    i2sz 0
  else
    let
      val i_first = i2sz 0
      and i_middle = half n
      and i_last = pred n

      val middle_lt_first =
        array_element_lt<a> {n} (arr, i_middle, i_first)
      and last_lt_first =
        array_element_lt<a> {n} (arr, i_last, i_first)
    in
      if middle_lt_first <> last_lt_first then
        i_first
      else
        let
          val middle_lt_last =
            array_element_lt<a> {n} (arr, i_middle, i_last)
        in
          if middle_lt_first <> middle_lt_last then
            i_middle
          else
            i_last
        end
    end

fn {a : vt@ype}
insertion_position
          {n      : int}
          {i      : pos | i < n}
          {p_arr  : addr}
          (pf_arr : !array_v (a, p_arr, n) >> _ |
           p_arr  : ptr p_arr,
           i      : size_t i)
    :<> [j : nat | j <= i]
        size_t j =
  let
    fun
    loop {k1 : nat | k1 <= i}
         .<k1>.
         (pf_arr : !array_v (a, p_arr, n) >> _ |
          k1     : size_t k1)
        :<> [j : nat | j <= i]
            size_t j =
      if k1 = i2sz 0 then
        k1
      else
        let
          val k = pred k1
        in
          if array_element_lt<a> {n} (!p_arr, i, k) then
            loop (pf_arr | k)
          else
            k1
        end
  in
    loop (pf_arr | i)
  end

fn {a : vt@ype}
array_insertion_sort
          {n       : nat}
          {p_arr   : addr}
          (pf_arr  : !array_v (a, p_arr, n) >> _ |
           p_arr   : ptr p_arr,
           n       : size_t n)
    :<!wrt> void =
  if n > 1 then
    let
      fun
      loop {i : pos | i <= n}
           .<n - i>.
           (pf_arr : !array_v (a, p_arr, n) >> _ |
            i      : size_t i)
          :<!wrt> void =
        if i <> n then
          let
            val j = insertion_position<a> {n} (pf_arr | p_arr, i)
          in
            array_subcirculate<a> (!p_arr, j, i);
            loop (pf_arr | succ i)
          end
    in
      loop (pf_arr | i2sz 1)
    end

fn {a : vt@ype}
array_select_pivot
          {n      : pos}
          {p_arr  : addr}
          (pf_arr : array_v (a, p_arr, n) |
           p_arr  : ptr p_arr,
           n      : size_t n)
    :<!wrt> [n_before : nat | n_before + 1 <= n]
            @(array_v (a, p_arr, n_before),
              a @ (p_arr + (n_before * sizeof a)),
              array_v (a, p_arr + (n_before * sizeof a) + sizeof a,
                       n - n_before - 1) |
              size_t n_before) =
  let
    val [n_before : int] n_before =
      array_stable_quicksort$pivot_index<a> (!p_arr, n)
    prval @(pf_before, pf_more) =
      array_v_split {a} {p_arr} {n} {n_before} pf_arr
    prval @(pf_pivot, pf_after) = array_v_uncons pf_more
  in
    @(pf_before, pf_pivot, pf_after | n_before)
  end

fn {a : vt@ype}
partition_array_before_pivot
          {n          : pos}
          {n_before   : nat | n_before + 1 <= n}
          {p_arr      : addr}
          {p_work     : addr}
          {p_pivot    : addr}
          (pf_before  : array_v (a, p_arr, n_before),
           pf_work   : array_v (a?, p_work, n),
           pf_pivot  : !(a @ p_pivot) |
           p_arr     : ptr p_arr,
           p_work    : ptr p_work,
           p_pivot   : ptr p_pivot,
           n_before  : size_t n_before)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n_before]
            @(array_v (a, p_arr, n_le),
              array_v (a?!, p_arr + (n_le * sizeof a),
                       n_before - n_le),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
              size_t n_le,
              size_t n_ge) =
  let
    fun
    loop {i : nat | i <= n_before}
         {n0_le, n0_ge : nat | n0_le + n0_ge == i}
         .<n_before - i>.
         (pf_le      : array_v (a, p_arr, n0_le),
          pf_between : array_v (a?!, p_arr + (n0_le * sizeof a),
                                i - n0_le),
          pf_before  : array_v (a, p_arr + (i * sizeof a),
                                n_before - i),
          pf_ge      : array_v (a, p_work, n0_ge),
          pf_work    : array_v (a?, p_work + (n0_ge * sizeof a),
                                n - n0_ge),
          pf_pivot   : !(a @ p_pivot) |
          i          : size_t i,
          n0_le      : size_t n0_le,
          n0_ge      : size_t n0_ge)
        :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n_before]
                @(array_v (a, p_arr, n_le),
                  array_v (a?!, p_arr + (n_le * sizeof a),
                           n_before - n_le),
                  array_v (a, p_work, n_ge),
                  array_v (a?, p_work + (n_ge * sizeof a),
                           n - n_ge) |
                  size_t n_le,
                  size_t n_ge) =
      if i = n_before then
        let
          prval () = array_v_unnil pf_before
        in
          @(pf_le, pf_between, pf_ge, pf_work | n0_le, n0_ge)
        end
      else
        let
          prval @(pf_src, pf_before) = array_v_uncons pf_before
          val p_src = ptr_add<a> (p_arr, i)
        in
          (* Move anything <= the pivot to the beginning of the array,
             and anything else to the workspace array. *)
          if array_stable_quicksort$lt<a> (!p_pivot, !p_src) then
            let          (* The element is > the pivot. Move it to the
                            workspace array. *)
              prval @(pf_dst, pf_work) = array_v_uncons pf_work
              val () =
                ptr_set<a> (pf_dst | ptr_add<a> (p_work, n0_ge),
                                     ptr_get<a> (pf_src | p_src))
              prval pf_ge = array_v_extend (pf_ge, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_le, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, n0_le, succ n0_ge)
            end
          else if i = n0_le then
            let   (* The element is <= to the pivot and already in the
                     correct place. *)
              prval () = lemma_mul_isfun {i, sizeof a}
                                         {n0_le, sizeof a} ()
              prval pf_between = array_v_unnil_nil{a?!, a} pf_between
              prval pf_between = array_v_extend (pf_between, pf_src)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              prval pf_le = array_v_extend (pf_le, pf_dst)
              prval pf_between = array_v_unnil_nil{a, a?!} pf_between
            in
              loop (pf_le, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, succ n0_le, n0_ge)
            end
          else
            let     (* The element is <= but not in the correct place.
                       Move it earlier in the same array. *)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              val p_dst = ptr_add<a> (p_arr, n0_le)
              val () =
                ptr_set<a>
                  (pf_dst | p_dst, ptr_get<a> (pf_src | p_src))
              prval pf_le = array_v_extend (pf_le, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_le, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, succ n0_le, n0_ge)
            end
        end

    prval pf_le = array_v_nil {a} {p_arr} ()
    prval pf_ge = array_v_nil {a} {p_work} ()
    prval pf_between = array_v_nil {a?!} {p_arr} ()
  in
    loop (pf_le, pf_between, pf_before,
          pf_ge, pf_work, pf_pivot |
          i2sz 0, i2sz 0, i2sz 0)
  end

fn {a : vt@ype}
partition_array_after_pivot
          {n          : pos}
          {n_before   : nat | n_before + 1 <= n}
          {n0_le      : nat}
          {n0_ge      : nat | n0_le + n0_ge == n_before}
          {p_arr      : addr}
          {p_work     : addr}
          {p_pivot    : addr}
          (pf_le      : array_v (a, p_arr, n0_le),
           pf_between : array_v (a?!, p_arr + (n0_le * sizeof a),
                                 n_before - n0_le + 1),
           pf_after   : array_v
                          (a,
                           p_arr + (n_before * sizeof a) + sizeof a,
                           n - n_before - 1),
           pf_ge      : array_v (a, p_work, n0_ge),
           pf_work    : array_v (a?, p_work + (n0_ge * sizeof a),
                                 n - n0_ge),
           pf_pivot   : !(a @ p_pivot) |
           p_arr      : ptr p_arr,
           p_work     : ptr p_work,
           p_pivot    : ptr p_pivot,
           n          : size_t n,
           n0_le      : size_t n0_le,
           n0_ge      : size_t n0_ge)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge + 1 == n]
            @(array_v (a, p_arr, n_le),
              array_v (a?!, p_arr + (n_le * sizeof a), n - n_le),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
              size_t n_le,
              size_t n_ge) =
  let
    fun
    loop {n1_le      : nat}
         {n1_ge      : nat | n0_ge <= n1_ge}
         {i          : int | n_before + 1 <= i; i <= n;
                             n1_le + n1_ge + 1 == i}
         .<n - i>.
         (pf_le      : array_v (a, p_arr, n1_le),
          pf_between : array_v (a?!, p_arr + (n1_le * sizeof a),
                                i - n1_le),
          pf_after   : array_v (a, p_arr + (i * sizeof a), n - i),
          pf_ge      : array_v (a, p_work, n1_ge),
          pf_work    : array_v (a?, p_work + (n1_ge * sizeof a),
                                n - n1_ge),
          pf_pivot   : !(a @ p_pivot) |
          i          : size_t i,
          n1_le      : size_t n1_le,
          n1_ge      : size_t n1_ge)
        :<!wrt> [n_le, n_ge : nat | n_le + n_ge + 1 == n]
                @(array_v (a, p_arr, n_le),
                  array_v (a?!, p_arr + (n_le * sizeof a), n - n_le),
                  array_v (a, p_work, n_ge),
                  array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
                  size_t n_le,
                  size_t n_ge) =
      if i = n then
        let
          prval () = array_v_unnil pf_after
        in
          @(pf_le, pf_between, pf_ge, pf_work | n1_le, n1_ge)
        end
      else
        let
          prval @(pf_src, pf_after) = array_v_uncons pf_after
          val p_src = ptr_add<a> (p_arr, i)
        in
          (* Move anything < the pivot to the beginning of the array,
             and anything else to the workspace array. *)
          if ~array_stable_quicksort$lt<a> (!p_src, !p_pivot) then
            let         (* The element is >= the pivot. Move it to the
                           workspace array. *)
              prval @(pf_dst, pf_work) = array_v_uncons pf_work
              val () =
                ptr_set<a> (pf_dst | ptr_add<a> (p_work, n1_ge),
                                     ptr_get<a> (pf_src | p_src))
              prval pf_ge = array_v_extend (pf_ge, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_le, pf_between, pf_after,
                    pf_ge, pf_work, pf_pivot |
                    succ i, n1_le, succ n1_ge)
            end
          else
            let  (* The element is < the pivot. Move it earlier in the
                    same array. *)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              val () =
                ptr_set<a> (pf_dst | ptr_add<a> (p_arr, n1_le),
                                     ptr_get<a> (pf_src | p_src))
              prval pf_le = array_v_extend (pf_le, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_le, pf_between, pf_after,
                    pf_ge, pf_work, pf_pivot |
                    succ i, succ n1_le, n1_ge)
            end
        end

    prval () = lemma_mul_isfun {n_before + 1, sizeof a}
                               {n0_le + n0_ge + 1, sizeof a} ()
  in
    loop (pf_le, pf_between, pf_after,
          pf_ge, pf_work, pf_pivot |
          succ (n0_le + n0_ge), n0_le, n0_ge)
  end

fn {a : vt@ype}
partition_array_after_pivot_removal
          {n          : pos}
          {n_before   : nat | n_before + 1 <= n}
          {p_arr      : addr}
          {p_work     : addr}
          {p_pivot    : addr}
          (pf_before  : array_v (a, p_arr, n_before),
           pf_emptied : a?! @ (p_arr + (n_before * sizeof a)),
           pf_after   : array_v
                          (a,
                           p_arr + (n_before * sizeof a) + sizeof a,
                           n - n_before - 1),
           pf_work   : array_v (a?, p_work, n),
           pf_pivot  : !(a @ p_pivot) |
           p_arr     : ptr p_arr,
           p_work    : ptr p_work,
           p_pivot   : ptr p_pivot,
           n         : size_t n,
           n_before  : size_t n_before)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge + 1 == n]
            @(array_v (a, p_arr, n_le),
              array_v (a?!, p_arr + (n_le * sizeof a), n - n_le),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
              size_t n_le,
              size_t n_ge) =
  let
    val @(pf_le, pf_between, pf_ge, pf_work | n_le, n_ge) =
      partition_array_before_pivot<a>
        (pf_before, pf_work, pf_pivot |
         p_arr, p_work, p_pivot, n_before)
    prval pf_between = array_v_extend (pf_between, pf_emptied)
  in
    partition_array_after_pivot<a>
      {n} {n_before}
      (pf_le, pf_between, pf_after, pf_ge, pf_work, pf_pivot |
       p_arr, p_work, p_pivot, n, n_le, n_ge)
  end

fn {a : vt@ype}
select_pivot_and_partition_array
          {n         : pos}
          {p_arr     : addr}
          {p_work    : addr}
          (pf_arr    : array_v (a, p_arr, n),
           pf_work   : array_v (a?, p_work, n) |
           p_arr     : ptr p_arr,
           p_work    : ptr p_work,
           n         : size_t n)
    :<!wrt> [n_le : nat | n_le + 1 <= n]
            @(array_v (a, p_arr, n_le),
              a @ (p_arr + (n_le * sizeof a)),
              array_v (a, p_arr + (n_le * sizeof a) + sizeof a,
                       n - n_le - 1),
              array_v (a?, p_work, n) |
              size_t n_le) =
  let
    (* Split the array at a pivot. *)
    val @(pf_before, pf_pivot_entry, pf_after | n_before) =
      array_select_pivot<a> (pf_arr | p_arr, n)

    (* Remove the pivot from the array. Move it to the stack frame. *)
    var pivot =
      ptr_get<a> (pf_pivot_entry | ptr_add<a> (p_arr, n_before))

    (* Partition into stuff <= the pivot in the original array, and
       stuff >= the pivot in the workspace array. *)
    val [n_le : int, n_ge : int]
        @(pf_le, pf_after_le, pf_ge, pf_after_ge | n_le, n_ge) =
      partition_array_after_pivot_removal<a>
        (pf_before, pf_pivot_entry, pf_after, pf_work, view@ pivot |
         p_arr, p_work, addr@ pivot, n, n_before)

    (* Move the pivot, and the stuff that is now in the workspace
       array, back into the original array. *)
    prval @(pf_pivot_entry1, pf_ge1) = array_v_uncons pf_after_le
    val p_pivot_entry1 = ptr_add<a> (p_arr, n_le)
    val p_ge1 = ptr1_succ<a> p_pivot_entry1
    val () = ptr_set<a> (pf_pivot_entry1 | p_pivot_entry1, pivot)
    val () = array_copy<a> (!p_ge1, !p_work, n_ge)

    (* Restore the view of the workspace array. *)
    prval pf_ge = discard_used_contents {a} pf_ge
    prval () = lemma_mul_isfun {n - n_le - 1, sizeof a}
                               {n_ge, sizeof a} ()
    prval pf_work = array_v_unsplit (pf_ge, pf_after_ge)
  in
    @(pf_le, pf_pivot_entry1, pf_ge1, pf_work | n_le)
  end

implement {a}
array_stable_quicksort_given_workspace {n} (arr, n, workspace) =
  if n = 0 then
    ()
  else
    let
      fun
      recurs {n1      : nat | n1 <= n}
             {p_arr1  : addr}
             {p_work  : addr}
             .<n1>.
             (pf_arr1 : !array_v (a, p_arr1, n1) >> _,
              pf_work : !array_v (a?, p_work, n) >> _ |
              p_arr1  : ptr p_arr1,
              p_work  : ptr p_work,
              n1      : size_t n1)
          :<!wrt> void =
        if n1 <= array_stable_quicksort$small<a> () then
          array_insertion_sort<a> (pf_arr1 | p_arr1, n1)
        else
          let
            prval @(pf_work1, pf_not_used) =
              array_v_split {a?} {..} {n} {n1} pf_work

            val [n1_le : int]
                @(pf_le, pf_pivot, pf_ge, pf_work1 | n1_le) =
              select_pivot_and_partition_array<a>
                (pf_arr1, pf_work1 | p_arr1, p_work, n1)

            prval () = pf_work :=
              array_v_unsplit (pf_work1, pf_not_used)

            val p_le = p_arr1
            and p_ge = ptr_add<a> (p_arr1, succ n1_le)
            and n1_ge = n1 - succ n1_le
          in
            (* Handle the smaller side of the partition first, to
               reduce stack blowup. The larger side of the partition
               is handled by a tail recursion. *)
            if n1_le < n1_ge then
              let
                val () = recurs (pf_le, pf_work | p_le, p_work, n1_le)
                val () = recurs (pf_ge, pf_work | p_ge, p_work, n1_ge)
                prval () = pf_arr1 := array_v_extend (pf_le, pf_pivot)
                prval () = pf_arr1 := array_v_unsplit (pf_arr1, pf_ge)
              in
              end
            else
              let
                val () = recurs (pf_ge, pf_work | p_ge, p_work, n1_ge)
                val () = recurs (pf_le, pf_work | p_le, p_work, n1_le)
                prval () = pf_arr1 := array_v_extend (pf_le, pf_pivot)
                prval () = pf_arr1 := array_v_unsplit (pf_arr1, pf_ge)
              in
              end
          end

      prval () = lemma_array_param arr
    in
      recurs (view@ arr, view@ workspace |
              addr@ arr, addr@ workspace, n)
    end

implement {a}
array_stable_quicksort_not_given_workspace {n} (arr, n) =
  let
    fn
    quicksort {n         : int}
              (arr       : &array (a, n),
               n         : size_t n,
               workspace : &array (a?, n))
        :<!wrt> void =
      array_stable_quicksort_given_workspace<a> (arr, n, workspace)

    prval () = lemma_array_param arr
  in
    if n <= ARRAY_STACK_STORAGE_THRESHOLD then
      let
        var storage : @[a?][ARRAY_STACK_STORAGE_THRESHOLD]

        prval @(pf_work, pf_rest) =
          array_v_split {a?} {..} {ARRAY_STACK_STORAGE_THRESHOLD} {n}
                        (view@ storage)
        val () = quicksort (arr, n, !(addr@ storage))
        prval () = view@ storage := array_v_unsplit (pf_work, pf_rest)
      in
      end
    else
      let
        val @(pf_work, pfgc_work | p_work) = array_ptr_alloc<a?> n
        val () = quicksort (arr, n, !p_work)
        val () = array_ptr_free (pf_work, pfgc_work | p_work)
      in
      end
  end

(*------------------------------------------------------------------*)
