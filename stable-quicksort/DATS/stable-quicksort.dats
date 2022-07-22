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

#define INSERTION_SORT_THRESHOLD 32

#define NIL list_vt_nil ()
#define ::  list_vt_cons

typedef sign_t (i : int) = [~1 <= i && i <= 1] int i
typedef sign_t = [i : int] sign_t i

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
    if list_vt_stable_quicksort$cmp<a> (!p_x, y) < 0 then
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
list_vt_stable_quicksort_pivot_index_random {n} (lst, n) =
  let
    val u64_n = $UN.cast{uint64 n} n
    val u64_rand : [i : nat] uint64 i = g1ofg0 (random_uint64 ())
    val u64_pivot = g1uint_mod (u64_rand, u64_n)
    val i_pivot = $UN.cast{[i : nat | i < n] int i} u64_pivot
  in
    i_pivot
  end

implement {a}
list_vt_stable_quicksort_pivot_index_middle (lst, n) =
  half n

implement {a}
list_vt_stable_quicksort_pivot_index_first (lst, n) =
  0

implement {a}                   (* The default is random pivot. *)
list_vt_stable_quicksort$pivot_index (lst, n) =
  list_vt_stable_quicksort_pivot_index_random (lst, n)

fn {a : vt@ype}
compare_head_with_pivot
          {n     : pos}
          (lst   : &list_vt (a, n),
           pivot : &a)
    :<> sign_t =
  let
    val+ @ (head :: _) = lst
    val sign = list_vt_stable_quicksort$cmp<a> (head, pivot)
    prval () = fold@ lst
  in
    sign
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
           sign  : sign_t)
    :<!wrt> [n1, n2 : int | 1 <= n1; 0 <= n2; n1 + n2 == n]
            @(extensible_list_vt (a, n1),
              list_vt (a, n2),
              int n2,
              sign_t) =
  let
    fun
    loop {m : pos}
         .<m>.
         (lst1  : &list_vt (a, m) >> list_vt (a, m1),
          lst2  : &(List_vt a)? >> list_vt (a, m2),
          pivot : &a,
          m     : int m)
        :<!wrt> #[m1, m2 : int | 1 <= m1; 0 <= m2; m1 + m2 == m]
                @(int m2, Ptr, sign_t) =
      let
        val+ @ (head :: tail) = lst1
      in
        case+ tail of
        | NIL =>
          let
            val () = lst2 := NIL
            prval () = fold@ lst1
            val p_last = $UN.castvwtp1{Ptr} lst1
          in
            @(0, p_last, 0)
          end
        | _ :: _ =>
          let
            val new_sign = compare_head_with_pivot<a> (tail, pivot)
          in
            if new_sign = sign then
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
                @(pred m, p_last, new_sign)
              end
          end
      end

    var lst1 = lst
    var lst2 : List_vt a
    val @(n2, p_last, new_sign) = loop (lst1, lst2, pivot, n)
    val elst1 = unsafe_list_vt2extensible (lst1, p_last, n - n2)
  in
    @(elst1, lst2, n2, new_sign)
  end

fn {a : vt@ype}
partition_pivot_free_list
          {n     : nat}
          (lst   : list_vt (a, n),
           n     : int n,
           pivot : &a)
    :<!wrt> [n_lt, n_eq, n_gt : nat | n_lt + n_eq + n_gt == n]
            @(extensible_list_vt (a, n_lt),
              extensible_list_vt (a, n_eq),
              extensible_list_vt (a, n_gt)) =
  let
    fun
    loop {m1 : nat | m1 <= n}
         {n1, n2, n3 : nat | m1 + n1 + n2 + n3 == n}
         .<m1>.
         (lst1    : list_vt (a, m1),
          m1      : int m1,
          pivot   : &a,
          sign    : sign_t,
          elst_lt : extensible_list_vt (a, n1),
          elst_eq : extensible_list_vt (a, n2),
          elst_gt : extensible_list_vt (a, n3))
        :<!wrt> [n_lt, n_eq, n_gt : nat | n_lt + n_eq + n_gt == n]
                @(extensible_list_vt (a, n_lt),
                  extensible_list_vt (a, n_eq),
                  extensible_list_vt (a, n_gt)) =
      case+ lst1 of
      | ~ NIL => @(elst_lt, elst_eq, elst_gt)
      | _ :: _ =>
        let
          macdef appd = extensible_list_vt_append<a>
          val @(elst, lst2, m2, new_sign) =
            split_after_run<a> (lst1, m1, pivot, sign)
        in
          if sign = ~1 then
            let
              val elst_lt = (elst_lt \appd elst)
            in
              loop (lst2, m2, pivot, new_sign,
                    elst_lt, elst_eq, elst_gt)
            end
          else if sign = 0 then
            let
              val elst_eq = (elst_eq \appd elst)
            in
              loop (lst2, m2, pivot, new_sign,
                    elst_lt, elst_eq, elst_gt)
            end
          else
            let
              val elst_gt = (elst_gt \appd elst)
            in
              loop (lst2, m2, pivot, new_sign,
                    elst_lt, elst_eq, elst_gt)
            end
        end
  in
    case+ lst of
    | ~ NIL =>
      @(extensible_list_vt_nil<a> (),
        extensible_list_vt_nil<a> (),
        extensible_list_vt_nil<a> ())
    | _ :: _ =>
      let
        var lst = lst
        val sign = compare_head_with_pivot<a> (lst, pivot)
      in
        loop (lst, n, pivot, sign,
              extensible_list_vt_nil<a> (),
              extensible_list_vt_nil<a> (),
              extensible_list_vt_nil<a> ())
      end
  end

fn {a : vt@ype}
partition_list
          {n     : pos}
          (lst   : list_vt (a, n),
           n     : int n)
    :<!wrt> [n_lt, n_eq, n_gt : int | 0 <= n_lt; 1 <= n_eq; 0 <= n_gt;
                                      n_lt + n_eq + n_gt == n]
            @(extensible_list_vt (a, n_lt),
              extensible_list_vt (a, n_eq),
              extensible_list_vt (a, n_gt)) =
  let
    macdef appd = extensible_list_vt_append<a>

    val @(lst_before, lst_pivot, lst_after, n_before, n_after) =
      list_vt_select_pivot<a> (lst, n)

    var lst_pivot = lst_pivot
    val+ @ (pivot :: _) = lst_pivot

    val @(elst1_lt, elst1_eq, elst1_gt) =
      partition_pivot_free_list<a> (lst_before, n_before, pivot)
    val @(elst2_lt, elst2_eq, elst2_gt) =
      partition_pivot_free_list<a> (lst_after, n_after, pivot)

    prval () = fold@ lst_pivot

    val elst_lt = (elst1_lt \appd elst2_lt)
    val p_pivot = $UN.castvwtp1{Ptr} lst_pivot
    val elst_pivot =
      unsafe_list_vt2extensible<a> (lst_pivot, p_pivot, 1)
    val elst_eq = ((elst1_eq \appd elst_pivot) \appd elst2_eq)
    val elst_gt = (elst1_gt \appd elst2_gt)
  in
    @(elst_lt, elst_eq, elst_gt)
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
      if INSERTION_SORT_THRESHOLD < m then
        let
          val @(elst_lt, elst_eq, elst_gt) =
            partition_list<a> (lst, m)
          val @(lst1, m1) = finalize elst_lt
          and @(lst2, m2) = finalize elst_gt
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

fn {a : vt@ype}
array_select_pivot
          {n      : pos}
          {p_arr  : addr}
          (pf_arr : array_v (a, p_arr, n) |
           p_arr  : ptr p_arr,
           n      : size_t n)
    :<!wrt> [n_before, n_after : nat | n_before + 1 + n_after == n]
            @(array_v (a, p_arr, n_before),
              a @ (p_arr + (n_before * sizeof a)),
              array_v (a, p_arr + (n_before * sizeof a) + sizeof a,
                       n_after) |
              ptr p_arr,
              ptr (p_arr + (n_before * sizeof a)),
              ptr (p_arr + (n_before * sizeof a) + sizeof a),
              size_t n_before,
              size_t n_after) =
  let
    val [n_before : int] n_before =
      array_stable_quicksort$pivot_index<a> (!p_arr, n)
    prval @(pf_before, pf_more) =
      array_v_split {a} {p_arr} {n} {n_before} pf_arr
    prval @(pf_pivot, pf_after) = array_v_uncons pf_more
  in
    @(pf_before, pf_pivot, pf_after |
      p_arr,
      ptr_add<a> (p_arr, n_before),
      ptr_add<a> (p_arr, succ n_before),
      n_before, n - succ n_before)
  end

fn {a : vt@ype}
partition_array_before_pivot
          {n         : pos}
          {n_before  : nat | n_before + 1 <= n}
          {p_arr     : addr}
          {p_work    : addr}
          {p_pivot   : addr}
          (pf_before : array_v (a, p_arr, n_before),
           pf_work   : array_v (a?, p_work, n),
           pf_pivot  : !(a @ p_pivot) |
           p_arr     : ptr p_arr,
           p_work    : ptr p_work,
           p_pivot   : ptr p_pivot,
           n_before  : size_t n_before)
    :<!wrt> [n_lt, n_ge : nat | n_lt + n_ge == n_before]
            @(array_v (a, p_arr, n_lt),
              array_v (a?!, p_arr + (n_lt * sizeof a),
                       n_before - n_lt),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
              size_t n_lt,
              size_t n_ge) =
  let
    fun
    loop {i : nat | i <= n_before}
         {n0_lt, n0_ge : nat | n0_lt + n0_ge == i}
         .<n_before - i>.
         (pf_lt      : array_v (a, p_arr, n0_lt),
          pf_between : array_v (a?!, p_arr + (n0_lt * sizeof a),
                                i - n0_lt),
          pf_before  : array_v (a, p_arr + (i * sizeof a),
                                n_before - i),
          pf_ge      : array_v (a, p_work, n0_ge),
          pf_work    : array_v (a?, p_work + (n0_ge * sizeof a),
                                n - n0_ge),
          pf_pivot   : !(a @ p_pivot) |
          i          : size_t i,
          n0_lt      : size_t n0_lt,
          n0_ge      : size_t n0_ge)
        :<!wrt> [n_lt, n_ge : nat | n_lt + n_ge == n_before]
                @(array_v (a, p_arr, n_lt),
                  array_v (a?!, p_arr + (n_lt * sizeof a),
                           n_before - n_lt),
                  array_v (a, p_work, n_ge),
                  array_v (a?, p_work + (n_ge * sizeof a),
                           n - n_ge) |
                  size_t n_lt,
                  size_t n_ge) =
      if i = n_before then
        let
          prval () = array_v_unnil pf_before
        in
          @(pf_lt, pf_between, pf_ge, pf_work | n0_lt, n0_ge)
        end
      else
        let
          prval @(pf_src, pf_before) = array_v_uncons pf_before
          val p_src = ptr_add<a> (p_arr, i)
          val sign = array_stable_quicksort$cmp<a> (!p_src, !p_pivot)
        in
          if 0 <= sign then
            let         (* Move the element to the workspace array. *)
              prval @(pf_dst, pf_work) =
                array_v_uncons pf_work
              val p_dst = ptr_add<a> (p_work, n0_ge)
              val () =
                ptr_set<a>
                  (pf_dst | p_dst, ptr_get<a> (pf_src | p_src))
              prval pf_ge = array_v_extend (pf_ge, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_lt, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, n0_lt, succ n0_ge)
            end
          else if i = n0_lt then
            let     (* The element is already in the correct place. *)
              prval () = lemma_mul_isfun {i, sizeof a}
                                         {n0_lt, sizeof a} ()
              prval pf_between = array_v_unnil_nil{a?!, a} pf_between
              prval pf_between = array_v_extend (pf_between, pf_src)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              prval pf_lt = array_v_extend (pf_lt, pf_dst)
              prval pf_between = array_v_unnil_nil{a, a?!} pf_between
            in
              loop (pf_lt, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, succ n0_lt, n0_ge)
            end
          else
            let      (* Move the element earlier in the same array. *)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              val p_dst = ptr_add<a> (p_arr, n0_lt)
              val () =
                ptr_set<a>
                  (pf_dst | p_dst, ptr_get<a> (pf_src | p_src))
              prval pf_lt = array_v_extend (pf_lt, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_lt, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, succ n0_lt, n0_ge)
            end
        end

    prval pf_lt = array_v_nil {a} {p_arr} ()
    prval pf_between = array_v_nil {a?!} {p_arr} ()
    prval pf_ge = array_v_nil {a} {p_work} ()
  in
    loop (pf_lt, pf_between, pf_before,
          pf_ge, pf_work, pf_pivot |
          i2sz 0, i2sz 0, i2sz 0)
  end

fn {a : vt@ype}
move_pivot {n          : pos}
           {n_lt       : nat}
           {i_pivot    : int | n_lt <= i_pivot; i_pivot < n}
           {n_ge       : nat | n_lt + n_ge + 1 <= n}
           {p_arr      : addr}
           {p_work     : addr}
           (pf_between : array_v (a?!, p_arr + (n_lt * sizeof a),
                                  i_pivot - n_lt),
            pf_pivot   : a @ p_arr + (i_pivot * sizeof a),
            pf_work    : array_v (a?, p_work + (n_ge * sizeof a),
                                  n - n_ge) |
            p_arr      : ptr p_arr,
            p_work     : ptr p_work,
            n          : size_t n,
            n_lt       : size_t n_lt,
            i_pivot    : size_t i_pivot,
            n_ge       : size_t n_ge)
    :<!wrt> @(array_v (a?!, p_arr + (n_lt * sizeof a),
                       i_pivot + 1 - n_lt),
              array_v (a?, p_work + (n_ge * sizeof a) + sizeof a,
                       n - n_ge - 1),
              a @ (p_work + (n_ge * sizeof a)) | ) =
  let
    prval @(pf_new_pivot, pf_work) = array_v_uncons pf_work
    val p_pivot = ptr_add<a> (p_arr, i_pivot)
    and p_new_pivot = ptr_add<a> (p_work, n_ge)
    val () =
      ptr_set<a>
        (pf_new_pivot | p_new_pivot, ptr_get<a> (pf_pivot | p_pivot))
    prval pf_between = array_v_extend (pf_between, pf_pivot)
  in
    @(pf_between, pf_work, pf_new_pivot | )
  end

fn {a : vt@ype}
partition_array_after_pivot
          {n          : pos}
          {n0_lt      : nat}
          {i0         : nat | n0_lt < i0; i0 <= n}
          {n0_ge      : nat | n0_lt + n0_ge + 1 == i0}
          {p_arr      : addr}
          {p_work     : addr}
          (pf_lt      : array_v (a, p_arr, n0_lt),
           pf_between : array_v (a?!, p_arr + (n0_lt * sizeof a),
                                 i0 - n0_lt),
           pf_after   : array_v (a, p_arr + (i0 * sizeof a), n - i0),
           pf_ge      : array_v (a, p_work, n0_ge),
           pf_pivot   : a @ (p_work + (n0_ge * sizeof a)),
           pf_work    : array_v (a?, p_work + (n0_ge * sizeof a)
                                     + sizeof a,
                                 n - n0_ge - 1) |
           p_arr      : ptr p_arr,
           p_work     : ptr p_work,
           n          : size_t n,
           n0_lt      : size_t n0_lt,
           i0         : size_t i0,
           n0_ge      : size_t n0_ge)
    :<!wrt> [n_lt, n_ge : nat | n_lt + n_ge == n]
            @(array_v (a, p_arr, n_lt),
              array_v (a?!, p_arr + (n_lt * sizeof a), n_ge),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n_lt) |
              size_t n_lt,
              size_t n_ge) =
  let
    fun
    loop {n1_lt      : nat}
         {n1_ge      : nat | n0_ge + 1 <= n1_ge}
         {i          : int | i0 <= i; i <= n;
                             n1_lt + n1_ge == i}
         .<n - i>.
         (pf_lt      : array_v (a, p_arr, n1_lt),
          pf_between : array_v (a?!, p_arr + (n1_lt * sizeof a),
                                i - n1_lt),
          pf_after   : array_v (a, p_arr + (i * sizeof a), n - i),
          pf_ge1     : array_v (a, p_work, n0_ge),
          pf_pivot   : a @ (p_work + (n0_ge * sizeof a)),
          pf_ge2     : array_v (a, (p_work + (n0_ge * sizeof a)
                                      + sizeof a),
                                n1_ge - n0_ge - 1),
          pf_work    : array_v (a?, p_work + (n1_ge * sizeof a),
                                n - n1_ge) |
          i          : size_t i,
          n1_lt      : size_t n1_lt,
          n1_ge      : size_t n1_ge)
        :<!wrt> [n_lt, n_ge : nat | n_lt + n_ge == n]
                @(array_v (a, p_arr, n_lt),
                  array_v (a?!, p_arr + (n_lt * sizeof a), n_ge),
                  array_v (a, p_work, n_ge),
                  array_v (a?, p_work + (n_ge * sizeof a), n_lt) |
                  size_t n_lt,
                  size_t n_ge) =
      if i = n then
        let
          prval () = array_v_unnil pf_after
          prval pf_ge = array_v_extend (pf_ge1, pf_pivot)
          prval pf_ge = array_v_unsplit (pf_ge, pf_ge2)
          prval () = lemma_mul_isfun {i - n1_lt, sizeof a}
                                     {n1_ge, sizeof a} ()
        in
          @(pf_lt, pf_between, pf_ge, pf_work | n1_lt, n1_ge)
        end
      else
        let
          prval @(pf_src, pf_after) = array_v_uncons pf_after
          val p_src = ptr_add<a> (p_arr, i)
          and p_pivot = ptr_add<a> (p_work, n0_ge) 
          val sign = array_stable_quicksort$cmp<a> (!p_src, !p_pivot)
        in
          if 0 <= sign then
            let         (* Move the element to the workspace array. *)
              prval @(pf_dst, pf_work) = array_v_uncons pf_work
              val p_dst = ptr_add<a> (p_work, n1_ge)
              val () =
                ptr_set<a>
                  (pf_dst | p_dst, ptr_get<a> (pf_src | p_src))
              prval pf_ge2 = array_v_extend (pf_ge2, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_lt, pf_between, pf_after,
                    pf_ge1, pf_pivot, pf_ge2, pf_work |
                    succ i, n1_lt, succ n1_ge)
            end
          else
            let      (* Move the element earlier in the same array. *)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              val p_dst = ptr_add<a> (p_arr, n1_lt)
              val () =
                ptr_set<a>
                  (pf_dst | p_dst, ptr_get<a> (pf_src | p_src))
              prval pf_lt = array_v_extend (pf_lt, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_lt, pf_between, pf_after,
                    pf_ge1, pf_pivot, pf_ge2, pf_work |
                    succ i, succ n1_lt, n1_ge)
            end
        end

    prval pf_ge1 = pf_ge
    prval pf_ge2 =
      array_v_nil {a} {p_work + (n0_ge * sizeof a) + sizeof a} ()
  in
    loop (pf_lt, pf_between, pf_after,
          pf_ge1, pf_pivot, pf_ge2, pf_work |
          i0, n0_lt, succ n0_ge)
  end

fn {a : vt@ype}
partition_array_after_pivot_selection
          {n         : pos}
          {n_before  : nat}
          {n_after   : nat | n_before + 1 + n_after == n}
          {p_arr     : addr}
          {p_work    : addr}
          (pf_before : array_v (a, p_arr, n_before),
           pf_pivot  : a @ (p_arr + (n_before * sizeof a)),
           pf_after  : array_v (a, (p_arr + (n_before * sizeof a)
                                      + sizeof a),
                                n_after),
           pf_work   : array_v (a?, p_work, n) |
           p_arr     : ptr p_arr,
           p_work    : ptr p_work,
           p_pivot   : ptr (p_arr + (n_before * sizeof a)),
           n         : size_t n,
           n_before  : size_t n_before,
           n_after   : size_t n_after)
    :<!wrt> [n_lt, n_ge : nat | n_lt + n_ge == n]
            @(array_v (a, p_arr, n_lt),
              array_v (a?!, p_arr + (n_lt * sizeof a), n_ge),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n_lt) |
              size_t n_lt,
              size_t n_ge) =
  let
    val @(pf_lt, pf_between, pf_ge, pf_work | n_lt, n_ge) =
      partition_array_before_pivot (pf_before, pf_work, pf_pivot |
                                    p_arr, p_work, p_pivot, n_before)
    val @(pf_between, pf_work, pf_pivot | ) =
      move_pivot (pf_between, pf_pivot, pf_work |
                  p_arr, p_work, n, n_lt, n_before, n_ge)
  in
    partition_array_after_pivot (pf_lt, pf_between, pf_after,
                                 pf_ge, pf_pivot, pf_work |
                                 p_arr, p_work, n, n_lt,
                                 succ n_before, n_ge)
  end

(*------------------------------------------------------------------*)
