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

#define ATS_PACKNAME "ats2-stable-quicksort"
#define ATS_EXTERN_PREFIX "ats2_stable_quicksort_"

#include "share/atspre_staload.hats"
staload "stable-quicksort/SATS/stable-quicksort.sats"
staload UN = "prelude/SATS/unsafe.sats"

#define NIL list_vt_nil ()
#define ::  list_vt_cons

(*------------------------------------------------------------------*)
(* A simple linear congruential generator, for pivot selection.     *)

%{
ats2_stable_quicksort_spinlock_t ats2_stable_quicksort_seed_lock;
uint64_t ats2_stable_quicksort_seed = 0;
%}

extern fn
random_uint64 () :<!wrt> uint64 = "mac#%"

(*------------------------------------------------------------------*)
(* A list with a pointer to its last node.                          *)

absvt@ype extensible_list_vt (a : vt@ype+, n : int, p : addr) =
  @(list_vt (a, n),
    p2tr (list_vt (a, ifint (n == 0, 0, 1)), p),
    int n)
vtypedef extensible_list_vt (a : vt@ype+, n : int) =
  [p : addr | null < p] extensible_list_vt (a, n, p)
vtypedef extensible_list_vt (a : vt@ype+) =
  [n : int] extensible_list_vt (a, n)

fn {a : vt@ype}
unsafe_list_vt2extensible
          {n       : nat}
          {p       : addr | null < p}
          (lst     : list_vt (a, n),
           p2_last : p2tr (list_vt (a, ifint (n == 0, 0, 1)), p),
           n       : int n)
    :<> extensible_list_vt (a, n, p) =
  $UN.castvwtp0 @(lst, p2_last, n)

fn {a : vt@ype}
extensible2list_vt
          {n       : nat}
          {p       : addr | null < p}
          (lst     : extensible_list_vt (a, n, p))
    :<> @(list_vt (a, n),
          p2tr (list_vt (a, ifint (n == 0, 0, 1)), p),
          int n) =
  $UN.castvwtp0 lst

%{
atstype_ptr ats2_stable_quicksort_nil = NULL;
atstype_ptr ats2_stable_quicksort_addr_of_nil =
  &ats2_stable_quicksort_nil;
%}

fn {a : vt@ype}
extensible_list_vt_nil ()
    :<> extensible_list_vt (a, 0) =
  let
    val p2 =
      $UN.ptr2p2tr{list_vt (a, 0)}
        $extval(Ptr1, "ats2_stable_quicksort_addr_of_nil")
  in
    unsafe_list_vt2extensible<a> (NIL, p2, 0)
  end

fn {a : vt@ype}
extensible_list_vt_finalize
          {n   : nat}
          (lst : extensible_list_vt (a, n))
    :<!wrt> @(list_vt (a, n), int n) =
  let
    val @(ls, _, n) = extensible2list_vt<a> lst
  in
    @(ls, n)
  end

fn {a : vt@ype}
extensible_list_vt_append
          {n1, n2 : nat}
          {p1, p2 : addr | null < p1; null < p2}
          (lst1   : extensible_list_vt (a, n1, p1),
           lst2   : extensible_list_vt (a, n2, p2))
    :<!wrt> extensible_list_vt (a, n1 + n2) =
  let
    val @(ls_1, p2_1, n_1) = extensible2list_vt<a> lst1
  in
    if n_1 = 0 then
      let
        val+ ~ NIL = ls_1
      in
        lst2
      end
    else
      let
        val @(ls_2, p2_2, n_2) = extensible2list_vt<a> lst2
      in
        if n_2 = 0 then
          let
            val+ ~ NIL = ls_2
          in
            unsafe_list_vt2extensible<a> (ls_1, p2_1, n_1)
          end
        else
          let
            val @(pf, fpf | p) = $UN.p2tr_vtake p2_1
            val+ @ (_ :: tail) = !p
            val+ ~ NIL = tail
            val () = tail := ls_2
            prval () = fold@ (!p)
            prval pf = $UN.castview0{list_vt (a, 1) @ p1} pf
            prval () = fpf pf
          in
            unsafe_list_vt2extensible<a>
              ($UN.castvwtp0 ls_1, p2_2, n_1 + n_2)
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
        val p2_last = $UN.ptr2p2tr ($UN.cast2Ptr1 (addr@ dst))
      in
        unsafe_list_vt2extensible (list_vt_reverse<a> dst, p2_last,
                                   m + n)
      end
  end

(*------------------------------------------------------------------*)

typedef sign_t (i : int) = [~1 <= i && i <= 1] int i
typedef sign_t = [i : int] sign_t i

fn {a : vt@ype}
compare_with_pivot
          (x     : &a,
           pivot : &a)
    :<> sign_t =
  let
    val sign = list_vt_stable_quicksort$cmp<a> (x, pivot)
    val sign = g1ofg0 sign
    val sign = max (sign, ~1)
    val sign = min (sign, 1)
  in
    sign
  end

fn {a : vt@ype}
compare_head_with_pivot
          {n     : pos}
          (lst   : &list_vt (a, n),
           pivot : &a)
    :<> sign_t =
  let
    val+ @ (head :: _) = lst
    val sign = compare_with_pivot<a> (head, pivot)
    prval () = fold@ lst
  in
    sign
  end

fn {a : vt@ype}
select_pivot_index
          {n   : pos}
          (lst : !list_vt (a, n),
           n   : int n)
    :<!wrt> [i : nat | i < n]
            int i =
  let
    val u64_n : uint64 n = g1i2u n
    val u64_rand : [i : nat] uint64 i = g1ofg0 (random_uint64 ())
    val u64_pivot = g1uint_mod (u64_rand, u64_n)
    val i_pivot : [i : nat | i < n] int i = g1u2i u64_pivot
  in
    i_pivot
  end

fn {a : vt@ype}
select_pivot
          {n          : pos}
          (lst        : list_vt (a, n),
           n          : int n,
           lst_before : &(List_vt a)? >> list_vt (a, n_before),
           lst_pivot  : &(List_vt a)? >> list_vt (a, 1),
           lst_after  : &(List_vt a)? >> list_vt (a, n_after),
           n_before   : &int? >> int n_before,
           n_after    : &int? >> int n_after)
    :<!wrt> #[n_before, n_after : nat | n_before + 1 + n_after == n]
            void =
  let
    val i_pivot = select_pivot_index<a> (lst, n)
    val @(left, right) = list_vt_split_at<a> (lst, i_pivot)
    val @(pivot, right) = list_vt_split_at<a> (right, 1)
  in
    lst_before := left;
    lst_pivot := pivot;
    lst_after := right;
    n_before := i_pivot;
    n_after := pred (n - i_pivot)
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
                @(int m2,
                  P2tr1 (list_vt (a, 1)),
                  sign_t) =
      let
        val+ @ (head :: tail) = lst1
      in
        case+ tail of
        | NIL =>
          let
            val () = lst2 := NIL
            prval () = fold@ lst1
          in
            @(0,
              $UN.ptr2p2tr ($UN.cast2Ptr1 (addr@ lst1)),
              0)
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
              in
                @(pred m,
                  $UN.ptr2p2tr ($UN.cast2Ptr1 (addr@ lst1)),
                  new_sign)
              end
          end
      end

    var lst1 = lst
    var lst2 : List_vt a
    val @(n2, p2_last, new_sign) = loop (lst1, lst2, pivot, n)
    val elst1 = unsafe_list_vt2extensible (lst1, p2_last, n - n2)
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
          val @(elst, lst2, m2, sign) =
            split_after_run<a> (lst1, m1, pivot, sign)
        in
          if sign = ~1 then
            let
              val elst_lt = (elst_lt \appd elst)
            in
              loop (lst2, m2, pivot, sign, elst_lt, elst_eq, elst_gt)
            end
          else if sign = 0 then
            let
              val elst_eq = (elst_eq \appd elst)
            in
              loop (lst2, m2, pivot, sign, elst_lt, elst_eq, elst_gt)
            end
          else
            let
              val elst_gt = (elst_gt \appd elst)
            in
              loop (lst2, m2, pivot, sign, elst_lt, elst_eq, elst_gt)
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
partition {n     : pos}
          (lst   : list_vt (a, n),
           n     : int n)
    :<!wrt> [n_lt, n_eq, n_gt : int | 0 <= n_lt; 1 <= n_eq; 0 <= n_gt;
                                      n_lt + n_eq + n_gt == n]
            @(extensible_list_vt (a, n_lt),
              extensible_list_vt (a, n_eq),
              extensible_list_vt (a, n_gt)) =
  let
    macdef appd = extensible_list_vt_append<a>

    var lst_before : List_vt a
    var lst_pivot  : List_vt a
    var lst_after  : List_vt a
    var n_before   : int
    var n_after    : int

    val () = select_pivot<a> (lst, n,
                              lst_before, lst_pivot, lst_after,
                              n_before, n_after)

    val+ @ (pivot :: _) = lst_pivot
    val @(elst1_lt, elst1_eq, elst1_gt) =
      partition_pivot_free_list<a> (lst_before, n_before, pivot)
    val @(elst2_lt, elst2_eq, elst2_gt) =
      partition_pivot_free_list<a> (lst_after, n_after, pivot)

    prval () = fold@ lst_pivot

    val elst_lt = (elst1_lt \appd elst2_lt)
    val p2_pivot = $UN.ptr2p2tr ($UN.cast2Ptr1 (addr@ lst_pivot))
    val elst_pivot =
      unsafe_list_vt2extensible<a> (lst_pivot, p2_pivot, 1)
    val elst_eq = ((elst1_eq \appd elst_pivot) \appd elst2_eq)
    val elst_gt = (elst1_gt \appd elst2_gt)
  in
    @(elst_lt, elst_eq, elst_gt)
  end

implement {a}
list_vt_stable_quicksort lst =
  let
    #define THRESHOLD 10        (* FIXME: Tune this. *)

    macdef finalize = extensible_list_vt_finalize<a>
    macdef appd = extensible_list_vt_append<a>

    fun
    recurs {m : nat}
           .<m>.
           (lst : list_vt (a, m),
            m   : int m)
        :<!wrt> extensible_list_vt (a, m) =
      if m <= THRESHOLD then
        list_vt_insertion_sort<a> (lst, m, NIL, 0)
      else
        let
          val @(elst_lt, elst_eq, elst_gt) =
            partition<a> (lst, m)
          val @(lst1, m1) = finalize elst_lt
          and @(lst2, m2) = finalize elst_gt
          val elst1 = recurs (lst1, m1)
          and elst2 = recurs (lst2, m2)
        in
          ((elst1 \appd elst_eq) \appd elst2)
        end

    prval () = lemma_list_vt_param lst
    val @(lst_sorted, _) = finalize (recurs (lst, length lst))
  in
    lst_sorted
  end

(*------------------------------------------------------------------*)
