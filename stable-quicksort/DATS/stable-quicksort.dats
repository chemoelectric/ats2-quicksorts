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
(* An insertion sort for small sublists.                            *)

(* Inserting in reverse order minimizes the work for a list already
   nearly sorted, or for stably sorting a list whose entries often
   have equal keys. *)
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
           reversed_prefix : list_vt (INV(a), n))
    :<!wrt> list_vt (a, m + n) =
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
    
    var dst : list_vt (a, n) = reversed_prefix
  in
    loop (lst, dst);
    list_vt_reverse<a> dst
  end

(*------------------------------------------------------------------*)

fn {a : vt@ype}
select_pivot
          {n          : pos}
          (lst        : list_vt (a, n),
           n          : int n,
           lst_before : &list_vt (a, 0)? >> list_vt (a, n_before),
           lst_pivot  : &list_vt (a, 0)? >> list_vt (a, 1),
           lst_after  : &list_vt (a, 0)? >> list_vt (a, n_after),
           n_before   : &int? >> int n_before,
           n_after    : &int? >> int n_after)
    :<!wrt> #[n_before, n_after : int | n_before + 1 + n_after == n]
            void =
  let
    val u64_n : uint64 n = g1i2u n
    val u64_rand : [i : nat] uint64 i = g1ofg0 (random_uint64 ())
    val u64_pivot = g1uint_mod (u64_rand, u64_n)
    val i_pivot : [i : nat | i < n] int i = g1u2i u64_pivot

    val @(left, right) = list_vt_split_at<a> (lst, i_pivot)
    val @(pivot, right) = list_vt_split_at<a> (right, 1)
  in
    lst_before := left;
    lst_pivot := pivot;
    lst_after := right;
    n_before := i_pivot;
    n_after := pred (n - i_pivot)
  end

(*------------------------------------------------------------------*)
