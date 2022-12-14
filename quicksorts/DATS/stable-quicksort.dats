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

#define ATS_PACKNAME "ats2-quicksorts"
#define ATS_EXTERN_PREFIX "ats2_quicksorts_"

#include "share/atspre_staload.hats"
staload "quicksorts/SATS/stable-quicksort.sats"
staload "quicksorts/SATS/bptr.sats"
staload _ = "quicksorts/DATS/bptr.dats"
staload UN = "prelude/SATS/unsafe.sats"

#define WORKSPACE_THRESHOLD 256
#define STK_MAX 64    (* Enough for arrays of up to 2**64 elements. *)

#include "quicksorts/DATS/SHARE/quicksorts.share.dats"

fn {a : vt@ype}
elem_lt_ptr1_ptr1
          {p, q : addr}
          (pf_p : !a @ p,
           pf_q : !a @ q |
           p    : ptr p,
           q    : ptr q)
    :<> bool =
  array_stable_quicksort$lt<a> (!p, !q)

fn {a : vt@ype}
elem_lt_bptr_bptr
          {p, q : addr}
          {i, j : int}
          (pf_i : !a @ (p + (i * sizeof a)),
           pf_j : !a @ (q + (j * sizeof a)) |
           bp_i : bptr (a, p, i),
           bp_j : bptr (a, q, j))
    :<> bool =
  elem_lt_ptr1_ptr1<a> (pf_i, pf_j | bptr2ptr bp_i, bptr2ptr bp_j)

fn {a : vt@ype}
elem_lt_array_bptr_bptr
          {p_arr  : addr}
          {n      : int}
          {i, j   : nat | i <= n - 1; j <= n - 1; i != j}
          (pf_arr : !array_v (a, p_arr, n) |
           bp_i   : bptr (a, p_arr, i),
           bp_j   : bptr (a, p_arr, j))
    :<> bool =
  let
    prval @(pf_i, pf_j, fpf) =
      array_v_takeout2 {a} {p_arr} {n} {i, j} pf_arr
    val is_lt =
      elem_lt_bptr_bptr<a> (pf_i, pf_j | bp_i, bp_j)
    prval () = pf_arr := fpf (pf_i, pf_j)
  in
    is_lt
  end

overload lt with elem_lt_ptr1_ptr1
overload lt with elem_lt_bptr_bptr
overload lt with elem_lt_array_bptr_bptr

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

#define DEFAULT_SMALL_SORT_THRESHOLD 80

implement {a}
array_stable_quicksort$small () =
  i2sz DEFAULT_SMALL_SORT_THRESHOLD

implement {a}
array_stable_quicksort$small_sort (arr, n) =
  array_stable_quicksort_small_sort_default (arr, n)

implement {a}
array_stable_quicksort_small_sort_default (arr, n) =
  array_stable_quicksort_small_sort_insertion (arr, n)

implement {a}
array_stable_quicksort$pivot_index {n} (arr, n) =
  array_stable_quicksort_pivot_index_default<a> {n} (arr, n)

implement {a}
array_stable_quicksort_pivot_index_default {n} (arr, n) =
  array_stable_quicksort_pivot_index_median_of_three_random<a>
    {n} (arr, n)

implement {a}
array_stable_quicksort_pivot_index_random {n} (arr, n) =
  quicksorts_pivot_index_random<a> {n} (arr, n)

implement {a}
array_stable_quicksort_pivot_index_median_of_three_random
        {n} (arr, n) =
  let
    implement
    quicksorts$array_element_lt<a> (arr, i, j) =
      array_element_lt<a> (arr, i, j)
  in
    quicksorts_pivot_index_median_of_three_random<a> {n} (arr, n)
  end

implement {a}
insertion_sort$lt (pf_arr | bp_i, bp_j) =
  lt<a> (pf_arr | bp_i, bp_j)

implement {a}
insertion_sort$gt_or_gte (pf_arr | bp_i, bp_j) =
  (* Greater than or equal to. *)
  ~lt<a> (pf_arr | bp_i, bp_j)

implement {a}
array_stable_quicksort_small_sort_insertion {n} (arr, n) =
  insertion_sort<a> (arr, n)

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

extern fn {a : vt@ype}
scan_run$pred
          {p        : addr}
          {p_pivot  : addr}
          (pf_p     : !a @ p,
           pf_pivot : !a @ p_pivot |
           p        : ptr p,
           p_pivot  : ptr p_pivot)
    :<> bool

fn {a : vt@ype}
scan_run {p_arr    : addr}
         {n        : int}
         {i0, i    : int | 0 <= i0; i0 <= i; i <= n}
         {p_pivot  : addr}
         (pf_arr1  : !array_v (a, p_arr + (i0 * sizeof a),
                               n - i0),
          pf_pivot : !a @ p_pivot |
          bp_i0    : bptr (a, p_arr, i0),
          bp_i     : bptr (a, p_arr, i),
          bp_n     : bptr (a, p_arr, n),
          p_pivot  : ptr p_pivot)
    :<> [j : int | i <= j; j <= n]
        bptr (a, p_arr, j) =
  let
    fun
    loop {k : nat | i <= k; k <= n}
         .<n - k>.
         (pf_arr1  : !array_v (a, p_arr + (i0 * sizeof a),
                               n - i0),
          pf_pivot : !a @ p_pivot |
          bp_k     : bptr (a, p_arr, k))
        :<> [j : int | i <= j; j <= n]
            bptr (a, p_arr, j) =
      if bp_k = bp_n then
        bp_k
      else
        let
          prval @(pf_k, fpf_k) =
            array_v_takeout {a} {p_arr + (i0 * sizeof a)}
                            {n - i0} {k - i0}
                            pf_arr1
          val pred_satisfied =
            scan_run$pred<a> (pf_k, pf_pivot | bptr2ptr bp_k, p_pivot)
          prval () = pf_arr1 := fpf_k pf_k
        in
          if pred_satisfied then
            loop (pf_arr1, pf_pivot | succ bp_k)
          else
            bp_k
        end
  in
    loop (pf_arr1, pf_pivot | bp_i)
  end

extern fn {a : vt@ype}
partition_before_or_after_pivot$lt_or_le
          {p        : addr}
          {p_pivot  : addr}
          (pf_p     : !a @ p,
           pf_pivot : !a @ p_pivot |
           p        : ptr p,
           p_pivot  : ptr p_pivot)
    :<> bool

extern fn {a : vt@ype}
partition_before_or_after_pivot$gt_or_ge
          {p        : addr}
          {p_pivot  : addr}
          (pf_p     : !a @ p,
           pf_pivot : !a @ p_pivot |
           p        : ptr p,
           p_pivot  : ptr p_pivot)
    :<> bool

fn {a : vt@ype}
partition_before_or_after_pivot
          {p_arr    : addr}
          {n_avail  : int}
          {n_arr    : int | n_arr <= n_avail}
          {p_avail  : addr}
          {p_pivot  : addr}
          (pf_arr   : array_v (a, p_arr, n_arr),
           pf_avail : array_v (a?, p_avail, n_avail),
           pf_pivot : !a @ p_pivot |
           bp_arr   : bptr_anchor (a, p_arr),
           bp_n_arr : bptr (a, p_arr, n_arr),
           bp_avail : bptr_anchor (a, p_avail),
           p_pivot  : ptr p_pivot)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n_arr]
            @(array_v (a, p_arr, n_le),
              array_v (a?, p_arr + (n_le * sizeof a),
                       n_arr - n_le),
              array_v (a, p_avail, n_ge),
              array_v (a?, p_avail + (n_ge * sizeof a),
                       n_avail - n_ge) |
            bptr (a, p_arr, n_le),
            bptr (a, p_avail, n_ge)) =
  let
    prval () = lemma_array_v_param pf_arr
    prval () = lemma_array_v_param pf_avail

    fun
    loop {i          : nat | i <= n_arr}
         {n_le, n_ge : nat | n_le + n_ge == i}
         .<n_arr - i>.
         (pf_le      : array_v (a, p_arr, n_le),
          pf_between : array_v (a?, p_arr + (n_le * sizeof a),
                                i - n_le),
          pf_arr     : array_v (a, p_arr + (i * sizeof a),
                                n_arr - i),
          pf_ge      : array_v (a, p_avail, n_ge),
          pf_avail   : array_v (a?, p_avail + (n_ge * sizeof a),
                                n_avail - n_ge),
          pf_pivot   : !a @ p_pivot |
          bp_i       : bptr (a, p_arr, i),
          bp_le      : bptr (a, p_arr, n_le),
          bp_ge      : bptr (a, p_avail, n_ge))
        :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n_arr]
                @(array_v (a, p_arr, n_le),
                  array_v (a?, p_arr + (n_le * sizeof a),
                           n_arr - n_le),
                  array_v (a, p_avail, n_ge),
                  array_v (a?, p_avail + (n_ge * sizeof a),
                           n_avail - n_ge) |
                bptr (a, p_arr, n_le),
                bptr (a, p_avail, n_ge)) =
      if bp_i = bp_n_arr then
        let
          prval () = array_v_unnil pf_arr
        in
          @(pf_le, pf_between, pf_ge, pf_avail | bp_le, bp_ge)
        end
      else
        let
          implement
          scan_run$pred<a> (pf_p, pf_pivot | p, p_pivot) =
            partition_before_or_after_pivot$gt_or_ge<a>
              (pf_p, pf_pivot | p, p_pivot)
          val [j : int] bp_j =
            scan_run<a> (pf_arr, pf_pivot |
                         bp_i, succ bp_i, bp_n_arr, p_pivot)
          val nmemb = bp_j - bp_i

          prval @(pf_arr1, pf_arr) =
            array_v_split {a} {p_arr + (i * sizeof a)}
                          {n_arr - i} {j - i}
                          pf_arr
          prval @(pf_avail1, pf_avail) =
            array_v_split {a?} {p_avail + (n_ge * sizeof a)}
                          {n_avail - n_ge} {j - i}
                          pf_avail

          val () = copy<a> (pf_avail1, pf_arr1 |
                            bptr2ptr bp_ge, bptr2ptr bp_i, nmemb)

          prval pf_between = array_v_unsplit (pf_between, pf_arr1)
          prval pf_ge = array_v_unsplit (pf_ge, pf_avail1)

          val bp_ge = bp_ge + nmemb
        in
          if bp_j = bp_n_arr then
            let
              prval () = array_v_unnil pf_arr
            in
              @(pf_le, pf_between, pf_ge, pf_avail | bp_le, bp_ge)
            end
          else
            let
              implement
              scan_run$pred<a> (pf_p, pf_pivot | p, p_pivot) =
                partition_before_or_after_pivot$lt_or_le<a>
                  (pf_p, pf_pivot | p, p_pivot)

              val [k : int] bp_k =
                scan_run<a> (pf_arr, pf_pivot |
                             bp_j, succ bp_j, bp_n_arr, p_pivot)
              val nmemb = bp_k - bp_j

              prval @(pf_arr1, pf_arr) =
                array_v_split {a} {p_arr + (j * sizeof a)}
                              {n_arr - j} {k - j}
                              pf_arr

              val () = move_left<a> (pf_between, pf_arr1 |
                                     bptr2ptr bp_le, bptr2ptr bp_j,
                                     nmemb)

              prval pf_le = array_v_unsplit (pf_le, pf_between)
              prval pf_between = pf_arr1

              val bp_le = bp_le + nmemb
            in
              loop (pf_le, pf_between, pf_arr,
                    pf_ge, pf_avail, pf_pivot |
                    bp_k, bp_le, bp_ge)
            end
        end

    implement
    scan_run$pred<a> (pf_p, pf_pivot | p, p_pivot) =
      partition_before_or_after_pivot$lt_or_le<a>
        (pf_p, pf_pivot | p, p_pivot)
    val [n0_le : int] bp_le = 
      (* Skip elements that do not need to be moved. *)
      scan_run<a> (pf_arr, pf_pivot |
                   bp_arr, bp_arr, bp_n_arr, p_pivot)

    prval @(pf_le, pf_arr) =
      array_v_split {a} {p_arr} {n_arr} {n0_le} pf_arr
    prval pf_between =
      array_v_nil {a?} {p_arr + (n0_le * sizeof a)} ()

    prval pf_ge = array_v_nil {a} {p_avail} ()
    prval pf_avail = pf_avail
  in
    loop (pf_le, pf_between, pf_arr,
          pf_ge, pf_avail, pf_pivot |
          bp_le, bp_le, bp_avail)
  end

fn {a : vt@ype}
partition_before_pivot
          {p_before    : addr}
          {n_avail     : int}
          {n_before    : int | n_before <= n_avail}
          {p_avail     : addr}
          {p_pivot     : addr}
          (pf_before   : array_v (a, p_before, n_before),
           pf_avail    : array_v (a?, p_avail, n_avail),
           pf_pivot    : !a @ p_pivot |
           bp_before   : bptr_anchor (a, p_before),
           bp_n_before : bptr (a, p_before, n_before),
           bp_avail    : bptr_anchor (a, p_avail),
           p_pivot     : ptr p_pivot)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n_before]
            @(array_v (a, p_before, n_le),
              array_v (a?, p_before + (n_le * sizeof a),
                       n_before - n_le),
              array_v (a, p_avail, n_ge),
              array_v (a?, p_avail + (n_ge * sizeof a),
                       n_avail - n_ge) |
            bptr (a, p_before, n_le),
            bptr (a, p_avail, n_ge)) =
  let
    implement
    partition_before_or_after_pivot$lt_or_le<a> (pf_p, pf_pivot |
                                                 p, p_pivot) =
      (* Less than or equal to the pivot. *)
      ~lt<a> (pf_pivot, pf_p | p_pivot, p)

    implement
    partition_before_or_after_pivot$gt_or_ge<a> (pf_p, pf_pivot |
                                                 p, p_pivot) =
      (* Strictly greater than the pivot. *)
      lt<a> (pf_pivot, pf_p | p_pivot, p)
  in
    partition_before_or_after_pivot<a>
      (pf_before, pf_avail, pf_pivot |
       bp_before, bp_n_before, bp_avail, p_pivot)
  end

fn {a : vt@ype}
partition_after_pivot
          {p_after    : addr}
          {n_avail    : int}
          {n_after    : int | n_after <= n_avail}
          {p_avail    : addr}
          {p_pivot    : addr}
          (pf_after   : array_v (a, p_after, n_after),
           pf_avail   : array_v (a?, p_avail, n_avail),
           pf_pivot   : !a @ p_pivot |
           bp_after   : bptr_anchor (a, p_after),
           bp_n_after : bptr (a, p_after, n_after),
           bp_avail   : bptr_anchor (a, p_avail),
           p_pivot    : ptr p_pivot)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n_after]
            @(array_v (a, p_after, n_le),
              array_v (a?, p_after + (n_le * sizeof a),
                       n_after - n_le),
              array_v (a, p_avail, n_ge),
              array_v (a?, p_avail + (n_ge * sizeof a),
                       n_avail - n_ge) |
            bptr (a, p_after, n_le),
            bptr (a, p_avail, n_ge)) =
  let
    implement
    partition_before_or_after_pivot$lt_or_le<a> (pf_p, pf_pivot |
                                                 p, p_pivot) =
      (* Strictly less than the pivot. *)
      lt<a> (pf_p, pf_pivot | p, p_pivot)

    implement
    partition_before_or_after_pivot$gt_or_ge<a> (pf_p, pf_pivot |
                                                 p, p_pivot) =
      (* Greater than or equal to the pivot. *)
      ~lt<a> (pf_p, pf_pivot | p, p_pivot)
  in
    partition_before_or_after_pivot<a>
      (pf_after, pf_avail, pf_pivot |
       bp_after, bp_n_after, bp_avail, p_pivot)
  end

fn {a : vt@ype}
partition {n       : pos}
          {p_arr   : addr}
          {p_work  : addr}
          (pf_arr  : !array_v (a, p_arr, n),
           pf_work : !array_v (a?, p_work, n - 1) |
           p_arr   : ptr p_arr,
           p_work  : ptr p_work,
           n       : size_t n)
    :<!wrt> [i_pivot_final : nat | i_pivot_final <= n - 1]
            size_t i_pivot_final =
  let
    val [i_pivot_initial : int] i_pivot_initial =
      array_stable_quicksort$pivot_index<a> (!p_arr, n)

    stadef n_before = i_pivot_initial
    stadef n_after = n - i_pivot_initial - 1

    val n_before : size_t n_before = i_pivot_initial
    and n_after : size_t n_after = n - i_pivot_initial - 1

    stadef p_pivot_initial = p_arr + (i_pivot_initial * sizeof a)
    val p_pivot_initial : ptr p_pivot_initial =
      ptr_add<a> (p_arr, i_pivot_initial)

    prval @(pf_before, pf_temp) =
      array_v_split {a} {p_arr} {n} {i_pivot_initial} pf_arr
    prval @(pf_pivot_initial, pf_after) =
      array_v_uncons {a} {p_pivot_initial} {n - i_pivot_initial}
                     pf_temp

    stadef p_before = p_arr
    stadef p_after = p_arr + (i_pivot_initial * sizeof a) + sizeof a
    stadef p_avail = p_work

    val p_before : ptr p_before = p_arr
    and p_after : ptr p_after =
      ptr_add<a> (p_arr, i_pivot_initial + 1)
    and p_avail : ptr p_avail = p_work

    prval pf_avail = pf_work

    val bp_before = ptr2bptr_anchor<a> p_before
    and bp_after = ptr2bptr_anchor<a> p_after
    and bp_avail = ptr2bptr_anchor<a> p_avail

    val bp_n_before = bp_before + n_before
    and bp_n_after = bp_after + n_after

    val [n_le1 : int, n_ge1 : int]
        @(pf_le1, pf_unused1, pf_ge1, pf_avail1 | bp_le1, bp_ge1) =
      partition_before_pivot
        (pf_before, pf_avail, pf_pivot_initial |
         bp_before, bp_n_before, bp_avail, p_pivot_initial)

    val [n_le2 : int, n_ge2 : int]
        @(pf_le2, pf_unused2, pf_ge2, pf_avail2 | bp_le2, bp_ge2) =
      partition_after_pivot
        (pf_after, pf_avail1, pf_pivot_initial |
         bp_after, bp_n_after, bptr_reanchor bp_ge1,
         p_pivot_initial)

    val n_le1 : size_t n_le1 = bp_le1 - bp_before
    and n_le2 : size_t n_le2 = bp_le2 - bp_after

    stadef n_le = n_le1 + n_le2
    stadef n_ge = n_ge1 + n_ge2
    val n_le : size_t n_le = n_le1 + n_le2
    val n_ge : size_t n_ge = n - n_le - 1

    val i_pivot_final = n_le
    val p_pivot_final = ptr_add<a> (p_arr, i_pivot_final)

    val pivot = ptr_get<a> (pf_pivot_initial | p_pivot_initial)

    prval pf_unused1 =
      array_v_extend {a?} {p_arr + (n_le1 * sizeof a)}
                     (pf_unused1, pf_pivot_initial)
    val () =
      move_left<a> (pf_unused1, pf_le2 |
                    bptr2ptr bp_le1, p_after, n_le2)

    prval pf_le = array_v_unsplit (pf_le1, pf_unused1)
    prval @(pf_pivot_final, pf_unused1) = array_v_uncons pf_le2
    val () = ptr_set<a> (pf_pivot_final | p_pivot_final, pivot)

    prval pf_unused =
      array_v_unsplit {a?} {p_arr + (n_le * sizeof a) + sizeof a}
                      {n - n_le - 1 - (n_after - n_le2),
                       n_after - n_le2}
                      (pf_unused1, pf_unused2)
    prval pf_ge =
      array_v_unsplit {a} {p_avail} {n_ge1, n_ge2} (pf_ge1, pf_ge2)
    val () = copy<a> (pf_unused, pf_ge |
                      ptr1_succ<a> p_pivot_final,
                      p_work, n - i_pivot_final - 1)
    prval pf_avail1 = pf_ge
    and pf_ge = pf_unused

    prval () = pf_work :=
      array_v_unsplit {a?} {p_work} {n_ge, n - 1 - n_ge}
                      (pf_avail1, pf_avail2)
    prval () = pf_arr :=
      array_v_unsplit {a} {p_arr} {n_le + 1, n_ge}
                      (array_v_extend (pf_le, pf_pivot_final), pf_ge)
  in
    i_pivot_final
  end

fn {a : vt@ype}
array_stable_sort
          {p_arr   : addr}
          {n       : nat}
          {p_work  : addr}
          (pf_arr  : !array_v (a, p_arr, n),
           pf_work : !array_v (a?, p_work, n - 1) |
           p_arr   : ptr p_arr,
           n       : size_t n,
           p_work  : ptr p_work)
    :<!wrt> void =
  if n <= i2sz 1 then
    ()
  else
    let
      fun
      loop {p_stk    : addr}
           {depth    : nat}
           {size_sum : nat}
           .<size_sum>.
           (pf_work : !array_v (a?, p_work, n - 1) |
            stk     : &stk_vt (p_stk, depth, size_sum)
                        >> stk_vt (p_stk, 0, 0))
          :<!wrt> void =
        if (stk.depth) = 0 then
          $effmask_exn assertloc (stk.size_sum = i2sz 0)
        else
          let
            val () = $effmask_exn assertloc (stk.size_sum <> i2sz 0)
            val @(p2tr_arr1, n1) = stk_vt_pop<a> stk
            val @(pf_arr1, fpf_arr1 | p_arr1) =
              $UN.p2tr_vtake p2tr_arr1
         in
            if n1 <= array_stable_quicksort$small<a> () then
              let
                val () =
                  array_stable_quicksort$small_sort<a> (!p_arr1, n1)
                prval () = fpf_arr1 pf_arr1
              in
                loop (pf_work | stk)
              end
            else
              let
                val () = $effmask_exn assertloc (n1 <= n)
                prval [n1 : int] EQINT () = eqint_make_guint n1

                prval @(pf_work1, pf_work2) =
                  array_v_split {a?} {p_work} {n - 1} {n1 - 1} pf_work
                val [n1_le : int] n1_le =
                  partition<a> (pf_arr1, pf_work1 |
                                p_arr1, p_work, n1)
                prval () = pf_work :=
                  array_v_unsplit (pf_work1, pf_work2)

                val p_le = p_arr1
                and p_ge = ptr_add<a> (p_arr1, succ n1_le)
                and n1_ge = n1 - succ n1_le

                prval @(pf_le, pf_pivot_and_ge) =
                  array_v_split {a} {..} {n1} {n1_le} pf_arr1
                prval @(pf_pivot, pf_ge) =
                  array_v_uncons pf_pivot_and_ge
              in
                (* Push the larger part of the partition first.
                   Otherwise the stack may overflow. *)
                if n1_le = i2sz 0 then
                  let
                    val () = $effmask_exn
                      assertloc ((stk.depth) <= STK_MAX - 1)
                    val () = stk_vt_push<a> (pf_ge | p_ge, n1_ge, stk)
                    val () = loop (pf_work | stk)
                    prval () = pf_arr1 :=
                      array_v_extend (pf_le, pf_pivot)
                    prval () = pf_arr1 :=
                      array_v_unsplit (pf_arr1, pf_ge)
                    prval () = fpf_arr1 pf_arr1
                  in
                  end
                else if n1_le < n1_ge then
                  let
                    val () = $effmask_exn
                      assertloc ((stk.depth) <= STK_MAX - 2)
                    val () = stk_vt_push<a> (pf_ge | p_ge, n1_ge, stk)
                    val () = stk_vt_push<a> (pf_le | p_le, n1_le, stk)
                    val () = loop (pf_work | stk)
                    prval () = pf_arr1 :=
                      array_v_extend (pf_le, pf_pivot)
                    prval () = pf_arr1 :=
                      array_v_unsplit (pf_arr1, pf_ge)
                    prval () = fpf_arr1 pf_arr1
                  in
                  end
                else if n1_ge = i2sz 0 then
                  let
                    val () = $effmask_exn
                      assertloc ((stk.depth) <= STK_MAX - 1)
                    val () = stk_vt_push<a> (pf_le | p_le, n1_le, stk)
                    val () = loop (pf_work | stk)
                    prval () = pf_arr1 :=
                      array_v_extend (pf_le, pf_pivot)
                    prval () = pf_arr1 :=
                      array_v_unsplit (pf_arr1, pf_ge)
                    prval () = fpf_arr1 pf_arr1
                  in
                  end
                else
                  let
                    val () = $effmask_exn
                      assertloc ((stk.depth) <= STK_MAX - 2)
                    val () = stk_vt_push<a> (pf_le | p_le, n1_le, stk)
                    val () = stk_vt_push<a> (pf_ge | p_ge, n1_ge, stk)
                    val () = loop (pf_work | stk)
                    prval () = pf_arr1 :=
                      array_v_extend (pf_le, pf_pivot)
                    prval () = pf_arr1 :=
                      array_v_unsplit (pf_arr1, pf_ge)
                    prval () = fpf_arr1 pf_arr1
                  in
                  end
              end
          end

      var stk_storage =
        @[stk_entry_t][STK_MAX] (@(the_null_ptr, i2sz 0))
      var stk = stk_vt_make (view@ stk_storage | addr@ stk_storage)

      val () = stk_vt_push<a> (pf_arr | p_arr, n, stk)
      val () = loop (pf_work | stk)
      prval () = view@ stk_storage := stk.pf
    in
    end

implement {a}
array_stable_quicksort_given_workspace {n} {m1} {m2}
                                       (arr, n, workspace) =
  if n = i2sz 0 then
    ()
  else
    let
      prval () = lemma_array_param arr
      prval () = lemma_g1uint_param n

      (* Check that n is not too large. This can happen only if size_t
         is more than STK_MAX bits long. *)
      val () = $effmask_exn assertloc (iseqz (n >> STK_MAX))

      prval @(pf_arr1, pf_arr2) =
        array_v_split {a} {..} {m1} {n} (view@ arr)
      prval @(pf_work1, pf_work2) =
        array_v_split {a?} {..} {m2} {n - 1} (view@ workspace)
      val () =
        array_stable_sort<a> (pf_arr1, pf_work1 |
                              addr@ arr, n, addr@ workspace)
      prval () = view@ arr :=
        array_v_unsplit (pf_arr1, pf_arr2)
      prval () = view@ workspace :=
        array_v_unsplit (pf_work1, pf_work2)
    in
    end

implement {a}
array_stable_quicksort_not_given_workspace {n} (arr, n) =
  let
    prval () = lemma_g1uint_param n

    fn
    quicksort {n         : int}
              {m1        : int | n <= m1}
              {m2        : int | n - 1 <= m2}
              (arr       : &array (a, m1),
               n         : size_t n,
               workspace : &array (a?, m2))
        :<!wrt> void =
      array_stable_quicksort_given_workspace<a> (arr, n, workspace)

    prval () = lemma_array_param arr
  in
    if n = i2sz 0 then
      ()
    else if pred n <= WORKSPACE_THRESHOLD then
      let
        var storage : @[a?][WORKSPACE_THRESHOLD]
        val () = quicksort (arr, n, storage)
      in
      end
    else
      let
        val @(pf_work, pfgc_work | p_work) =
          array_ptr_alloc<a?> (n - 1)
        val () = quicksort (arr, n, !p_work)
        val () = array_ptr_free (pf_work, pfgc_work | p_work)
      in
      end
  end

(*------------------------------------------------------------------*)
