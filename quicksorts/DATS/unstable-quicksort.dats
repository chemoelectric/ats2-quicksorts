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
staload "quicksorts/SATS/unstable-quicksort.sats"
staload "quicksorts/SATS/bptr.sats"
staload _ = "quicksorts/DATS/bptr.dats"
staload UN = "prelude/SATS/unsafe.sats"

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
  array_unstable_quicksort$lt<a> (!p, !q)

fn {a : vt@ype}
elem_lt_bptr_bptr
          {p      : addr}
          {i, j   : int}
          (pf_i   : !a @ (p + (i * sizeof a)),
           pf_j   : !a @ (p + (j * sizeof a)) |
           bp_i   : bptr (a, p, i),
           bp_j   : bptr (a, p, j))
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
      lt<a> (pf_i, pf_j | ptr_add<a> (addr@ arr, i),
                          ptr_add<a> (addr@ arr, j))
    prval () = view@ arr := fpf (pf_i, pf_j)
  in
    is_lt
  end

implement {a}
array_unstable_quicksort$lt (x, y) =
  array_unstable_quicksort$cmp<a> (x, y) < 0

implement {a}
array_unstable_quicksort$cmp (x, y) =
  (* This default is the same as for array_quicksort$cmp in the
     prelude. *)
  gcompare_ref_ref<a> (x, y)

#define DEFAULT_SMALL_SORT_THRESHOLD 80

implement {a}
array_unstable_quicksort$small () =
  i2sz DEFAULT_SMALL_SORT_THRESHOLD

implement {a}
array_unstable_quicksort$small_sort (arr, n) =
  array_unstable_quicksort_small_sort_default (arr, n)

implement {a}
array_unstable_quicksort_small_sort_default (arr, n) =
  array_unstable_quicksort_small_sort_insertion (arr, n)

implement {a}
array_unstable_quicksort$pivot_index {n} (arr, n) =
  array_unstable_quicksort_pivot_index_default<a> {n} (arr, n)

implement {a}
array_unstable_quicksort_pivot_index_default {n} (arr, n) =
  array_unstable_quicksort_pivot_index_median_of_three<a> {n} (arr, n)

implement {a}
array_unstable_quicksort_pivot_index_random {n} (arr, n) =
  quicksorts_pivot_index_random<a> {n} (arr, n)

implement {a}
array_unstable_quicksort_pivot_index_middle {n} (arr, n) =
  quicksorts_pivot_index_middle<a> {n} (arr, n)

implement {a}
array_unstable_quicksort_pivot_index_median_of_three {n} (arr, n) =
  let
    implement
    quicksorts$array_element_lt<a> (arr, i, j) =
      array_element_lt<a> (arr, i, j)
  in
    quicksorts_pivot_index_median_of_three<a> {n} (arr, n)
  end

implement {a}
array_unstable_quicksort_pivot_index_median_of_three_random
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
  (* Greater than (but not equal to). *)
  lt<a> (pf_arr | bp_j, bp_i)

implement {a}
array_unstable_quicksort_small_sort_insertion {n} (arr, n) =
  insertion_sort<a> (arr, n)

fn {a : vt@ype}
shell_sort_gap_pass
          {p_arr  : addr}
          {n      : int}
          {gap    : pos | gap <= n}
          (pf_arr : !array_v (a, p_arr, n) |
           bp_arr : bptr_anchor (a, p_arr),
           bp_n   : bptr (a, p_arr, n),
           gap    : size_t gap)
    :<!wrt> void =
  let
    fun
    loop {i : int | gap <= i; i <= n}
         .<n - i>.
         (pf_arr : !array_v (a, p_arr, n) |
          bp_i   : bptr (a, p_arr, i))
        :<!wrt> void =
      if bp_i <> bp_n then
        let
          fun
          inner_loop {m : int | 0 <= m}
                     {j : int | 0 <= j; j <= i}
                     .<j>.
                     (pf_arr : !array_v (a, p_arr, n),
                      pf_m   : MUL (m, gap, i - j) |
                      bp_j   : bptr (a, p_arr, j))
              :<> [m1 : int | 0 <= m1]
                  [k  : int | 0 <= k]
                  @(MUL (m1, gap, i - k) | bptr (a, p_arr, k)) =
            if bp_j - bp_arr < gap then
              @(pf_m | bp_j)
            else
              let
                val bp_j1 = bptr_sub<a> (bp_j, gap)
              in
                if lt<a> (pf_arr | bp_i, bp_j1) then
                  inner_loop (pf_arr, MULind pf_m | bp_j1)
                else
                  @(pf_m | bp_j)
              end

          val [m : int]
              [k : int]
              @(pf_m | bp_k) =
                inner_loop (pf_arr, mul_make {0, gap} () | bp_i)
          prval () = mul_elim pf_m
          prval () = prop_verify {k + (m * gap) == i} ()
        in
          subcirculate_right_with_gap
            {p_arr} {n} {k, m, gap} (pf_arr | bp_k, bp_i, gap);
          loop (pf_arr | succ bp_i)
        end
  in
    loop (pf_arr | bp_arr + gap)
  end

implement {a}
array_unstable_quicksort_small_sort_shell {n} (arr, n) =
  if i2sz 2 <= n then
    let
      prval pf_arr = view@ arr
      val p_arr = addr@ arr
      prval [p_arr : addr] EQADDR () = eqaddr_make_ptr p_arr
      val bp_arr = ptr2bptr_anchor p_arr
      val bp_n = bp_arr + n

      macdef pass (gap) =
        if array_unstable_quicksort$small () >= i2sz ,(gap) then
          if n >= i2sz ,(gap) then
            shell_sort_gap_pass<a>
              (pf_arr | bp_arr, bp_n, i2sz ,(gap))
    in
      (* See https://oeis.org/A102549 for the gap sequence,
         which is thanks to Marcin Ciura and Roman Dovgopol. *)
      pass 1750;
      pass 701;
      pass 301;
      pass 132;
      pass 57;
      pass 23;
      pass 10;
      pass 4;
      shell_sort_gap_pass<a> (pf_arr | bp_arr, bp_n, i2sz 1);

      { prval () = view@ arr := pf_arr }
    end

implement {a}
array_unstable_quicksort$partition (arr, n) =
  array_unstable_quicksort_partition_default<a> (arr, n)

implement {a}
array_unstable_quicksort_partition_default (arr, n) =
  array_unstable_quicksort_partition_method_1<a> (arr, n)

implement {a}
array_unstable_quicksort_partition_method_1 {n} (arr, n) =
  let
    prval pf_arr = view@ arr
    val p_arr = addr@ arr
    prval [p_arr : addr] EQADDR () = eqaddr_make_ptr p_arr
    val bp_arr = ptr2bptr_anchor p_arr
    val bp_n = bp_arr + n

    fn {}
    move_i_rightwards
              {i, i_pivot : int | 0 <= i;
                                  i <= i_pivot;
                                  i_pivot <= n - 1}
              (pf_arr   : !array_v (a, p_arr, n) |
               bp_i     : bptr (a, p_arr, i),
               bp_pivot : bptr (a, p_arr, i_pivot))
        :<> [i1 : int | i <= i1; i1 <= i_pivot]
            bptr (a, p_arr, i1) =
      let
        fun
        loop {i : int | 0 <= i; i <= i_pivot}
             .<i_pivot - i>.
             (pf_arr : !array_v (a, p_arr, n) |
              bp_i   : bptr (a, p_arr, i))
            :<> [i1 : int | i <= i1; i1 <= i_pivot]
                bptr (a, p_arr, i1) =
          if bp_i = bp_pivot then
            bp_i
          else if ~lt<a> (pf_arr | bp_i, bp_pivot) then
            bp_i
          else
            loop (pf_arr | succ bp_i)
      in
        loop (pf_arr | bp_i)
      end

    fn {}
    move_j_leftwards
              {i_pivot, j : int | 0 <= i_pivot;
                                  i_pivot <= j;
                                  j <= n - 1}
              (pf_arr   : !array_v (a, p_arr, n) |
               bp_j     : bptr (a, p_arr, j),
               bp_pivot : bptr (a, p_arr, i_pivot))
        :<> [j1 : nat | i_pivot <= j1; j1 <= j]
            bptr (a, p_arr, j1) =
      let
        fun
        loop {j : int | i_pivot <= j; j <= n - 1}
             .<j - i_pivot>.
             (pf_arr : !array_v (a, p_arr, n) |
              bp_j   : bptr (a, p_arr, j))
            :<> [j1 : nat | i_pivot <= j1; j1 <= j]
                bptr (a, p_arr, j1) =
          if bp_j = bp_pivot then
            bp_j
          else if ~lt<a> (pf_arr | bp_pivot, bp_j) then
            bp_j
          else
            loop (pf_arr | pred bp_j)
      in
        loop (pf_arr | bp_j)
      end

    fun
    loop {i, j    : int | 0 <= i; i <= j; j <= n - 1}
         {i_pivot : int | i <= i_pivot; i_pivot <= j}
         .<j - i>.
         (pf_arr   : !array_v (a, p_arr, n) |
          bp_i     : bptr (a, p_arr, i),
          bp_j     : bptr (a, p_arr, j),
          bp_pivot : bptr (a, p_arr, i_pivot))
        :<!wrt> [i_final : nat | i_final <= n - 1]
                bptr (a, p_arr, i_final) =
      let
        val [i1 : int] bp_i1 =
          move_i_rightwards<> (pf_arr | bp_i, bp_pivot)
        and [j1 : int] bp_j1 =
          move_j_leftwards<> (pf_arr | bp_j, bp_pivot)

        prval () = prop_verify {i1 <= j1} ()

        val diff = bp_j1 - bp_i1
      in
        if diff = i2sz 0 then
          bp_pivot
        else
          let
            prval () = prop_verify {i1 < j1} ()
          in
            interchange<a> (pf_arr | bp_i1, bp_j1);
            if bp_i1 = bp_pivot then
              let               (* Keep the pivot between i and j. *)
                val bp_pivot1 = bptr_sub<a> (bp_j1, half diff)
              in
                interchange<a> (pf_arr | bp_pivot1, bp_j1);
                loop (pf_arr | succ bp_i1, bp_j1, bp_pivot1)
              end
            else if bp_j1 = bp_pivot then
              let               (* Keep the pivot between i and j. *)
                val bp_pivot1 = bp_i1 + half diff
              in
                interchange<a> (pf_arr | bp_pivot1, bp_i1);
                loop (pf_arr | bp_i1, pred bp_j1, bp_pivot1)
              end
            else
              loop (pf_arr | succ bp_i1, pred bp_j1, bp_pivot)
          end
      end

    val i_pivot_initial =
      array_unstable_quicksort$pivot_index<a> (arr, n)
    val bp_pivot_final =
      loop (pf_arr | bp_arr, pred bp_n,
                     bp_arr + i_pivot_initial)

    prval () = view@ arr := pf_arr
  in
    bp_pivot_final - bp_arr
  end

implement {a}
array_unstable_quicksort_partition_method_2 {n} (arr, n) =
  let
    macdef andalso1 (p, q) =
      if ,(p) then
        ,(q)
      else
        false

    prval pf_arr = view@ arr
    val p_arr = addr@ arr
    prval [p_arr : addr] EQADDR () = eqaddr_make_ptr p_arr
    val bp_arr = ptr2bptr_anchor p_arr
    val bp_n = bp_arr + n

    fn {}
    move_i_rightwards
              {i, j     : nat | i <= j; j <= n - 1}
              {i_pivot  : nat | i_pivot <= n - 1}
              (pf_arr   : !array_v (a, p_arr, n) |
               bp_i     : bptr (a, p_arr, i),
               bp_j     : bptr (a, p_arr, j),
               bp_pivot : bptr (a, p_arr, i_pivot))
        :<> [i1 : int | i <= i1; i1 <= j]
            bptr (a, p_arr, i1) =
      let
        fun
        loop {i : nat | i <= j}
             .<j - i>.
             (pf_arr : !array_v (a, p_arr, n) |
              bp_i   : bptr (a, p_arr, i))
            :<> [i1 : int | i <= i1; i1 <= j]
                bptr (a, p_arr, i1) =
          if bp_i = bp_j then
            bp_i
          else if bp_i = bp_pivot then
            bp_i
          else if ~lt<a> (pf_arr | bp_i, bp_pivot) then
            bp_i
          else
            loop (pf_arr | succ bp_i)
      in
        loop (pf_arr | bp_i)
      end

    fn {}
    move_j_leftwards
              {i, j     : nat | i <= j; j <= n - 1}
              {i_pivot  : nat | i_pivot <= n - 1}
              (pf_arr   : !array_v (a, p_arr, n) |
               bp_i     : bptr (a, p_arr, i),
               bp_j     : bptr (a, p_arr, j),
               bp_pivot : bptr (a, p_arr, i_pivot))
        :<> [j1 : nat | i <= j1; j1 <= j]
            bptr (a, p_arr, j1) =
      let
        fun
        loop {j : nat | i <= j; j <= n - 1}
             .<j - i>.
             (pf_arr : !array_v (a, p_arr, n) |
              bp_j   : bptr (a, p_arr, j))
            :<> [j1 : nat | i <= j1; j1 <= j]
                bptr (a, p_arr, j1) =
          if bp_i = bp_j then
            bp_j
          else if bp_j = bp_pivot then
            bp_j
          else if ~lt<a> (pf_arr | bp_pivot, bp_j) then
            bp_j
          else
            loop (pf_arr | pred bp_j)
      in
        loop (pf_arr | bp_j)
      end

    fun
    loop {i, j    : nat | i <= j; j <= n - 1}
         {i_pivot : nat | i_pivot <= n - 1}
         .<j - i>.
         (pf_arr   : !array_v (a, p_arr, n) |
          bp_i     : bptr (a, p_arr, i),
          bp_j     : bptr (a, p_arr, j),
          bp_pivot : bptr (a, p_arr, i_pivot))
        :<!wrt> [i_pivot_final : nat | i_pivot_final <= n - 1]
                bptr (a, p_arr, i_pivot_final) =
      if bp_i <> bp_j then
        let
          val () = interchange<a> (pf_arr | bp_i, bp_j)

          (* The interchange may have just moved the pivot. *)
          val bp_pivot =
            (if bp_pivot = bp_i then
               bp_j
             else if bp_pivot = bp_j then
               bp_i
             else
               bp_pivot) : [k : nat | k <= n - 1] bptr (a, p_arr, k)

          val bp_i =
            move_i_rightwards<>
              (pf_arr | succ bp_i, bp_j, bp_pivot)
        in
          if bp_i <> bp_j then
            let
              val bp_j =
                move_j_leftwards<>
                  (pf_arr | bp_i, pred bp_j, bp_pivot)
            in
              loop (pf_arr | bp_i, bp_j, bp_pivot)
            end
          else
            (* The following will be the last call to the top of the
               loop. *)
            loop (pf_arr | bp_i, bp_j, bp_pivot)
        end
      else if (bp_j <> bp_pivot) \andalso1
                lt<a> (pf_arr | bp_pivot, bp_j) then
        begin
          (* Put the pivot between the two parts of the partition. *)
          if (bp_pivot < bp_j) then
            begin
              interchange<a> (pf_arr | bp_pivot, pred bp_j);
              pred bp_j
            end
          else
            begin
              interchange<a> (pf_arr | bp_pivot, bp_j);
              bp_j
            end
        end
      else
        begin
          (* Put the pivot between the two parts of the partition. *)
          if (bp_j < bp_pivot) then
            begin
              interchange<a> (pf_arr | bp_pivot, succ bp_j);
              succ bp_j
            end
          else
            begin
              interchange<a> (pf_arr | bp_pivot, bp_j);
              bp_j
            end
        end

    val i_pivot_initial =
      array_unstable_quicksort$pivot_index<a> (!p_arr, n)    
    val bp_pivot_initial = bp_arr + i_pivot_initial

    (* Put the pivot in the middle, so it will be as near to other
       elements as possible. *)
    val i_pivot_middle = half n
    val bp_pivot_middle = bp_arr + i_pivot_middle
    val () = interchange<a> (pf_arr | bp_pivot_initial,
                                      bp_pivot_middle)

    val bp_i =
      move_i_rightwards<>
        (pf_arr | bp_arr, pred bp_n, bp_pivot_middle)
    val bp_j =
      move_j_leftwards<>
        (pf_arr | bp_i, pred bp_n, bp_pivot_middle)

    val bp_pivot_final = loop (pf_arr | bp_i, bp_j, bp_pivot_middle)

    prval () = view@ arr := pf_arr
  in
    bp_pivot_final - bp_arr
  end

fn {a : vt@ype}
array_unstable_sort
          {p_arr  : addr}
          {n      : nat}
          (pf_arr : !array_v (a, p_arr, n) |
           p_arr  : ptr p_arr,
           n      : size_t n)
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
           (stk : &stk_vt (p_stk, depth, size_sum)
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
            if n1 <= array_unstable_quicksort$small<a> () then
              let
                val () =
                  array_unstable_quicksort$small_sort<a> (!p_arr1, n1)
                prval () = fpf_arr1 pf_arr1
              in
                loop stk
              end
            else
              let
                val [n1_le : int] n1_le =
                  array_unstable_quicksort$partition<a> (!p_arr1, n1)

                val p_le = p_arr1
                and p_ge = ptr_add<a> (p_arr1, succ n1_le)
                and n1_ge = n1 - succ n1_le

                prval [n1 : int] EQINT () = eqint_make_guint n1
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
                    val () = loop stk
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
                    val () = loop stk
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
                    val () = loop stk
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
                    val () = loop stk
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
      val () = loop stk
      prval () = view@ stk_storage := stk.pf
    in
    end

implement {a}
array_unstable_quicksort {n} {m1} (arr, n) =
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
      val () = array_unstable_sort<a> (pf_arr1 | addr@ arr, n)
      prval () = view@ arr := array_v_unsplit (pf_arr1, pf_arr2)
    in
    end
