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
staload "quicksorts/SATS/uptr.sats"
staload _ = "quicksorts/DATS/uptr.dats"
staload UN = "prelude/SATS/unsafe.sats"

#define DEFAULT_ARRAY_INSERTION_SORT_THRESHOLD 80

#ifdef ATS2_QUICKSORTS_CHAR_BIT #then
  #define CHAR_BIT ATS2_QUICKSORTS_CHAR_BIT
#else
  #define CHAR_BIT 8
#endif

#ifdef ATS2_QUICKSORTS_STK_MAX #then
  #define STK_MAX ATS2_QUICKSORTS_STK_MAX
#else
  #define STK_MAX 64         (* Enough for size_t of up to 64 bits. *)
#endif

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
elem_lt_uptr_uptr
          {p      : addr}
          {i, j   : int}
          (pf_i   : !a @ (p + (i * sizeof a)),
           pf_j   : !a @ (p + (j * sizeof a)) |
           anchor : uptr_anchor (a, p),
           up_i   : uptr (a, p, i),
           up_j   : uptr (a, p, j))
    :<> bool =
  elem_lt_ptr1_ptr1<a> (pf_i, pf_j | uptr2ptr (anchor, up_i),
                                     uptr2ptr (anchor, up_j))

fn {a : vt@ype}
elem_lt_array_uptr_uptr
          {p_arr  : addr}
          {n      : int}
          {i, j   : nat | i <= n - 1; j <= n - 1; i != j}
          (pf_arr : !array_v (a, p_arr, n) |
           up_arr : uptr_anchor (a, p_arr),
           up_i   : uptr (a, p_arr, i),
           up_j   : uptr (a, p_arr, j))
    :<> bool =
  let
    prval @(pf_i, pf_j, fpf) =
      array_v_takeout2 {a} {p_arr} {n} {i, j} pf_arr
    val is_lt =
      elem_lt_uptr_uptr<a> (pf_i, pf_j | up_arr, up_i, up_j)
    prval () = pf_arr := fpf (pf_i, pf_j)
  in
    is_lt
  end

overload lt with elem_lt_ptr1_ptr1
overload lt with elem_lt_uptr_uptr
overload lt with elem_lt_array_uptr_uptr

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

implement {a}
array_unstable_quicksort$small () =
  i2sz DEFAULT_ARRAY_INSERTION_SORT_THRESHOLD

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

fn {a : vt@ype}
make_an_ordered_prefix
          {p_arr  : addr}
          {n      : int | 2 <= n}
          (pf_arr : !array_v (a, p_arr, n) |
           up_arr : uptr_anchor (a, p_arr),
           up_n   : uptr (a, p_arr, n))
    :<!wrt> [pfx_len : int | 2 <= pfx_len; pfx_len <= n]
            uptr (a, p_arr, pfx_len) =
  if ~lt<a> (pf_arr | up_arr, uptr_succ<a> up_arr, up_arr) then
    let                       (* Non-decreasing order. *)
      fun
      loop {pfx_len : int | 2 <= pfx_len; pfx_len <= n}
           .<n - pfx_len>.
           (pf_arr  : !array_v (a, p_arr, n) |
            up      : uptr (a, p_arr, pfx_len))
          :<> [pfx_len : int | 2 <= pfx_len; pfx_len <= n]
              uptr (a, p_arr, pfx_len) =
        if up = up_n then
          up
        else if lt<a> (pf_arr | up_arr, up, uptr_pred<a> up) then
          up
        else
          loop (pf_arr | uptr_succ<a> up)
    in
      loop (pf_arr | uptr_add<a> (up_arr, 2))
    end
  else
    let      (* Non-increasing order. This branch sorts unstably. *)
      fun
      loop {pfx_len : int | 2 <= pfx_len; pfx_len <= n}
           .<n - pfx_len>.
           (pf_arr  : !array_v (a, p_arr, n) |
            up      : uptr (a, p_arr, pfx_len))
          :<> [pfx_len : int | 2 <= pfx_len; pfx_len <= n]
              uptr (a, p_arr, pfx_len) =
        if up = up_n then
          up
        else if lt<a> (pf_arr | up_arr, uptr_pred<a> up, up) then
          up
        else
          loop (pf_arr | uptr_succ<a> up)

      val up = loop (pf_arr | uptr_add<a> (up_arr, 2))
    in
      subreverse<a> (pf_arr | up_arr, up_arr, up);
      up
    end

fn {a  : vt@ype}
insertion_position
          {p_arr  : addr}
          {n      : int}
          {i      : pos | i < n}
          (pf_arr : !array_v (a, p_arr, n) |
           up_arr : uptr_anchor (a, p_arr),
           up_i   : uptr (a, p_arr, i))
    :<> [j : nat | j <= i]
        uptr (a, p_arr, j) =
  (*
    A binary search.

    References:

      * H. Bottenbruch, "Structure and use of ALGOL 60", Journal of
        the ACM, Volume 9, Issue 2, April 1962, pp.161-221.
        https://doi.org/10.1145/321119.321120

        The general algorithm is described on pages 214 and 215.

      * https://en.wikipedia.org/w/index.php?title=Binary_search_algorithm&oldid=1062988272#Alternative_procedure
  *)
  let
    fun
    loop {j, k : int | 0 <= j; j <= k; k < i}
         .<k - j>.
         (pf_arr : !array_v (a, p_arr, n) |
          up_j   : uptr (a, p_arr, j),
          up_k   : uptr (a, p_arr, k))
        :<> [j1 : nat | j1 <= i]
            uptr (a, p_arr, j1) =
      if up_j <> up_k then
        let
          (* Find the point that is halfway between up_j and up_k,
             rounding towards up_k. *)
          stadef h = k - ((k - j) / 2)
          val up_h : uptr (a, p_arr, h) =
            uptr_sub<a>
              (up_k, half (uptr_diff_unsigned<a> (up_k, up_j)))
        in
          if lt<a> (pf_arr | up_arr, up_i, up_h) then
            loop (pf_arr | up_j, uptr_pred<a> up_h)
          else
            loop (pf_arr | up_h, up_k)
        end
      else if up_j <> up_arr then
        uptr_succ<a> up_j
      else if lt<a> (pf_arr | up_arr, up_i, up_arr) then
        up_arr
      else
        uptr_succ<a> up_arr
  in
    loop (pf_arr | up_arr, uptr_pred<a> up_i)
  end

fn {a : vt@ype}
array_insertion_sort
          {p_arr  : addr}
          {n      : nat}
          (pf_arr : !array_v (a, p_arr, n) >> _ |
           p_arr  : ptr p_arr,
           n      : size_t n)
    :<!wrt> void =
  if i2sz 2 <= n then
    let
      val up_arr = ptr2uptr_anchor p_arr
      val up_n = uptr_add<a> (up_arr, n)
      val up_i = make_an_ordered_prefix<a> (pf_arr | up_arr, up_n)

      fun
      loop {i : pos | i <= n}
           .<n - i>.
           (pf_arr : !array_v (a, p_arr, n) >> _ |
            up_i   : uptr (a, p_arr, i))
          :<!wrt> void =
        if up_i <> up_n then
          let
            val up_j = insertion_position<a> (pf_arr | up_arr, up_i)
          in
            subcirculate_right<a> (pf_arr | up_arr, up_j, up_i);
            loop (pf_arr | uptr_succ<a> up_i)
          end
    in
      loop (pf_arr | up_i)
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
    val up_arr = ptr2uptr_anchor p_arr
    val up_n = uptr_add<a> (up_arr, n)

    fn {}
    move_i_rightwards
              {i, i_pivot : int | 0 <= i;
                                  i <= i_pivot;
                                  i_pivot <= n - 1}
              (pf_arr   : !array_v (a, p_arr, n) |
               up_i     : uptr (a, p_arr, i),
               up_pivot : uptr (a, p_arr, i_pivot))
        :<> [i1 : int | i <= i1; i1 <= i_pivot]
            uptr (a, p_arr, i1) =
      let
        fun
        loop {i : int | 0 <= i; i <= i_pivot}
             .<i_pivot - i>.
             (pf_arr : !array_v (a, p_arr, n) |
              up_i   : uptr (a, p_arr, i))
            :<> [i1 : int | i <= i1; i1 <= i_pivot]
                uptr (a, p_arr, i1) =
          if up_i = up_pivot then
            up_i
          else if ~lt<a> (pf_arr | up_arr, up_i, up_pivot) then
            up_i
          else
            loop (pf_arr | uptr_succ<a> up_i)
      in
        loop (pf_arr | up_i)
      end

    fn {}
    move_j_leftwards
              {i_pivot, j : int | 0 <= i_pivot;
                                  i_pivot <= j;
                                  j <= n - 1}
              (pf_arr   : !array_v (a, p_arr, n) |
               up_j     : uptr (a, p_arr, j),
               up_pivot : uptr (a, p_arr, i_pivot))
        :<> [j1 : nat | i_pivot <= j1; j1 <= j]
            uptr (a, p_arr, j1) =
      let
        fun
        loop {j : int | i_pivot <= j; j <= n - 1}
             .<j - i_pivot>.
             (pf_arr : !array_v (a, p_arr, n) |
              up_j   : uptr (a, p_arr, j))
            :<> [j1 : nat | i_pivot <= j1; j1 <= j]
                uptr (a, p_arr, j1) =
          if up_j = up_pivot then
            up_j
          else if ~lt<a> (pf_arr | up_arr, up_pivot, up_j) then
            up_j
          else
            loop (pf_arr | uptr_pred<a> up_j)
      in
        loop (pf_arr | up_j)
      end

    fun
    loop {i, j    : int | 0 <= i; i <= j; j <= n - 1}
         {i_pivot : int | i <= i_pivot; i_pivot <= j}
         .<j - i>.
         (pf_arr   : !array_v (a, p_arr, n) |
          up_i     : uptr (a, p_arr, i),
          up_j     : uptr (a, p_arr, j),
          up_pivot : uptr (a, p_arr, i_pivot))
        :<!wrt> [i_final : nat | i_final <= n - 1]
                uptr (a, p_arr, i_final) =
      let
        val [i1 : int] up_i1 =
          move_i_rightwards<> (pf_arr | up_i, up_pivot)
        and [j1 : int] up_j1 =
          move_j_leftwards<> (pf_arr | up_j, up_pivot)

        prval () = prop_verify {i1 <= j1} ()

        val diff = uptr_diff_unsigned<a> (up_j1, up_i1)
      in
        if diff = i2sz 0 then
          up_pivot
        else
          let
            prval () = prop_verify {i1 < j1} ()
          in
            interchange<a> (pf_arr | up_arr, up_i1, up_j1);
            if up_i1 = up_pivot then
              let               (* Keep the pivot between i and j. *)
                val up_pivot1 = uptr_sub<a> (up_j1, half diff)
              in
                interchange<a> (pf_arr | up_arr, up_pivot1, up_j1);
                loop (pf_arr | uptr_succ<a> up_i1, up_j1, up_pivot1)
              end
            else if up_j1 = up_pivot then
              let               (* Keep the pivot between i and j. *)
                val up_pivot1 = uptr_add<a> (up_i1, half diff)
              in
                interchange<a> (pf_arr | up_arr, up_pivot1, up_i1);
                loop (pf_arr | up_i1, uptr_pred<a> up_j1, up_pivot1)
              end
            else
              loop (pf_arr | uptr_succ<a> up_i1, uptr_pred<a> up_j1,
                             up_pivot)
          end
      end

    val i_pivot_initial =
      array_unstable_quicksort$pivot_index<a> (arr, n)
    val up_pivot_final =
      loop (pf_arr | up_arr, uptr_pred<a> up_n,
                     uptr_add<a> (up_arr, i_pivot_initial))

    prval () = view@ arr := pf_arr
  in
    uptr_diff_unsigned<a> (up_pivot_final, up_arr)
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
    val up_arr = ptr2uptr_anchor p_arr
    val up_n = uptr_add<a> (up_arr, n)

    fn {}
    move_i_rightwards
              {i, j     : nat | i <= j; j <= n - 1}
              {i_pivot  : nat | i_pivot <= n - 1}
              (pf_arr   : !array_v (a, p_arr, n) |
               up_i     : uptr (a, p_arr, i),
               up_j     : uptr (a, p_arr, j),
               up_pivot : uptr (a, p_arr, i_pivot))
        :<> [i1 : int | i <= i1; i1 <= j]
            uptr (a, p_arr, i1) =
      let
        fun
        loop {i : nat | i <= j}
             .<j - i>.
             (pf_arr : !array_v (a, p_arr, n) |
              up_i   : uptr (a, p_arr, i))
            :<> [i1 : int | i <= i1; i1 <= j]
                uptr (a, p_arr, i1) =
          if up_i = up_j then
            up_i
          else if up_i = up_pivot then
            up_i
          else if ~lt<a> (pf_arr | up_arr, up_i, up_pivot) then
            up_i
          else
            loop (pf_arr | uptr_succ<a> up_i)
      in
        loop (pf_arr | up_i)
      end

    fn {}
    move_j_leftwards
              {i, j     : nat | i <= j; j <= n - 1}
              {i_pivot  : nat | i_pivot <= n - 1}
              (pf_arr   : !array_v (a, p_arr, n) |
               up_i     : uptr (a, p_arr, i),
               up_j     : uptr (a, p_arr, j),
               up_pivot : uptr (a, p_arr, i_pivot))
        :<> [j1 : nat | i <= j1; j1 <= j]
            uptr (a, p_arr, j1) =
      let
        fun
        loop {j : nat | i <= j; j <= n - 1}
             .<j - i>.
             (pf_arr : !array_v (a, p_arr, n) |
              up_j   : uptr (a, p_arr, j))
            :<> [j1 : nat | i <= j1; j1 <= j]
                uptr (a, p_arr, j1) =
          if up_i = up_j then
            up_j
          else if up_j = up_pivot then
            up_j
          else if ~lt<a> (pf_arr | up_arr, up_pivot, up_j) then
            up_j
          else
            loop (pf_arr | uptr_pred<a> up_j)
      in
        loop (pf_arr | up_j)
      end

    fun
    loop {i, j    : nat | i <= j; j <= n - 1}
         {i_pivot : nat | i_pivot <= n - 1}
         .<j - i>.
         (pf_arr   : !array_v (a, p_arr, n) |
          up_i     : uptr (a, p_arr, i),
          up_j     : uptr (a, p_arr, j),
          up_pivot : uptr (a, p_arr, i_pivot))
        :<!wrt> [i_pivot_final : nat | i_pivot_final <= n - 1]
                uptr (a, p_arr, i_pivot_final) =
      if up_i <> up_j then
        let
          val () = interchange<a> (pf_arr | up_arr, up_i, up_j)

          (* The interchange may have just moved the pivot. *)
          val up_pivot =
            (if up_pivot = up_i then
               up_j
             else if up_pivot = up_j then
               up_i
             else
               up_pivot) : [k : nat | k <= n - 1] uptr (a, p_arr, k)

          val up_i =
            move_i_rightwards<>
              (pf_arr | uptr_succ<a> up_i, up_j, up_pivot)
        in
          if up_i <> up_j then
            let
              val up_j =
                move_j_leftwards<>
                  (pf_arr | up_i, uptr_pred<a> up_j, up_pivot)
            in
              loop (pf_arr | up_i, up_j, up_pivot)
            end
          else
            (* The following will be the last call to the top of the
               loop. *)
            loop (pf_arr | up_i, up_j, up_pivot)
        end
      else if (up_j <> up_pivot) \andalso1
                lt<a> (pf_arr | up_arr, up_pivot, up_j) then
        begin
          (* Put the pivot between the two parts of the partition. *)
          if (up_pivot < up_j) then
            begin
              interchange<a> (pf_arr | up_arr, up_pivot,
                                       uptr_pred<a> up_j);
              uptr_pred<a> up_j
            end
          else
            begin
              interchange<a> (pf_arr | up_arr, up_pivot, up_j);
              up_j
            end
        end
      else
        begin
          (* Put the pivot between the two parts of the partition. *)
          if (up_j < up_pivot) then
            begin
              interchange<a> (pf_arr | up_arr, up_pivot,
                                       uptr_succ<a> up_j);
              uptr_succ<a> up_j
            end
          else
            begin
              interchange<a> (pf_arr | up_arr, up_pivot, up_j);
              up_j
            end
        end

    val i_pivot_initial =
      array_unstable_quicksort$pivot_index<a> (!p_arr, n)    
    val up_pivot_initial = uptr_add<a> (up_arr, i_pivot_initial)

    (* Put the pivot in the middle, so it will be as near to other
       elements as possible. *)
    val i_pivot_middle = half n
    val up_pivot_middle = uptr_add<a> (up_arr, i_pivot_middle)
    val () = interchange<a> (pf_arr | up_arr, up_pivot_initial,
                                      up_pivot_middle)

    val up_i =
      move_i_rightwards<>
        (pf_arr | up_arr, uptr_pred<a> up_n, up_pivot_middle)
    val up_j =
      move_j_leftwards<>
        (pf_arr | up_i, uptr_pred<a> up_n, up_pivot_middle)

    val up_pivot_final = loop (pf_arr | up_i, up_j, up_pivot_middle)

    prval () = view@ arr := pf_arr
  in
    uptr_diff_unsigned<a> (up_pivot_final, up_arr)
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
                val () = array_insertion_sort (pf_arr1 | p_arr1, n1)
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

      val () = $effmask_exn
        assertloc (CHAR_BIT * sizeof<size_t> <= i2sz STK_MAX)

      prval @(pf_arr1, pf_arr2) =
        array_v_split {a} {..} {m1} {n} (view@ arr)
      val () = array_unstable_sort<a> (pf_arr1 | addr@ arr, n)
      prval () = view@ arr := array_v_unsplit (pf_arr1, pf_arr2)
    in
    end
