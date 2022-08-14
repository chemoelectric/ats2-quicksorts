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
      array_unstable_quicksort$lt<a> (!(ptr_add<a> (addr@ arr, i)),
                                      !(ptr_add<a> (addr@ arr, j)))
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
  array_unstable_quicksort_pivot_index_random<a> {n} (arr, n)

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
          {n      : int | 2 <= n}
          {p_arr  : addr}
          (pf_arr : !array_v (a, p_arr, n) >> _ |
           p_arr  : ptr p_arr,
           n      : size_t n)
    :<!wrt> [prefix_length : int | 2 <= prefix_length;
                                   prefix_length <= n]
            size_t prefix_length =
  let
    macdef arr = !p_arr
  in
    if ~array_element_lt<a> (arr, i2sz 1, i2sz 0) then
      let                       (* Non-decreasing order. *)
        fun
        loop {pfx_len : int | 2 <= pfx_len; pfx_len <= n}
             .<n - pfx_len>.
             (arr     : &array (a, n) >> _,
              pfx_len : size_t pfx_len)
            :<> [prefix_length : int | 2 <= prefix_length;
                                       prefix_length <= n]
                size_t prefix_length =
          if pfx_len = n then
            pfx_len
          else if array_element_lt<a>
                    {n} {pfx_len, pfx_len - 1}
                    (arr, pfx_len, pred pfx_len) then
            pfx_len
          else
            loop (arr, succ pfx_len)

        val prefix_length = loop (arr, i2sz 2)
      in
        prefix_length
      end
    else
      let      (* Non-increasing order. This branch sorts unstably. *)
        fun
        loop {pfx_len : int | 2 <= pfx_len; pfx_len <= n}
             .<n - pfx_len>.
             (arr     : &array (a, n) >> _,
              pfx_len : size_t pfx_len)
            :<> [prefix_length : int | 2 <= prefix_length;
                                       prefix_length <= n]
                size_t prefix_length =
          if pfx_len = n then
            pfx_len
          else if array_element_lt<a>
                     {n} {pfx_len - 1, pfx_len}
                     (arr, pred pfx_len, pfx_len) then
            pfx_len
          else
            loop (arr, succ pfx_len)

        val prefix_length = loop (arr, i2sz 2)
      in
        array_subreverse<a> (arr, i2sz 0, prefix_length);
        prefix_length
      end
  end

fn {a  : vt@ype}
insertion_position
          {n      : int}
          {i      : pos | i < n}
          {p_arr  : addr}
          (pf_arr : !array_v (a, p_arr, n) >> _ |
           p_arr  : ptr p_arr,
           i      : size_t i)
    :<> [j : nat | j <= i]
        size_t j =
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
         (arr : &array (a, n),
          j   : size_t j,
          k   : size_t k)
        :<> [j1 : nat | j1 <= i]
            size_t j1 =
      if j <> k then
        let
          val h = k - half (k - j) (* (j + k) ceildiv 2 *)
         in
          if array_element_lt<a> {n} (arr, i, h) then
            loop (arr, j, pred h)
          else
            loop (arr, h, k)
        end
      else if j <> i2sz 0 then
        succ j
      else if array_element_lt<a> {n} (arr, i, i2sz 0) then
        i2sz 0
      else
        i2sz 1
  in
    loop (!p_arr, i2sz 0, pred i)
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
            array_subcirculate_right<a> (!p_arr, j, i);
            loop (pf_arr | succ i)
          end

      val prefix_length =
        make_an_ordered_prefix<a> (pf_arr | p_arr, n)
    in
      loop (pf_arr | prefix_length)
    end

fn {a : vt@ype}
move_i_rightwards
          {n       : int}
          {i, j    : nat | i <= j; j <= n - 1}
          {i_pivot : nat | i_pivot <= n - 1}
          (arr     : &array (a, n),
           i       : size_t i,
           j       : size_t j,
           i_pivot : size_t i_pivot)
    :<> [i1 : int | i <= i1; i1 <= j]
        size_t i1 =
  let
    fun
    loop {i : nat | i <= j}
         .<j - i>.
         (arr : &array (a, n),
          i   : size_t i)
        :<> [i1 : int | i <= i1; i1 <= j]
            size_t i1 =
      if i = j then
        i
      else if i = i_pivot then
        i
      else if ~array_element_lt<a> (arr, i, i_pivot) then
        i
      else
        loop (arr, succ i)
  in
    loop (arr, i)
  end

fn {a : vt@ype}
move_j_leftwards
          {n       : int}
          {i, j    : nat | i <= j; j <= n - 1}
          {i_pivot : nat | i_pivot <= n - 1}
          (arr     : &array (a, n),
           i       : size_t i,
           j       : size_t j,
           i_pivot : size_t i_pivot)
    :<> [j1 : nat | i <= j1; j1 <= j]
        size_t j1 =
  let
    fun
    loop {j : nat | i <= j; j <= n - 1}
         .<j - i>.
         (arr : &array (a, n),
          j   : size_t j)
        :<> [j1 : nat | i <= j1; j1 <= j]
            size_t j1 =
      if i = j then
        j
      else if j = i_pivot then
        j
      else if ~array_element_lt<a> (arr, i_pivot, j) then
        j
      else
        loop (arr, pred j)
  in
    loop (arr, j)
  end

fn {a : vt@ype}
partition {n     : pos}
          (arr   : &array (a, n),
           n     : size_t n)
    :<!wrt> [i_pivot_final : nat | i_pivot_final < n]
            size_t i_pivot_final =
  let
    macdef lt (arr, p, q) =
      if ,(p) = ,(q) then
        false
      else
        array_element_lt<a> (,(arr), ,(p), ,(q))

    fun
    loop {i, j    : nat | i <= j; j <= n - 1}
         {i_pivot : nat | i_pivot <= n - 1}
         .<j - i>.
         (arr     : &array (a, n),
          i       : size_t i,
          j       : size_t j,
          i_pivot : size_t i_pivot)
        :<!wrt> [i_pivot_final : nat | i_pivot_final <= n - 1]
                size_t i_pivot_final =
      if i <> j then
        let
          val () = array_interchange<a> (arr, i, j)

          (* array_interchange may have just moved the pivot. *)
          val i_pivot =
            (if i_pivot = i then
               j
             else if i_pivot = j then
               i
             else
               i_pivot) : [k : nat | k <= n - 1] size_t k

          val i = move_i_rightwards<a> (arr, succ i, j, i_pivot)
        in
          if i <> j then
            let
              val j = move_j_leftwards<a> (arr, i, pred j, i_pivot)
            in
              loop (arr, i, j, i_pivot)
            end
          else
            (* The following will be the last call to the top of the
               loop. *)
            loop (arr, i, j, i_pivot)
        end
      else if lt (arr, i_pivot, j) then
        begin
          (* Put the pivot between the two parts of the partition. *)
          if (i_pivot < j) then
            begin
              array_interchange<a> (arr, i_pivot, pred j);
              pred j
            end
          else
            begin
              array_interchange<a> (arr, i_pivot, j);
              j
            end
        end
      else
        begin
          (* Put the pivot between the two parts of the partition. *)
          if (j < i_pivot) then
            begin
              array_interchange<a> (arr, i_pivot, succ j);
              succ j
            end
          else
            begin
              array_interchange<a> (arr, i_pivot, j);
              j
            end
        end

    val i_pivot_initial =
      array_unstable_quicksort$pivot_index<a> (arr, n)

    (* Put the pivot in the middle, so it will be as near to other
       elements as possible. *)
    val i_pivot_middle = half n
    val () = array_interchange<a> (arr, i_pivot_initial,
                                   i_pivot_middle)

    val i = move_i_rightwards<a> (arr, i2sz 0, pred n, i_pivot_middle)
    val j = move_j_leftwards<a> (arr, i, pred n, i_pivot_middle)
  in
    loop (arr, i, j, i_pivot_middle)
  end

fn {a : vt@ype}
array_unstable_sort
          {n         : int}
          (arr       : &array (a, n),
           n         : size_t n)
    :<!wrt> void =
  if n <= 1 then
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
                  array_insertion_sort<a> (pf_arr1 | p_arr1, n1)
                prval () = fpf_arr1 pf_arr1
              in
                loop stk
              end
            else
              let
                val [n1_le : int] n1_le = partition<a> (!p_arr1, n1)

                val p_le = p_arr1
                and p_ge = ptr_add<a> (p_arr1, succ n1_le)
                and n1_ge = n1 - succ n1_le

                prval [n1 : int] () = g1uint_get_static n1
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

      prval () = lemma_array_param arr

      var stk_storage =
        @[stk_entry_vt][STK_MAX] (@(the_null_ptr, i2sz 0))
      var stk = stk_vt_make (view@ stk_storage | addr@ stk_storage)

      val () = stk_vt_push<a> (view@ arr | addr@ arr, n, stk)
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
      val () = array_unstable_sort<a> {n} (!(addr@ arr), n)
      prval () = view@ arr := array_v_unsplit (pf_arr1, pf_arr2)
    in
    end
