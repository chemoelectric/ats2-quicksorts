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

#ifdef UNSTABLE_QUICKSORT_STK_MAX #then
  #define STK_MAX UNSTABLE_QUICKSORT_STK_MAX
#else
  #define STK_MAX 64   (* Enough for arrays of up to 2**64 entries. *)
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
  (* FIXME: DECIDE WHICH STRATEGY SHOULD BE THE DEFAULT *)
  array_unstable_quicksort_pivot_index_random<a> {n} (arr, n)

implement {a}
array_unstable_quicksort_pivot_index_random {n} (arr, n) =
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
array_unstable_quicksort_pivot_index_middle (arr, n) =
  half n

implement {a}            (* FIXME: MAKE THIS REARRANGE THE ELEMENTS *)
array_unstable_quicksort_pivot_index_median_of_three {n} (arr, n) =
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
      array_unstable_quicksort$pivot_index<a> (!p_arr, n)
    prval @(pf_before, pf_more) =
      array_v_split {a} {p_arr} {n} {n_before} pf_arr
    prval @(pf_pivot, pf_after) = array_v_uncons pf_more
  in
    @(pf_before, pf_pivot, pf_after | n_before)
  end

fn {a : vt@ype}
move_pivot_to_end
          {n         : pos}
          {n_before  : nat | n_before + 1 <= n}
          {p_arr     : addr}
          (pf_before : array_v (a, p_arr, n_before),
           pf_pivot  : a @ (p_arr + (n_before * sizeof a)),
           pf_after  : array_v
                         (a, p_arr + (n_before * sizeof a) + sizeof a,
                          n - n_before - 1) |
           p_arr     : ptr p_arr,
           n         : size_t n,
           n_before  : size_t n_before)
    :<!wrt> @(array_v (a, p_arr, n - 1),
              a @ (p_arr + (n * sizeof a) - sizeof a) |
              ) =
  if n_before = pred n then
    let                         (* The pivot already is at the end. *)
      prval () = array_v_unnil pf_after
      prval () = lemma_mul_isfun {n_before, sizeof a}
                                 {n - 1, sizeof a} ()
    in
      @(pf_before, pf_pivot | )
    end
  else
    let                 (* Exchange the pivot with the end element. *)
      val p_pivot = ptr_add<a> (p_arr, n_before)
      and p_end = ptr_add<a> (p_arr, n - 1)
      prval @(pf_after, pf_end) = array_v_unextend pf_after
      val () = ptr_exch<a> (pf_end | p_end, !p_pivot)
      prval pf_arr =
        array_v_unsplit (pf_before, array_v_cons (pf_pivot, pf_after))
    in
      @(pf_arr, pf_end | )
    end
