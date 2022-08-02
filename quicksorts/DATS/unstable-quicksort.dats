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

abstype uptr (a : vt@ype, p : addr, n : int, i : int)

fn {a : vt@ype}
ptr2uptr {p_arr  : addr}
         {n      : nat}
         (pf_arr : !array_v (a, p_arr, n) |
          p_arr  : ptr p_arr)
    :<> uptr (a, p_arr, n, 0) =
  $UN.cast ($UN.cast{uintptr} p_arr)

(* One can convert back to a pointer only if the uptr points to an
   array element. *)
fn {a : vt@ype}
uptr2ptr {p_arr  : addr}
         {n      : nat}
         {i      : nat | i < n}
         (pf_arr : !array_v (a, p_arr, n) |
          up     : uptr (a, p_arr, n, i))
    :<> ptr (p_arr + (i * sizeof a)) =
  $UN.cast ($UN.cast{uintptr} up)

fn {a  : vt@ype}
   {tk : tkind}
uptr_g1uint_add
          {p_arr : addr}
          {n     : nat}
          {i     : int}
          {j     : int}
          (up    : uptr (a, p_arr, n, i),
           j     : g1uint (tk, j))
    :<> uptr (a, p_arr, n, i + j) =
  $UN.cast ($UN.cast{uintptr} up -
              $UN.cast{uintptr} (g1u2u j * sizeof<a>))

overload uptr_add with uptr_g1uint_add

fn {a : vt@ype}
uptr_pred {p_arr : addr}
          {n     : nat}
          {i     : int}
          (up    : uptr (a, p_arr, n, i))
    :<> uptr (a, p_arr, n, i - 1) =
  $UN.cast ($UN.cast{uintptr} up - $UN.cast{uintptr} sizeof<a>)

fn {a : vt@ype}
uptr_succ {p_arr : addr}
          {n     : nat}
          {i     : int}
          (up    : uptr (a, p_arr, n, i))
    :<> uptr (a, p_arr, n, i + 1) =
  $UN.cast ($UN.cast{uintptr} up + $UN.cast{uintptr} sizeof<a>)

fn {a : vt@ype}
uptr_eq {p_arr : addr}
        {n     : nat}
        {i, j  : int}
        (up_i  : uptr (a, p_arr, n, i),
         up_j  : uptr (a, p_arr, n, j))
    :<> bool (i == j) =
  (* I can guaranteed two equivalent uptr are equal *only* if they
     were created by arithmetic from the same uptr. *)
  $UN.cast ($UN.cast{uintptr} up_i = $UN.cast{uintptr} up_j)

overload = with uptr_eq

fn {a : vt@ype}
uptr_difference
          {p_arr  : addr}
          {n      : nat}
          {i, j   : nat | j <= i; i < n; 1 <= sizeof a}
          (pf_arr : !array_v (a, p_arr, n) |
           up_i   : uptr (a, p_arr, n, i),
           up_j   : uptr (a, p_arr, n, j))
    :<> size_t (i - j) =
  let
    val ui = $UN.cast{uintptr} up_i
    and uj = $UN.cast{uintptr} up_j
    val diff = $UN.cast{size_t} (ui - uj)
  in
    $UN.cast (diff / sizeof<a>)
  end

fn {a : vt@ype}
uptr_exch {p_arr  : addr}
          {n      : nat}
          {i, j   : nat | i < n; j < n; i != j}
          (pf_arr : !array_v (a, p_arr, n) |
           up_i   : uptr (a, p_arr, n, i),
           up_j   : uptr (a, p_arr, n, j))
    :<!wrt> void =
  let
    val p_i = uptr2ptr<a> (pf_arr | up_i)
    and p_j = uptr2ptr<a> (pf_arr | up_j)
    prval @(pf_i, pf_j, fpf) =
      array_v_takeout2 {a} {..} {n} {i, j} pf_arr
    val () = ptr_exch<a> (pf_i | p_i, !p_j)
    prval () = pf_arr := fpf (pf_i, pf_j)
  in
  end

fn {a : vt@ype}
array_element_lt_uptr
          {p_arr  : addr}
          {n      : int}
          {i, j   : nat | i < n; j < n; i != j}
          (pf_arr : !array_v (a, p_arr, n) |
           up_i   : uptr (a, p_arr, n, i),
           up_j   : uptr (a, p_arr, n, j))
    :<> bool =
  let
    val p_i = uptr2ptr<a> (pf_arr | up_i)
    and p_j = uptr2ptr<a> (pf_arr | up_j)
    prval @(pf_i, pf_j, fpf) =
      array_v_takeout2 {a} {..} {n} {i, j} pf_arr
    val is_lt = array_unstable_quicksort$lt<a> (!p_i, !p_j)
    prval () = pf_arr := fpf (pf_i, pf_j)
  in
    is_lt
  end

fn {a : vt@ype}
array_element_lt_indices
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

overload array_element_lt with array_element_lt_uptr
overload array_element_lt with array_element_lt_indices

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
hoare_partitioning
          {n      : pos}
          {p_arr  : addr}
          (pf_arr : !array_v (a, p_arr, n) |
           p_arr  : ptr p_arr,
           n      : size_t n)
    :<!wrt> [i_final : nat | i_final < n]
            size_t i_final =
  let
    val () = $effmask_exn assertloc (i2sz 0 < sizeof<a>)

    val [i_pivot : int] i_pivot =
      array_unstable_quicksort$pivot_index<a> (!p_arr, n)

    val up_arr = ptr2uptr<a> (pf_arr | p_arr)
    val up_end = uptr_add<a> (up_arr, pred n)
    and up_pivot = uptr_add<a> (up_arr, i_pivot)

    (* Move the pivot out of the way, to the end. *)
    val () =
      if i_pivot <> pred n then
        uptr_exch<a> (pf_arr | up_pivot, up_end)

    fun
    outer_loop {i, j : int | (~1 == i && j == n - 1) ||
                               (0 <= i && i < j && j < n - 1)}
               .<j - i>.
               (pf_arr : !array_v (a, p_arr, n) |
                up_i   : uptr (a, p_arr, n, i),
                up_j   : uptr (a, p_arr, n, j))
        :<!wrt> [k : nat | k <= n - 1]
                uptr (a, p_arr, n, k) =
      let
        (* Move up_i so everything to its left is less than or equal
           to the pivot. *)
        fun
        loop {k, j : int | i < k; k <= j; j <= n - 1}
             .<j - k>.
             (pf_arr : !array_v (a, p_arr, n) |
              up_k   : uptr (a, p_arr, n, k),
              up_j   : uptr (a, p_arr, n, j))
            :<> [k : nat | i < k; k <= j]
                uptr (a, p_arr, n, k) =
          if up_k = up_j then
            up_k
          else
            let
              val p_k = uptr2ptr<a> (pf_arr | up_k)
            in
              if array_element_lt<a> (pf_arr | up_end, up_k) then
                up_k
              else
                loop (pf_arr | uptr_succ<a> up_k, up_j)
            end
        val up_i : uptr (a, p_arr, n, i + 1) = uptr_succ<a> up_i
        val [i1 : int] up_i = loop (pf_arr | up_i, up_j)

        prval () = prop_verify {0 <= i1} ()
        prval () = prop_verify {i1 <= j} ()
      in
        if up_i = up_j then
          up_i
        else
          (* Move up_j so everything to its right is greater than or
             equal to the pivot. *)
          let
            fun
            loop {i, k : nat | i <= k; k < j}
                 .<k>.
                 (pf_arr : !array_v (a, p_arr, n) |
                  up_i   : uptr (a, p_arr, n, i),
                  up_k   : uptr (a, p_arr, n, k))
                :<> [k : int | i <= k; k < j]
                    uptr (a, p_arr, n, k) =
              if up_i = up_k then
                up_k
              else
                let
                  prval () = prop_verify {0 < k} ()
                in
                  if array_element_lt<a> (pf_arr | up_k, up_end) then
                    up_k
                  else
                    loop (pf_arr | up_i, uptr_pred<a> up_k)
                end
            val up_j : uptr (a, p_arr, n, j - 1) = uptr_pred<a> up_j
            val [j1 : int] up_j = loop (pf_arr | up_i, up_j)

            prval () = prop_verify {i1 <= j1} ()
            prval () = prop_verify {j1 < n - 1} ()
          in
            if up_i = up_j then
              up_i
            else
              begin
                uptr_exch<a> (pf_arr | up_i, up_j);
                outer_loop (pf_arr | up_i, up_j)
              end
          end
      end

    val up_final = outer_loop (pf_arr | uptr_pred<a> up_arr, up_end)
    val i_final = uptr_difference<a> (pf_arr | up_final, up_arr)

    (* Move the pivot into its final position. *)
    val () =
      if i_final <> pred n then
        uptr_exch<a> (pf_arr | up_final, up_end)
  in
    i_final
  end
