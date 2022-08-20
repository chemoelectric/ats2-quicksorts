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

staload "quicksorts/SATS/bptr.sats"
staload _ = "quicksorts/DATS/bptr.dats"
staload UN = "prelude/SATS/unsafe.sats"

(*------------------------------------------------------------------*)

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

extern prfn
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

primplement
array_v_takeout2 {a} {p} {n} {i, j} pf_arr =
  sif i < j then
    let
      prval @(pf1, pf1a) = array_v_split {a} {p} {n} {i} pf_arr
      prval @(pf2, pf3) =
        array_v_split {a} {p + (i * sizeof a)} {n - i} {j - i} pf1a
      prval @(pf_i, pf2a) =
        array_v_uncons {a} {p + (i * sizeof a)} {j - i} pf2
      prval @(pf_j, pf3a) =
        array_v_uncons {a} {p + (j * sizeof a)} {n - j} pf3
    in
      @(pf_i, pf_j,
        lam (pf_i, pf_j) =<lin,prf>
          let
            prval pf3 =
              array_v_cons
                {a} {p + (j * sizeof a)} {n - j - 1} (pf_j, pf3a)
            prval pf2 =
              array_v_cons
                {a} {p + (i * sizeof a)} {j - i - 1} (pf_i, pf2a)
            prval pf1a =
              array_v_unsplit {a} {p + (i * sizeof a)} {j - i, n - j}
                              (pf2, pf3)
            prval pf_arr =
              array_v_unsplit {a} {p} {i, n - i} (pf1, pf1a)
          in
            pf_arr
          end)
    end
  else
    let
      prval @(pf_j, pf_i, fpf_ji) =
        array_v_takeout2 {a} {p} {n} {j, i} pf_arr
    in
      @(pf_i, pf_j,
        lam (pf_i, pf_j) =<lin,prf> fpf_ji (pf_j, pf_i))
    end

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

extern fn
copy_bytes :
  {n : int}
  (ptr, ptr, size_t n) -< !wrt > void = "mac#%"

fn {a : vt@ype}
my_array_copy
          {n : int}
          (dst : &array (a?, n) >> array (a, n),
           src : &array (a, n) >> array (a?!, n),
           n: size_t n)
    :<!wrt> void =
  let
    val () = copy_bytes (addr@ dst, addr@ src, n * sizeof<a>)
    prval () = $UN.castview2void_at{array (a, n)} (view@ dst)
    prval () = $UN.castview2void_at{array (a?!, n)} (view@ src)
  in
  end

(*------------------------------------------------------------------*)
(* A simple linear congruential generator.                          *)

extern fn
random_uint64 () :<!wrt> uint64 = "mac#%"

fn {tk : tkind}
g1uint_randint
          {n : pos}
          (n : g1uint (tk, n))
    :<> [i : nat | i <= n - 1] g1uint (tk, i) =
  let
    val u64_n = $UN.cast{uint64 n} n
    val u64_rand : [i : nat] uint64 i =
      g1ofg0 ($effmask_wrt random_uint64 ())
    val u64_result = g1uint_mod (u64_rand, u64_n)
  in
    $UN.cast u64_result
  end

overload randint with g1uint_randint

(*------------------------------------------------------------------*)
(* A stack for non-recursive implementation of quicksort.           *)

typedef stk_entry_t (p : addr, n : int) =
  [p == null || 0 < n] @(ptr p, size_t n)
typedef stk_entry_t (n : int) =
  [p : addr] stk_entry_t (p, n)
typedef stk_entry_t =
  [n : int] stk_entry_t n

vtypedef stk_vt (p        : addr,
                 depth    : int,
                 size_sum : int) =
  @{
    pf       = array_v (stk_entry_t, p, STK_MAX) |
    p        = ptr p,
    depth    = int depth,
    size_sum = size_t size_sum
  }

fn {}
stk_vt_make
          {p  : addr}
          (pf : array_v (stk_entry_t, p, STK_MAX) |
           p  : ptr p)
    :<> stk_vt (p, 0, 0) =
  @{
    pf = pf |
    p = p,
    depth = 0,
    size_sum = i2sz 0
  }

fn {a : vt@ype}
stk_vt_push
          {p_stk    : addr}
          {depth    : nat | depth < STK_MAX}
          {size_sum : nat}
          {p_entry  : addr}
          {size     : pos}
          (pf_entry : !array_v (a, p_entry, size) |
           p_entry  : ptr p_entry,
           size     : size_t size,
           stk      : &stk_vt (p_stk, depth, size_sum)
                      >> stk_vt (p_stk, depth + 1, size_sum + size))
    :<!wrt> void =
  let
    macdef storage = !(stk.p)
  in
    stk.depth := succ (stk.depth);
    storage[STK_MAX - stk.depth] := @(p_entry, size);
    stk.size_sum := stk.size_sum + size
  end

fn {a : vt@ype}
stk_vt_pop
          {p_stk    : addr}
          {depth    : pos}
          {size_sum : pos}
          {p_entry  : addr}
          (stk      : &stk_vt (p_stk, depth, size_sum)
                      >> stk_vt (p_stk, depth - 1, size_sum - size))
    :<!wrt> #[size : pos | size <= size_sum]
            @(P2tr1 (array (a, size)),
              size_t size) =
  let
    macdef storage = !(stk.p)
    val @(p_arr1, size) = storage[STK_MAX - stk.depth]
    val () = stk.depth := pred (stk.depth)
    val size_sum = stk.size_sum
    val () = $effmask_exn assertloc (size <= size_sum)
    val () = stk.size_sum := size_sum - size
    prval [size : int] EQINT () = eqint_make_guint size
    val () = $effmask_exn assertloc (ptr_isnot_null p_arr1)
  in
    @($UN.ptr2p2tr {array (a, size)} p_arr1,
      size)
  end

(*------------------------------------------------------------------*)
(* Some pivot strategies.                                           *)

typedef quicksorts_pivot_index_t (a : vt@ype) =
  {n : pos}
  (&array (a, n), size_t n) -<>
    [i : int | 0 <= i; i < n]
    size_t i

extern fn {a : vt@ype}
quicksorts$array_element_lt
          {n    : int}
          {i, j : nat | i < n; j < n; i != j}
          (arr  : &array (a, n),
           i    : size_t i,
           j    : size_t j)
    :<> bool

extern fn {a : vt@ype}
quicksorts_pivot_index_random :
  quicksorts_pivot_index_t a

extern fn {a : vt@ype}
quicksorts_pivot_index_middle :
  quicksorts_pivot_index_t a

extern fn {a : vt@ype}
quicksorts_pivot_index_median_of_three :
  quicksorts_pivot_index_t a

implement {a}
quicksorts_pivot_index_random {n} (arr, n) =
  randint n

implement {a}
quicksorts_pivot_index_middle (arr, n) =
  half n

implement {a}
quicksorts_pivot_index_median_of_three {n} (arr, n) =
  if n <= 2 then
    i2sz 0
  else
    let
      macdef lt = quicksorts$array_element_lt<a>

      val i_first = i2sz 0
      and i_middle = half n
      and i_last = pred n

      val middle_lt_first =
        lt {n} (arr, i_middle, i_first)
      and last_lt_first =
        lt {n} (arr, i_last, i_first)
    in
      if middle_lt_first <> last_lt_first then
        i_first
      else
        let
          val middle_lt_last =
            lt {n} (arr, i_middle, i_last)
        in
          if middle_lt_first <> middle_lt_last then
            i_middle
          else
            i_last
        end
    end

(*------------------------------------------------------------------*)
(* Shared code for binary insertion sorting.                        *)

extern fn {a : vt@ype}
insertion_sort$lt :
  {p_arr  : addr}
  {n      : int}
  {i, j   : nat | i <= n - 1; j <= n - 1; i != j}
  (!array_v (a, p_arr, n) |
   bptr (a, p_arr, i),
   bptr (a, p_arr, j)) -<>
    bool

extern fn {a : vt@ype}
insertion_sort$gt_or_gte :
  {p_arr  : addr}
  {n      : int}
  {i, j   : nat | i <= n - 1; j <= n - 1; i != j}
  (!array_v (a, p_arr, n) |
   bptr (a, p_arr, i),
   bptr (a, p_arr, j)) -<>
    bool

fn {a : vt@ype}
make_an_ordered_prefix
          {p_arr  : addr}
          {n      : int | 2 <= n}
          (pf_arr : !array_v (a, p_arr, n) |
           bp_arr : bptr_anchor (a, p_arr),
           bp_n   : bptr (a, p_arr, n))
    :<!wrt> [pfx_len : int | 2 <= pfx_len; pfx_len <= n]
            bptr (a, p_arr, pfx_len) =
  if ~insertion_sort$lt<a>
       (pf_arr | bptr_succ<a> bp_arr, bp_arr) then
    let                       (* Non-decreasing order. *)
      fun
      loop {pfx_len : int | 2 <= pfx_len; pfx_len <= n}
           .<n - pfx_len>.
           (pf_arr  : !array_v (a, p_arr, n) |
            bp      : bptr (a, p_arr, pfx_len))
          :<> [pfx_len : int | 2 <= pfx_len; pfx_len <= n]
              bptr (a, p_arr, pfx_len) =
        if bp = bp_n then
          bp
        else if insertion_sort$lt<a>
                  (pf_arr | bp, bptr_pred<a> bp) then
          bp
        else
          loop (pf_arr | bptr_succ<a> bp)
    in
      loop (pf_arr | bptr_add<a> (bp_arr, 2))
    end
  else
    let (* Either non-increasing or monotonically decreasing order. *)
      fun
      loop {pfx_len : int | 2 <= pfx_len; pfx_len <= n}
           .<n - pfx_len>.
           (pf_arr  : !array_v (a, p_arr, n) |
            bp      : bptr (a, p_arr, pfx_len))
          :<> [pfx_len : int | 2 <= pfx_len; pfx_len <= n]
              bptr (a, p_arr, pfx_len) =
        if bp = bp_n then
          bp
        else if insertion_sort$gt_or_gte<a>
                  (pf_arr | bp, bptr_pred<a> bp) then
          bp
        else
          loop (pf_arr | bptr_succ<a> bp)

      val bp = loop (pf_arr | bptr_add<a> (bp_arr, 2))
    in
      subreverse<a> (pf_arr | bp_arr, bp);
      bp
    end

fn {a : vt@ype}
insertion_position
          {p_arr  : addr}
          {n      : int}
          {i      : pos | i < n}
          (pf_arr : !array_v (a, p_arr, n) |
           bp_arr : bptr_anchor (a, p_arr),
           bp_i   : bptr (a, p_arr, i))
    :<> [j : nat | j <= i]
        bptr (a, p_arr, j) =
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
          bp_j   : bptr (a, p_arr, j),
          bp_k   : bptr (a, p_arr, k))
        :<> [j1 : nat | j1 <= i]
            bptr (a, p_arr, j1) =
      if bp_j <> bp_k then
        let
          (* Find the point that is halfway between bp_j and bp_k,
             rounding towards bp_k. *)
          stadef h = k - ((k - j) / 2)
          val bp_h : bptr (a, p_arr, h) =
            bptr_sub<a>
              (bp_k, half (bptr_diff_unsigned<a> (bp_k, bp_j)))
        in
          if insertion_sort$lt<a> (pf_arr | bp_i, bp_h) then
            loop (pf_arr | bp_j, bptr_pred<a> bp_h)
          else
            loop (pf_arr | bp_h, bp_k)
        end
      else if bp_j <> bp_arr then
        bptr_succ<a> bp_j
      else if insertion_sort$lt<a> (pf_arr | bp_i, bp_arr) then
        bp_arr
      else
        bptr_succ<a> bp_arr
  in
    loop (pf_arr | bp_arr, bptr_pred<a> bp_i)
  end

fn {a : vt@ype}
insertion_sort
          {n   : nat}
          (arr : &array (a, n),
           n   : size_t n)
    :<!wrt> void =
  if i2sz 2 <= n then
    let
      prval pf_arr = view@ arr
      val p_arr = addr@ arr
      prval [p_arr : addr] EQADDR () = eqaddr_make_ptr p_arr
      val bp_arr = ptr2bptr_anchor p_arr
      val bp_n = bptr_add<a> (bp_arr, n)
      val bp_i = make_an_ordered_prefix<a> (pf_arr | bp_arr, bp_n)

      fun
      loop {i : pos | i <= n}
           .<n - i>.
           (pf_arr : !array_v (a, p_arr, n) >> _ |
            bp_i   : bptr (a, p_arr, i))
          :<!wrt> void =
        if bp_i <> bp_n then
          let
            val bp_j = insertion_position<a> (pf_arr | bp_arr, bp_i)
          in
            subcirculate_right<a> (pf_arr | bp_j, bp_i);
            loop (pf_arr | bptr_succ<a> bp_i)
          end

      val () = loop (pf_arr | bp_i)

      prval () = view@ arr := pf_arr
    in
    end

(*------------------------------------------------------------------*)
