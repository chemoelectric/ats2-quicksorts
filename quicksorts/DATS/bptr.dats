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

#define ATS_PACKNAME "ats2-quicksorts-bptr"
#define ATS_EXTERN_PREFIX "ats2_quicksorts_bptr_"

#include "share/atspre_staload.hats"
staload "quicksorts/SATS/bptr.sats"
staload UN = "prelude/SATS/unsafe.sats"

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

implement {a}
ptr2bptr_anchor {p} p =
  let
    extern fn
    ptr2bptr_anchor__ :
      {a : vt@ype}
      {p : addr}
      ptr p -<> bptr (a, p, 0) = "mac#%"
  in
    ptr2bptr_anchor__ {a} {p} p
  end

implement {a}
bptr2ptr {p} {i} bp =
  let
    extern fn
    bptr2ptr__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      (bptr (a, p, i)) -<>
        ptr (p + (i * sizeof a)) = "mac#%"
  in
    bptr2ptr__ {a} {p} {i} bp
  end

implement {a} {tk}
bptr_add_g1uint {p} {i} {j} (bp, j) =
  let
    extern fn
    bptr_add_size__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (bptr (a, p, i), size_t j, size_t (sizeof a)) -<>
        bptr (a, p, i + j) = "mac#%"
  in
    bptr_add_size__ {a} {p} {i} {j} (bp, g1u2u j, sizeof<a>)
  end

implement {a} {tk}
bptr_add_g1int {p} {i} {j} (bp, j) =
  let
    extern fn
    bptr_add_ssize__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (bptr (a, p, i), ssize_t j, size_t (sizeof a)) -<>
        bptr (a, p, i + j) = "mac#%"
  in
    bptr_add_ssize__ {a} {p} {i} {j} (bp, g1i2i j, sizeof<a>)
  end

implement {a} {tk}
bptr_sub_g1uint {p} {i} {j} (bp, j) =
  let
    extern fn
    bptr_sub_size__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (bptr (a, p, i), size_t j, size_t (sizeof a)) -<>
        bptr (a, p, i - j) = "mac#%"
  in
    bptr_sub_size__ {a} {p} {i} {j} (bp, g1u2u j, sizeof<a>)
  end

implement {a} {tk}
bptr_sub_g1int {p} {i} {j} (bp, j) =
  let
    extern fn
    bptr_ssize_sub__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (bptr (a, p, i), ssize_t j, size_t (sizeof a)) -<>
        bptr (a, p, i - j) = "mac#%"
  in
    bptr_ssize_sub__ {a} {p} {i} {j} (bp, g1i2i j, sizeof<a>)
  end

implement {a}
bptr_succ {p} {i} bp =
  let
    extern fn
    bptr_succ__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      (bptr (a, p, i), size_t (sizeof a)) -<>
        bptr (a, p, i + 1) = "mac#%"
  in
    bptr_succ__ {a} {p} {i} (bp, sizeof<a>)
  end

implement {a}
bptr_pred {p} {i} bp =
  let
    extern fn
    bptr_pred__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      (bptr (a, p, i), size_t (sizeof a)) -<>
        bptr (a, p, i - 1) = "mac#%"
  in
    bptr_pred__ {a} {p} {i} (bp, sizeof<a>)
  end

implement {a}
bptr_diff {p} {i, j} (bp_i, bp_j) =
  let
    extern fn
    bptr_diff__ :
      {a    : vt@ype}
      {p    : addr}
      {i, j : int}
      (bptr (a, p, i), bptr (a, p, j), size_t (sizeof a)) -<>
        ssize_t (i - j) = "mac#%"
  in
    bptr_diff__ {a} {p} {i, j} (bp_i, bp_j, sizeof<a>)
  end

implement {a}
bptr_diff_unsigned {p} {i, j} (bp_i, bp_j) =
  let
    extern fn
    bptr_diff_unsigned__ :
      {a    : vt@ype}
      {p    : addr}
      {i, j : int}
      (bptr (a, p, i), bptr (a, p, j), size_t (sizeof a)) -<>
        size_t (i - j) = "mac#%"
  in
    bptr_diff_unsigned__ {a} {p} {i, j} (bp_i, bp_j, sizeof<a>)
  end

implement {a}
bptr_get (pf_view | bp) =
  ptr_get<a> (pf_view | bptr2ptr bp)

implement {a}
bptr_set (pf_view | bp, x) =
  ptr_set<a> (pf_view | bptr2ptr bp, x)

implement {a}
bptr_exch (pf_view | bp, x) =
  ptr_exch<a> (pf_view | bptr2ptr bp, x)

implement {a}
interchange_bptr_bptr {p} {n} {i, j} (pf_arr | bp_i, bp_j) =
  if bp_i <> bp_j then
    let
      fn {}
      exch (pf_i   : !a @ (p + (i * sizeof a)),
            pf_j   : !a @ (p + (j * sizeof a)) |
            bp_i   : bptr (a, p, i),
            p_j    : ptr (p + (j * sizeof a)))
          :<!wrt> void =
        bptr_exch<a> (pf_i | bp_i, !p_j)

      prval @(pf_i, pf_j, fpf) =
        array_v_takeout2 {a} {p} {n} {i, j} pf_arr
      val p_j = bptr2ptr bp_j
      val () = exch (pf_i, pf_j | bp_i, p_j)
      prval () = pf_arr := fpf (pf_i, pf_j)
    in
    end

implement {a}
subreverse_bptr_bptr {p} {n} {i, j} (pf_arr | bp_i, bp_j) =
  let
    fun
    loop {i, j : int | 0 <= i; i <= j; j <= n}
         .<j - i>.
         (pf_arr : !array_v (a, p, n) |
          bp_i   : bptr (a, p, i),
          bp_j   : bptr (a, p, j))
        :<!wrt> void =
      let
        val bp_i1 = bptr_succ<a> bp_i
      in
        if bp_i1 < bp_j then
          let
            val bp_j1 = bptr_pred<a> bp_j
          in
            interchange_bptr_bptr<a> (pf_arr | bp_i, bp_j1);
            loop (pf_arr | bp_i1, bp_j1)
          end
      end
  in
    loop (pf_arr | bp_i, bp_j)
  end

implement {a}
subcirculate_right_bptr_bptr {p} {n} {i, j}
                             (pf_arr | bp_i, bp_j) =
  if bp_i <> bp_j then
    let
      extern fn                 (* Unsafe memmove. *)
      memmove : (Ptr, Ptr, Size_t) -< !wrt > void = "mac#%"

      prval @(pf_i, pf_j, fpf) =
        array_v_takeout2 {a} {p} {n} {i, j} pf_arr

      val tmp = bptr_get<a> (pf_j | bp_j)

      prval () = lemma_sizeof {a} ()
      prval () = mul_gte_gte_gte {j - i, sizeof a} ()
      val () =
        memmove (bptr2ptr (bptr_succ<a> bp_i),
                 bptr2ptr bp_i,
                 bptr_diff_unsigned<a> (bp_j, bp_i) * sizeof<a>)

      prval () = $UN.castview2void_at{a?}{a} pf_i
      val () = bptr_set<a> (pf_i | bp_i, tmp)

      prval () = $UN.castview2void_at{a}{a?!} pf_j
      prval () = pf_arr := fpf (pf_i, pf_j)
    in
    end
