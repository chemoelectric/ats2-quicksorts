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
staload "quicksorts/SATS/uptr.sats"
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
ptr2uptr_anchor {p} p =
  let
    extern fn
    ptr2uptr_anchor__ :
      {a : vt@ype}
      {p : addr}
      ptr p -<> uptr (a, p, 0) = "mac#%"
  in
    ptr2uptr_anchor__ {a} {p} p
  end

implement {a}
uptr2ptr {p} {i} (anchor, up) =
  let
    extern fn
    uptr2ptr__ :
      {p : addr}
      {i : int}
      (uptr_anchor (a, p), uptr (a, p, i)) -<>
        ptr (p + (i * sizeof a)) = "mac#%"
  in
    uptr2ptr__ {p} {i} (anchor, up)
  end

implement {a} {tk}
uptr_add_g1uint {p} {i} {j} (up, j) =
  let
    extern fn
    uptr_add_size__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (uptr (a, p, i), size_t j, size_t (sizeof a)) -<>
        uptr (a, p, i + j) = "mac#%"
  in
    uptr_add_size__ {a} {p} {i} {j} (up, g1u2u j, sizeof<a>)
  end

implement {a} {tk}
uptr_add_g1int {p} {i} {j} (up, j) =
  let
    extern fn
    uptr_add_ssize__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (uptr (a, p, i), ssize_t j, size_t (sizeof a)) -<>
        uptr (a, p, i + j) = "mac#%"
  in
    uptr_add_ssize__ {a} {p} {i} {j} (up, g1i2i j, sizeof<a>)
  end

implement {a} {tk}
uptr_sub_g1uint {p} {i} {j} (up, j) =
  let
    extern fn
    uptr_sub_size__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (uptr (a, p, i), size_t j, size_t (sizeof a)) -<>
        uptr (a, p, i - j) = "mac#%"
  in
    uptr_sub_size__ {a} {p} {i} {j} (up, g1u2u j, sizeof<a>)
  end

implement {a} {tk}
uptr_sub_g1int {p} {i} {j} (up, j) =
  let
    extern fn
    uptr_ssize_sub__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (uptr (a, p, i), ssize_t j, size_t (sizeof a)) -<>
        uptr (a, p, i - j) = "mac#%"
  in
    uptr_ssize_sub__ {a} {p} {i} {j} (up, g1i2i j, sizeof<a>)
  end

implement {a}
uptr_succ {p} {i} up =
  let
    extern fn
    uptr_succ__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      (uptr (a, p, i), size_t (sizeof a)) -<>
        uptr (a, p, i + 1) = "mac#%"
  in
    uptr_succ__ {a} {p} {i} (up, sizeof<a>)
  end

implement {a}
uptr_pred {p} {i} up =
  let
    extern fn
    uptr_pred__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      (uptr (a, p, i), size_t (sizeof a)) -<>
        uptr (a, p, i - 1) = "mac#%"
  in
    uptr_pred__ {a} {p} {i} (up, sizeof<a>)
  end

implement {a}
uptr_diff {p} {i, j} (up_i, up_j) =
  let
    extern fn
    uptr_diff__ :
      {a    : vt@ype}
      {p    : addr}
      {i, j : int}
      (uptr (a, p, i), uptr (a, p, j), size_t (sizeof a)) -<>
        ssize_t (i - j) = "mac#%"
  in
    uptr_diff__ {a} {p} {i, j} (up_i, up_j, sizeof<a>)
  end

implement {a}
uptr_diff_unsigned {p} {i, j} (up_i, up_j) =
  let
    extern fn
    uptr_diff_unsigned__ :
      {a    : vt@ype}
      {p    : addr}
      {i, j : int}
      (uptr (a, p, i), uptr (a, p, j), size_t (sizeof a)) -<>
        size_t (i - j) = "mac#%"
  in
    uptr_diff_unsigned__ {a} {p} {i, j} (up_i, up_j, sizeof<a>)
  end

implement {a}
uptr_get (pf_view | anchor, up) =
  ptr_get<a> (pf_view | uptr2ptr (anchor, up))

implement {a}
uptr_set (pf_view | anchor, up, x) =
  ptr_set<a> (pf_view | uptr2ptr (anchor, up), x)

implement {a}
uptr_exch (pf_view | anchor, up, x) =
  ptr_exch<a> (pf_view | uptr2ptr (anchor, up), x)

implement {a}
uptr_interchange {p} {n} {i, j} (pf_arr | anchor, up_i, up_j) =
  if up_i <> up_j then
    let
      fn {}
      exch (pf_i   : !a @ (p + (i * sizeof a)),
            pf_j   : !a @ (p + (j * sizeof a)) |
            anchor : uptr_anchor (a, p),
            up_i   : uptr (a, p, i),
            p_j    : ptr (p + (j * sizeof a)))
          :<!wrt> void =
        uptr_exch<a> (pf_i | anchor, up_i, !p_j)

      prval @(pf_i, pf_j, fpf) =
        array_v_takeout2 {a} {p} {n} {i, j} pf_arr
      val p_j = uptr2ptr (anchor, up_j)
      val () = exch (pf_i, pf_j | anchor, up_i, p_j)
      prval () = pf_arr := fpf (pf_i, pf_j)
    in
    end
