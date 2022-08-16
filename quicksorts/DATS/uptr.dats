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

implement {a}
ptr2uptr {p} p =
  let
    extern fn
    ptr2uptr__ :
      {a : vt@ype}
      {p : addr}
      ptr p -<> uptr (a, p, 0) = "mac#%"
  in
    ptr2uptr__ {a} {p} p
  end

implement {a}
uptr2ptr {p} {i} up =
  let
    extern fn
    uptr2ptr__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      uptr (a, p, i) -<> ptr (p + (i * sizeof a)) = "mac#%"
  in
    uptr2ptr__ {a} {p} {i} up
  end

implement {a}
uptr_anchor2ptr {p} up =
  uptr2ptr {p} {0} up

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
uptr_get {p} {i} (pf_view | up) =
  ptr_get<a> (pf_view | uptr2ptr {p} {i} up)

implement {a}
uptr_set {p} {i} (pf_view | up, x) =
  ptr_set<a> (pf_view | uptr2ptr {p} {i} up, x)

implement {a}
uptr_exch {p} {i} (pf_view | up, x) =
  ptr_exch<a> (pf_view | uptr2ptr {p} {i} up, x)
