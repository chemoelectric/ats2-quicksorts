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

#define ATS_PACKNAME "ats2-quicksorts-uptr"
#define ATS_EXTERN_PREFIX "ats2_quicksorts_uptr_"

%{#
#include <quicksorts/CATS/uptr.cats>
%}

(*------------------------------------------------------------------*)

stacst addr2uint : addr -> int

typedef uptr (a : vt@ype+,
              p : addr,
              i : int) =
  uintptr (addr2uint p + (i * sizeof a))

fn {a : vt@ype}
ptr2uptr :
  {p : addr}
  ptr p -<> uptr (a, p, 0)

fn {a : vt@ype}
uptr2ptr :
  {p : addr}
  {i : int}
  uptr (a, p, i) -<> ptr (p + (i * sizeof a))

(*------------------------------------------------------------------*)

fn {a  : vt@ype}
   {tk : tkind}
g1uint_uptr_add :
  {p : addr}
  {i : int}
  {j : int}
  (uptr (a, p, i), g1uint (tk, j)) -<> uptr (a, p, i + j)

fn {a  : vt@ype}
   {tk : tkind}
g1int_uptr_add :
  {p : addr}
  {i : int}
  {j : int}
  (uptr (a, p, i), g1int (tk, j)) -<> uptr (a, p, i + j)

overload uptr_add with g1uint_uptr_add
overload uptr_add with g1int_uptr_add

(*------------------------------------------------------------------*)

fn {a  : vt@ype}
   {tk : tkind}
g1uint_uptr_sub :
  {p : addr}
  {i : int}
  {j : int}
  (uptr (a, p, i), g1uint (tk, j)) -<> uptr (a, p, i - j)

fn {a  : vt@ype}
   {tk : tkind}
g1int_uptr_sub :
  {p : addr}
  {i : int}
  {j : int}
  (uptr (a, p, i), g1int (tk, j)) -<> uptr (a, p, i - j)

overload uptr_sub with g1uint_uptr_sub
overload uptr_sub with g1int_uptr_sub

(*------------------------------------------------------------------*)

fn {a  : vt@ype}
uptr_succ :
  {p : addr}
  {i : int}
  uptr (a, p, i) -<> uptr (a, p, i + 1)

fn {a  : vt@ype}
uptr_pred :
  {p : addr}
  {i : int}
  uptr (a, p, i) -<> uptr (a, p, i - 1)

(*------------------------------------------------------------------*)
