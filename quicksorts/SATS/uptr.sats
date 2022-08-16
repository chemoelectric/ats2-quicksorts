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
uptr_add_g1uint :
  {p : addr}
  {i : int}
  {j : int}
  (uptr (a, p, i), g1uint (tk, j)) -<> uptr (a, p, i + j)

fn {a  : vt@ype}
   {tk : tkind}
uptr_add_g1int :
  {p : addr}
  {i : int}
  {j : int}
  (uptr (a, p, i), g1int (tk, j)) -<> uptr (a, p, i + j)

overload uptr_add with uptr_add_g1uint
overload uptr_add with uptr_add_g1int

(*------------------------------------------------------------------*)

fn {a  : vt@ype}
   {tk : tkind}
uptr_sub_g1uint :
  {p : addr}
  {i : int}
  {j : int}
  (uptr (a, p, i), g1uint (tk, j)) -<> uptr (a, p, i - j)

fn {a  : vt@ype}
   {tk : tkind}
uptr_sub_g1int :
  {p : addr}
  {i : int}
  {j : int}
  (uptr (a, p, i), g1int (tk, j)) -<> uptr (a, p, i - j)

overload uptr_sub with uptr_sub_g1uint
overload uptr_sub with uptr_sub_g1int

(*------------------------------------------------------------------*)

fn {a : vt@ype}
uptr_succ :
  {p : addr}
  {i : int}
  uptr (a, p, i) -<> uptr (a, p, i + 1)

fn {a : vt@ype}
uptr_pred :
  {p : addr}
  {i : int}
  uptr (a, p, i) -<> uptr (a, p, i - 1)

(*------------------------------------------------------------------*)

fn {a : vt@ype}
uptr_get :
  {p : addr}
  {i : int}
  (!a @ (p + (i * sizeof a)) >> a?! @ (p + (i * sizeof a)) |
   uptr (a, p, i)) -<>
    a

fn {a : vt@ype}
uptr_set :
  {p : addr}
  {i : int}
  (!a? @ (p + (i * sizeof a)) >> a @ (p + (i * sizeof a)) |
   uptr (a, p, i), a) -< !wrt >
    void

fn {a : vt@ype}
uptr_exch :
  {p : addr}
  {i : int}
  (!a @ (p + (i * sizeof a)) | uptr (a, p, i), &a >> a) -< !wrt >
    void

(*------------------------------------------------------------------*)
