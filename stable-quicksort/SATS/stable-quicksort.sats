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

#define ATS_PACKNAME "ats2-stable-quicksort"
#define ATS_EXTERN_PREFIX "ats2_stable_quicksort_"

fn {a : vt@ype}                (* ‘Less than’: the order predicate. *)
list_vt_stable_quicksort$lt :
  (&RD(a), &RD(a)) -<> bool

fn {a : vt@ype}
list_vt_stable_quicksort :
  {n : int}
  list_vt (INV(a), n) -< !wrt >
    list_vt (a, n)
