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

%{#
#include <stable-quicksort/CATS/stable-quicksort.cats>
%}

(*------------------------------------------------------------------*)
(* array quicksort                                                  *)

fn {a : vt@ype}
array_stable_quicksort_given_workspace :
  {n : int}
  (&array (INV(a), n),
   size_t n,
   &array (a?, n)) -< !wrt >
    void

fn {a : vt@ype}
array_stable_quicksort_not_given_workspace :
  {n : int}
  (&array (INV(a), n),
   size_t n) -< !wrt >
    void

overload array_stable_quicksort with
  array_stable_quicksort_given_workspace
overload array_stable_quicksort with
  array_stable_quicksort_not_given_workspace

(* Implement either array_stable_quicksort$lt or
   array_stable_quicksort$cmp. The former takes
   precedence. The latter defaults to ‘gcompare_ref_ref<a>’. *)
fn {a : vt@ype}
array_stable_quicksort$lt :
  (&RD(a), &RD(a)) -<> bool
fn {a : vt@ype}
array_stable_quicksort$cmp :
  (&RD(a), &RD(a)) -<> int

(* When should we switch over to insertion sort? *)
fn {a : vt@ype}
array_stable_quicksort$small :
  () -<> [n : pos] size_t n

typedef array_stable_quicksort_pivot_index_t (a : vt@ype) =
  {n : pos}
  (&array (a, n), size_t n) -<>
    [i : int | 0 <= i; i < n]
    size_t i
fn {a : vt@ype}
array_stable_quicksort$pivot_index :
  array_stable_quicksort_pivot_index_t a

(* Some pivot strategies. *)
fn {a : vt@ype}   (* Some method, chosen for its supposed goodness. *)
array_stable_quicksort_pivot_index_default :
  array_stable_quicksort_pivot_index_t a
fn {a : vt@ype}              (* This seems to work well in general. *)
array_stable_quicksort_pivot_index_random :
  array_stable_quicksort_pivot_index_t a
fn {a : vt@ype}     (* Currently this works poorly on large arrays. *)
array_stable_quicksort_pivot_index_middle :
  array_stable_quicksort_pivot_index_t a
fn {a : vt@ype}     (* Currently this works poorly on large arrays. *)
array_stable_quicksort_pivot_index_median_of_three :
  array_stable_quicksort_pivot_index_t a

(*------------------------------------------------------------------*)
