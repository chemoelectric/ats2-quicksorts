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
(* List quicksort                                                   *)

(* FIXME: WRITE A NEW LIST QUICKSORT THAT USES THE PARTITION STRATEGY
          ALREADY USED IN THE ARRAY QUICKSORT. This will allow the use
          of a $lt function as in the array quicksort. It should also
          be more efficient in the absence of a great many equal
          keys. *)

fn {a : vt@ype}
list_vt_stable_quicksort :
  {n : int}
  list_vt (INV(a), n) -< !wrt >
    list_vt (a, n)

fn {a : vt@ype}
list_vt_stable_quicksort$cmp :
  (&RD(a), &RD(a)) -<>
    [i : int | ~1 <= i; i <= 1]
    int i

typedef list_vt_stable_quicksort_pivot_index_t (a : vt@ype) =
  {n : pos}
  (!list_vt (a, n), int n) -<>
    [i : int | 0 <= i; i < n]
    int i
fn {a : vt@ype}
list_vt_stable_quicksort$pivot_index :
  list_vt_stable_quicksort_pivot_index_t a

(* Some pivot strategies. *)
fn {a : vt@ype}   (* Some method, chosen for its supposed goodness. *)
list_vt_stable_quicksort_pivot_index_default :
  list_vt_stable_quicksort_pivot_index_t a
fn {a : vt@ype}
list_vt_stable_quicksort_pivot_index_random :
  list_vt_stable_quicksort_pivot_index_t a
fn {a : vt@ype}
list_vt_stable_quicksort_pivot_index_middle :
  list_vt_stable_quicksort_pivot_index_t a
fn {a : vt@ype}
list_vt_stable_quicksort_pivot_index_first :
  list_vt_stable_quicksort_pivot_index_t a

(*------------------------------------------------------------------*)
(* Array quicksort                                                  *)

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
   precedence. The latter defaults to
   ‘gcompare_ref_ref<a>’. *)
fn {a : vt@ype}
array_stable_quicksort$lt :
  (&RD(a), &RD(a)) -<> bool
fn {a : vt@ype}
array_stable_quicksort$cmp :
  (&RD(a), &RD(a)) -<> int

(* The pivot strategy has a default, but I leave the default
   unspecified. *)
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
