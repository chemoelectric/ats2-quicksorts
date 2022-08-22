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

#define ATS_PACKNAME "ats2-quicksorts"
#define ATS_EXTERN_PREFIX "ats2_quicksorts_"

%{#
#include <quicksorts/CATS/quicksorts.cats>
#include <quicksorts/CATS/bptr.cats>
%}

(*------------------------------------------------------------------*)
(* A stable array quicksort.                                        *)

fn {a : vt@ype}
array_stable_quicksort_given_workspace :
  {n  : int}
  {m1 : int | n <= m1}
  {m2 : int | n - 1 <= m2}
  (&array (a, m1),
   size_t n,
   &array (a?, m2)) -< !wrt >
    void

fn {a : vt@ype}
array_stable_quicksort_not_given_workspace :
  {n  : int}
  {m1 : int | n <= m1}
  (&array (a, m1),
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
  (&a, &a) -<> bool
fn {a : vt@ype}
array_stable_quicksort$cmp :
  (&a, &a) -<> int

(*------------------------------------------------------------------*)
(* Customization of the sorting of ‘small’ subarrays.               *)
(*                                                                  *)
(* (Any method used has to be stable, of course.)                   *)
(*                                                                  *)

typedef array_stable_quicksort_small_sort_t (a : vt@ype) =
  {n : nat}
  (&array (a, n), size_t n) -< !wrt > void

(* What ‘small’ sort should we use? *)
fn {a : vt@ype}
array_stable_quicksort$small_sort :
  array_stable_quicksort_small_sort_t a

(* When should we switch over to a ‘small’ sort? *)
fn {a : vt@ype}
array_stable_quicksort$small :
  () -<> [n : pos] size_t n

(* Some ‘small’ sort choices: *)

fn {a : vt@ype}   (* Some method, chosen for its supposed goodness. *)
array_stable_quicksort_small_sort_default :
  array_stable_quicksort_small_sort_t a

fn {a : vt@ype}                 (* A stable binary insertion sort. *)
array_stable_quicksort_small_sort_insertion :
  array_stable_quicksort_small_sort_t a

(*------------------------------------------------------------------*)
(* Customization of pivoting.                                       *)

typedef array_stable_quicksort_pivot_index_t (a : vt@ype) =
  {n : pos}
  (&array (a, n), size_t n) -<>
    [i : int | 0 <= i; i < n]
    size_t i

fn {a : vt@ype}
array_stable_quicksort$pivot_index :
  array_stable_quicksort_pivot_index_t a

(* Some pivot strategies: *)

fn {a : vt@ype}   (* Some method, chosen for its supposed goodness. *)
array_stable_quicksort_pivot_index_default :
  array_stable_quicksort_pivot_index_t a

fn {a : vt@ype}                 (* A randomly chosen element. *)
array_stable_quicksort_pivot_index_random :
  array_stable_quicksort_pivot_index_t a

fn {a : vt@ype}    (* The median of three randomly chosen elements. *)
array_stable_quicksort_pivot_index_median_of_three_random :
  array_stable_quicksort_pivot_index_t a

(*------------------------------------------------------------------*)
