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
#include <quicksorts/CATS/uptr.cats>
%}

(*------------------------------------------------------------------*)
(* An unstable array quicksort.                                     *)

fn {a : vt@ype}
array_unstable_quicksort :
  {n  : int}
  {m1 : int | n <= m1}
  (&array (a, m1),
   size_t n) -< !wrt >
    void

(* Implement either array_unstable_quicksort$lt or
   array_unstable_quicksort$cmp. The former takes
   precedence. The latter defaults to ‘gcompare_ref_ref<a>’. *)
fn {a : vt@ype}
array_unstable_quicksort$lt :
  (&a, &a) -<> bool
fn {a : vt@ype}
array_unstable_quicksort$cmp :
  (&a, &a) -<> int

(*------------------------------------------------------------------*)
(* Customization of the sorting of ‘small’ subarrays.               *)

(* When should we switch over to a ‘small’ sort? *)
fn {a : vt@ype}
array_unstable_quicksort$small :
  () -<> [n : pos] size_t n

(*------------------------------------------------------------------*)
(* Customization of pivoting.                                       *)

typedef array_unstable_quicksort_pivot_index_t (a : vt@ype) =
  {n : pos}
  (&array (a, n), size_t n) -<>
    [i : int | 0 <= i; i < n]
    size_t i

fn {a : vt@ype}
array_unstable_quicksort$pivot_index :
  array_unstable_quicksort_pivot_index_t a

(* Some pivot strategies: *)

fn {a : vt@ype}   (* Some method, chosen for its supposed goodness. *)
array_unstable_quicksort_pivot_index_default :
  array_unstable_quicksort_pivot_index_t a

fn {a : vt@ype}
array_unstable_quicksort_pivot_index_random :
  array_unstable_quicksort_pivot_index_t a

fn {a : vt@ype}
array_unstable_quicksort_pivot_index_middle :
  array_unstable_quicksort_pivot_index_t a

fn {a : vt@ype}
array_unstable_quicksort_pivot_index_median_of_three :
  array_unstable_quicksort_pivot_index_t a

(*------------------------------------------------------------------*)
(* Customization of partitioning.                                   *)

typedef array_unstable_quicksort_partition_t (a : vt@ype) =
  {n : pos}
  (&array (a, n), size_t n) -< !wrt >
    [i_pivot_final : nat | i_pivot_final < n]
    size_t i_pivot_final

fn {a : vt@ype}
array_unstable_quicksort$partition :
  array_unstable_quicksort_partition_t a

(* Some partitioning strategies: *)

fn {a : vt@ype}   (* Some method, chosen for its supposed goodness. *)
array_unstable_quicksort_partition_default :
  array_unstable_quicksort_partition_t a

fn {a : vt@ype}
array_unstable_quicksort_partition_method_1 :
  array_unstable_quicksort_partition_t a

fn {a : vt@ype}
array_unstable_quicksort_partition_method_2 :
  array_unstable_quicksort_partition_t a

(*------------------------------------------------------------------*)
