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

#define ATS_PACKNAME "ats2-stable-quicksort"
#define ATS_EXTERN_PREFIX "ats2_stable_quicksort_"

#include "share/atspre_staload.hats"
staload "stable-quicksort/SATS/stable-quicksort.sats"
staload UN = "prelude/SATS/unsafe.sats"

#define DEFAULT_ARRAY_INSERTION_SORT_THRESHOLD 32
#define ARRAY_STACK_STORAGE_THRESHOLD 256

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

extern praxi
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

extern praxi
discard_used_contents :
  {a : vt@ype}
  {p : addr}
  {n : int}
  array_v (a?!, p, n) -<prf> array_v (a?, p, n)

extern fn
g1uint_mod_uint64 :
  {x, y : int}
  (uint64 x, uint64 y) -<> uint64 (x mod y) = "mac#%"

implement
g1uint_mod<uint64_kind> (x, y) =
  g1uint_mod_uint64 (x, y)

(*------------------------------------------------------------------*)
(* A simple linear congruential generator, for pivot selection.     *)

%{
ats2_stable_quicksort_spinlock_t ats2_stable_quicksort_seed_lock;
uint64_t ats2_stable_quicksort_seed = UINT64_C (0x1234567891234567);
%}

extern fn
random_uint64 () :<!wrt> uint64 = "mac#%"

(*------------------------------------------------------------------*)

fn {a : vt@ype}
array_element_lt
          {n    : int}
          {i, j : nat | i < n; j < n; i != j}
          (arr  : &array (a, n),
           i    : size_t i,
           j    : size_t j)
    :<> bool =
  let
    prval @(pf_i, pf_j, fpf) =
      array_v_takeout2 {a} {..} {n} {i, j} (view@ arr)
    val is_lt =
      array_stable_quicksort$lt<a> (!(ptr_add<a> (addr@ arr, i)),
                                    !(ptr_add<a> (addr@ arr, j)))
    prval () = view@ arr := fpf (pf_i, pf_j)
  in
    is_lt
  end

implement {a}
array_stable_quicksort$lt (x, y) =
  array_stable_quicksort$cmp<a> (x, y) < 0

implement {a}
array_stable_quicksort$cmp (x, y) =
  (* This default is the same as for array_quicksort$cmp in the
     prelude. *)
  gcompare_ref_ref<a> (x, y)

implement {a}
array_stable_quicksort$small () =
  i2sz DEFAULT_ARRAY_INSERTION_SORT_THRESHOLD

implement {a}
array_stable_quicksort$pivot_index {n} (arr, n) =
  array_stable_quicksort_pivot_index_default<a> {n} (arr, n)

implement {a}
array_stable_quicksort_pivot_index_default {n} (arr, n) =
  (* The default is random pivot, which I _highly_ recommend. *)
  array_stable_quicksort_pivot_index_random<a> {n} (arr, n)

implement {a}
array_stable_quicksort_pivot_index_random {n} (arr, n) =
  let
    val u64_n = $UN.cast{uint64 n} n
    val u64_rand : [i : nat] uint64 i =
      g1ofg0 ($effmask_wrt random_uint64 ())
    val u64_pivot = g1uint_mod (u64_rand, u64_n)
    val i_pivot = $UN.cast{[i : nat | i < n] size_t i} u64_pivot
  in
    i_pivot
  end

implement {a}
array_stable_quicksort_pivot_index_middle (arr, n) =
  half n

implement {a}
array_stable_quicksort_pivot_index_median_of_three {n} (arr, n) =
  if n <= 2 then
    i2sz 0
  else
    let
      val i_first = i2sz 0
      and i_middle = half n
      and i_last = pred n

      val middle_lt_first =
        array_element_lt<a> {n} (arr, i_middle, i_first)
      and last_lt_first =
        array_element_lt<a> {n} (arr, i_last, i_first)
    in
      if middle_lt_first <> last_lt_first then
        i_first
      else
        let
          val middle_lt_last =
            array_element_lt<a> {n} (arr, i_middle, i_last)
        in
          if middle_lt_first <> middle_lt_last then
            i_middle
          else
            i_last
        end
    end

fn {a : vt@ype}
insertion_position
          {n      : int}
          {i      : pos | i < n}
          {p_arr  : addr}
          (pf_arr : !array_v (a, p_arr, n) >> _ |
           p_arr  : ptr p_arr,
           i      : size_t i)
    :<> [j : nat | j <= i]
        size_t j =
  let
    fun
    loop {k1 : nat | k1 <= i}
         .<k1>.
         (pf_arr : !array_v (a, p_arr, n) >> _ |
          k1     : size_t k1)
        :<> [j : nat | j <= i]
            size_t j =
      if k1 = i2sz 0 then
        k1
      else
        let
          val k = pred k1
        in
          if array_element_lt<a> {n} (!p_arr, i, k) then
            loop (pf_arr | k)
          else
            k1
        end
  in
    loop (pf_arr | i)
  end

fn {a : vt@ype}
array_insertion_sort
          {n       : nat}
          {p_arr   : addr}
          (pf_arr  : !array_v (a, p_arr, n) >> _ |
           p_arr   : ptr p_arr,
           n       : size_t n)
    :<!wrt> void =
  if n > 1 then
    let
      fun
      loop {i : pos | i <= n}
           .<n - i>.
           (pf_arr : !array_v (a, p_arr, n) >> _ |
            i      : size_t i)
          :<!wrt> void =
        if i <> n then
          let
            val j = insertion_position<a> {n} (pf_arr | p_arr, i)
          in
            array_subcirculate<a> (!p_arr, j, i);
            loop (pf_arr | succ i)
          end
    in
      loop (pf_arr | i2sz 1)
    end

fn {a : vt@ype}
array_select_pivot
          {n      : pos}
          {p_arr  : addr}
          (pf_arr : array_v (a, p_arr, n) |
           p_arr  : ptr p_arr,
           n      : size_t n)
    :<!wrt> [n_before : nat | n_before + 1 <= n]
            @(array_v (a, p_arr, n_before),
              a @ (p_arr + (n_before * sizeof a)),
              array_v (a, p_arr + (n_before * sizeof a) + sizeof a,
                       n - n_before - 1) |
              size_t n_before) =
  let
    val [n_before : int] n_before =
      array_stable_quicksort$pivot_index<a> (!p_arr, n)
    prval @(pf_before, pf_more) =
      array_v_split {a} {p_arr} {n} {n_before} pf_arr
    prval @(pf_pivot, pf_after) = array_v_uncons pf_more
  in
    @(pf_before, pf_pivot, pf_after | n_before)
  end

fn {a : vt@ype}
partition_array_before_pivot
          {n          : pos}
          {n_before   : nat | n_before + 1 <= n}
          {p_arr      : addr}
          {p_work     : addr}
          {p_pivot    : addr}
          (pf_before  : array_v (a, p_arr, n_before),
           pf_work   : array_v (a?, p_work, n),
           pf_pivot  : !(a @ p_pivot) |
           p_arr     : ptr p_arr,
           p_work    : ptr p_work,
           p_pivot   : ptr p_pivot,
           n_before  : size_t n_before)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n_before]
            @(array_v (a, p_arr, n_le),
              array_v (a?!, p_arr + (n_le * sizeof a),
                       n_before - n_le),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
              size_t n_le,
              size_t n_ge) =
  let
    fun
    loop {i : nat | i <= n_before}
         {n0_le, n0_ge : nat | n0_le + n0_ge == i}
         .<n_before - i>.
         (pf_le      : array_v (a, p_arr, n0_le),
          pf_between : array_v (a?!, p_arr + (n0_le * sizeof a),
                                i - n0_le),
          pf_before  : array_v (a, p_arr + (i * sizeof a),
                                n_before - i),
          pf_ge      : array_v (a, p_work, n0_ge),
          pf_work    : array_v (a?, p_work + (n0_ge * sizeof a),
                                n - n0_ge),
          pf_pivot   : !(a @ p_pivot) |
          i          : size_t i,
          n0_le      : size_t n0_le,
          n0_ge      : size_t n0_ge)
        :<!wrt> [n_le, n_ge : nat | n_le + n_ge == n_before]
                @(array_v (a, p_arr, n_le),
                  array_v (a?!, p_arr + (n_le * sizeof a),
                           n_before - n_le),
                  array_v (a, p_work, n_ge),
                  array_v (a?, p_work + (n_ge * sizeof a),
                           n - n_ge) |
                  size_t n_le,
                  size_t n_ge) =
      if i = n_before then
        let
          prval () = array_v_unnil pf_before
        in
          @(pf_le, pf_between, pf_ge, pf_work | n0_le, n0_ge)
        end
      else
        let
          prval @(pf_src, pf_before) = array_v_uncons pf_before
          val p_src = ptr_add<a> (p_arr, i)
        in
          (* Move anything <= the pivot to the beginning of the array,
             and anything else to the workspace array. *)
          if array_stable_quicksort$lt<a> (!p_pivot, !p_src) then
            let          (* The element is > the pivot. Move it to the
                            workspace array. *)
              prval @(pf_dst, pf_work) = array_v_uncons pf_work
              val () =
                ptr_set<a> (pf_dst | ptr_add<a> (p_work, n0_ge),
                                     ptr_get<a> (pf_src | p_src))
              prval pf_ge = array_v_extend (pf_ge, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_le, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, n0_le, succ n0_ge)
            end
          else if i = n0_le then
            let   (* The element is <= to the pivot and already in the
                     correct place. *)
              prval () = lemma_mul_isfun {i, sizeof a}
                                         {n0_le, sizeof a} ()
              prval pf_between = array_v_unnil_nil{a?!, a} pf_between
              prval pf_between = array_v_extend (pf_between, pf_src)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              prval pf_le = array_v_extend (pf_le, pf_dst)
              prval pf_between = array_v_unnil_nil{a, a?!} pf_between
            in
              loop (pf_le, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, succ n0_le, n0_ge)
            end
          else
            let     (* The element is <= but not in the correct place.
                       Move it earlier in the same array. *)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              val p_dst = ptr_add<a> (p_arr, n0_le)
              val () =
                ptr_set<a>
                  (pf_dst | p_dst, ptr_get<a> (pf_src | p_src))
              prval pf_le = array_v_extend (pf_le, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_le, pf_between, pf_before,
                    pf_ge, pf_work, pf_pivot |
                    succ i, succ n0_le, n0_ge)
            end
        end

    prval pf_le = array_v_nil {a} {p_arr} ()
    prval pf_ge = array_v_nil {a} {p_work} ()
    prval pf_between = array_v_nil {a?!} {p_arr} ()
  in
    loop (pf_le, pf_between, pf_before,
          pf_ge, pf_work, pf_pivot |
          i2sz 0, i2sz 0, i2sz 0)
  end

fn {a : vt@ype}
partition_array_after_pivot
          {n          : pos}
          {n_before   : nat | n_before + 1 <= n}
          {n0_le      : nat}
          {n0_ge      : nat | n0_le + n0_ge == n_before}
          {p_arr      : addr}
          {p_work     : addr}
          {p_pivot    : addr}
          (pf_le      : array_v (a, p_arr, n0_le),
           pf_between : array_v (a?!, p_arr + (n0_le * sizeof a),
                                 n_before - n0_le + 1),
           pf_after   : array_v
                          (a,
                           p_arr + (n_before * sizeof a) + sizeof a,
                           n - n_before - 1),
           pf_ge      : array_v (a, p_work, n0_ge),
           pf_work    : array_v (a?, p_work + (n0_ge * sizeof a),
                                 n - n0_ge),
           pf_pivot   : !(a @ p_pivot) |
           p_arr      : ptr p_arr,
           p_work     : ptr p_work,
           p_pivot    : ptr p_pivot,
           n          : size_t n,
           n0_le      : size_t n0_le,
           n0_ge      : size_t n0_ge)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge + 1 == n]
            @(array_v (a, p_arr, n_le),
              array_v (a?!, p_arr + (n_le * sizeof a), n - n_le),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
              size_t n_le,
              size_t n_ge) =
  let
    fun
    loop {n1_le      : nat}
         {n1_ge      : nat | n0_ge <= n1_ge}
         {i          : int | n_before + 1 <= i; i <= n;
                             n1_le + n1_ge + 1 == i}
         .<n - i>.
         (pf_le      : array_v (a, p_arr, n1_le),
          pf_between : array_v (a?!, p_arr + (n1_le * sizeof a),
                                i - n1_le),
          pf_after   : array_v (a, p_arr + (i * sizeof a), n - i),
          pf_ge      : array_v (a, p_work, n1_ge),
          pf_work    : array_v (a?, p_work + (n1_ge * sizeof a),
                                n - n1_ge),
          pf_pivot   : !(a @ p_pivot) |
          i          : size_t i,
          n1_le      : size_t n1_le,
          n1_ge      : size_t n1_ge)
        :<!wrt> [n_le, n_ge : nat | n_le + n_ge + 1 == n]
                @(array_v (a, p_arr, n_le),
                  array_v (a?!, p_arr + (n_le * sizeof a), n - n_le),
                  array_v (a, p_work, n_ge),
                  array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
                  size_t n_le,
                  size_t n_ge) =
      if i = n then
        let
          prval () = array_v_unnil pf_after
        in
          @(pf_le, pf_between, pf_ge, pf_work | n1_le, n1_ge)
        end
      else
        let
          prval @(pf_src, pf_after) = array_v_uncons pf_after
          val p_src = ptr_add<a> (p_arr, i)
        in
          (* Move anything < the pivot to the beginning of the array,
             and anything else to the workspace array. *)
          if ~array_stable_quicksort$lt<a> (!p_src, !p_pivot) then
            let         (* The element is >= the pivot. Move it to the
                           workspace array. *)
              prval @(pf_dst, pf_work) = array_v_uncons pf_work
              val () =
                ptr_set<a> (pf_dst | ptr_add<a> (p_work, n1_ge),
                                     ptr_get<a> (pf_src | p_src))
              prval pf_ge = array_v_extend (pf_ge, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_le, pf_between, pf_after,
                    pf_ge, pf_work, pf_pivot |
                    succ i, n1_le, succ n1_ge)
            end
          else
            let  (* The element is < the pivot. Move it earlier in the
                    same array. *)
              prval @(pf_dst, pf_between) = array_v_uncons pf_between
              val () =
                ptr_set<a> (pf_dst | ptr_add<a> (p_arr, n1_le),
                                     ptr_get<a> (pf_src | p_src))
              prval pf_le = array_v_extend (pf_le, pf_dst)
              prval pf_between = array_v_extend (pf_between, pf_src)
            in
              loop (pf_le, pf_between, pf_after,
                    pf_ge, pf_work, pf_pivot |
                    succ i, succ n1_le, n1_ge)
            end
        end

    prval () = lemma_mul_isfun {n_before + 1, sizeof a}
                               {n0_le + n0_ge + 1, sizeof a} ()
  in
    loop (pf_le, pf_between, pf_after,
          pf_ge, pf_work, pf_pivot |
          succ (n0_le + n0_ge), n0_le, n0_ge)
  end

fn {a : vt@ype}
partition_array_after_pivot_removal
          {n          : pos}
          {n_before   : nat | n_before + 1 <= n}
          {p_arr      : addr}
          {p_work     : addr}
          {p_pivot    : addr}
          (pf_before  : array_v (a, p_arr, n_before),
           pf_emptied : a?! @ (p_arr + (n_before * sizeof a)),
           pf_after   : array_v
                          (a,
                           p_arr + (n_before * sizeof a) + sizeof a,
                           n - n_before - 1),
           pf_work   : array_v (a?, p_work, n),
           pf_pivot  : !(a @ p_pivot) |
           p_arr     : ptr p_arr,
           p_work    : ptr p_work,
           p_pivot   : ptr p_pivot,
           n         : size_t n,
           n_before  : size_t n_before)
    :<!wrt> [n_le, n_ge : nat | n_le + n_ge + 1 == n]
            @(array_v (a, p_arr, n_le),
              array_v (a?!, p_arr + (n_le * sizeof a), n - n_le),
              array_v (a, p_work, n_ge),
              array_v (a?, p_work + (n_ge * sizeof a), n - n_ge) |
              size_t n_le,
              size_t n_ge) =
  let
    val @(pf_le, pf_between, pf_ge, pf_work | n_le, n_ge) =
      partition_array_before_pivot<a>
        (pf_before, pf_work, pf_pivot |
         p_arr, p_work, p_pivot, n_before)
    prval pf_between = array_v_extend (pf_between, pf_emptied)
  in
    partition_array_after_pivot<a>
      {n} {n_before}
      (pf_le, pf_between, pf_after, pf_ge, pf_work, pf_pivot |
       p_arr, p_work, p_pivot, n, n_le, n_ge)
  end

fn {a : vt@ype}
select_pivot_and_partition_array
          {n         : pos}
          {p_arr     : addr}
          {p_work    : addr}
          (pf_arr    : array_v (a, p_arr, n),
           pf_work   : array_v (a?, p_work, n) |
           p_arr     : ptr p_arr,
           p_work    : ptr p_work,
           n         : size_t n)
    :<!wrt> [n_le : nat | n_le + 1 <= n]
            @(array_v (a, p_arr, n_le),
              a @ (p_arr + (n_le * sizeof a)),
              array_v (a, p_arr + (n_le * sizeof a) + sizeof a,
                       n - n_le - 1),
              array_v (a?, p_work, n) |
              size_t n_le) =
  let
    (* Split the array at a pivot. *)
    val @(pf_before, pf_pivot_entry, pf_after | n_before) =
      array_select_pivot<a> (pf_arr | p_arr, n)

    (* Remove the pivot from the array. Move it to the stack frame. *)
    var pivot =
      ptr_get<a> (pf_pivot_entry | ptr_add<a> (p_arr, n_before))

    (* Partition into stuff <= the pivot in the original array, and
       stuff >= the pivot in the workspace array. *)
    val [n_le : int, n_ge : int]
        @(pf_le, pf_after_le, pf_ge, pf_after_ge | n_le, n_ge) =
      partition_array_after_pivot_removal<a>
        (pf_before, pf_pivot_entry, pf_after, pf_work, view@ pivot |
         p_arr, p_work, addr@ pivot, n, n_before)

    (* Move the pivot, and the stuff that is now in the workspace
       array, back into the original array. *)
    prval @(pf_pivot_entry1, pf_ge1) = array_v_uncons pf_after_le
    val p_pivot_entry1 = ptr_add<a> (p_arr, n_le)
    val p_ge1 = ptr1_succ<a> p_pivot_entry1
    val () = ptr_set<a> (pf_pivot_entry1 | p_pivot_entry1, pivot)
    val () = array_copy<a> (!p_ge1, !p_work, n_ge)

    (* Restore the view of the workspace array. *)
    prval pf_ge = discard_used_contents {a} pf_ge
    prval () = lemma_mul_isfun {n - n_le - 1, sizeof a}
                               {n_ge, sizeof a} ()
    prval pf_work = array_v_unsplit (pf_ge, pf_after_ge)
  in
    @(pf_le, pf_pivot_entry1, pf_ge1, pf_work | n_le)
  end

implement {a}
array_stable_quicksort_given_workspace {n} (arr, n, workspace) =
  if n = 0 then
    ()
  else
    let
      fun
      recurs {n1      : nat | n1 <= n}
             {p_arr1  : addr}
             {p_work  : addr}
             .<n1>.
             (pf_arr1 : !array_v (a, p_arr1, n1) >> _,
              pf_work : !array_v (a?, p_work, n) >> _ |
              p_arr1  : ptr p_arr1,
              p_work  : ptr p_work,
              n1      : size_t n1)
          :<!wrt> void =
        if n1 <= array_stable_quicksort$small<a> () then
          array_insertion_sort<a> (pf_arr1 | p_arr1, n1)
        else
          let
            prval @(pf_work1, pf_not_used) =
              array_v_split {a?} {..} {n} {n1} pf_work

            val [n1_le : int]
                @(pf_le, pf_pivot, pf_ge, pf_work1 | n1_le) =
              select_pivot_and_partition_array<a>
                (pf_arr1, pf_work1 | p_arr1, p_work, n1)

            prval () = pf_work :=
              array_v_unsplit (pf_work1, pf_not_used)

            val p_le = p_arr1
            and p_ge = ptr_add<a> (p_arr1, succ n1_le)
            and n1_ge = n1 - succ n1_le
          in
            (* Handle the smaller side of the partition first, to
               reduce stack blowup. The larger side of the partition
               is handled by a tail recursion. *)
            if n1_le < n1_ge then
              let
                val () = recurs (pf_le, pf_work | p_le, p_work, n1_le)
                val () = recurs (pf_ge, pf_work | p_ge, p_work, n1_ge)
                prval () = pf_arr1 := array_v_extend (pf_le, pf_pivot)
                prval () = pf_arr1 := array_v_unsplit (pf_arr1, pf_ge)
              in
              end
            else
              let
                val () = recurs (pf_ge, pf_work | p_ge, p_work, n1_ge)
                val () = recurs (pf_le, pf_work | p_le, p_work, n1_le)
                prval () = pf_arr1 := array_v_extend (pf_le, pf_pivot)
                prval () = pf_arr1 := array_v_unsplit (pf_arr1, pf_ge)
              in
              end
          end

      prval () = lemma_array_param arr
    in
      recurs (view@ arr, view@ workspace |
              addr@ arr, addr@ workspace, n)
    end

implement {a}
array_stable_quicksort_not_given_workspace {n} (arr, n) =
  let
    fn
    quicksort {n         : int}
              (arr       : &array (a, n),
               n         : size_t n,
               workspace : &array (a?, n))
        :<!wrt> void =
      array_stable_quicksort_given_workspace<a> (arr, n, workspace)

    prval () = lemma_array_param arr
  in
    if n <= ARRAY_STACK_STORAGE_THRESHOLD then
      let
        var storage : @[a?][ARRAY_STACK_STORAGE_THRESHOLD]

        prval @(pf_work, pf_rest) =
          array_v_split {a?} {..} {ARRAY_STACK_STORAGE_THRESHOLD} {n}
                        (view@ storage)
        val () = quicksort (arr, n, !(addr@ storage))
        prval () = view@ storage := array_v_unsplit (pf_work, pf_rest)
      in
      end
    else
      let
        val @(pf_work, pfgc_work | p_work) = array_ptr_alloc<a?> n
        val () = quicksort (arr, n, !p_work)
        val () = array_ptr_free (pf_work, pfgc_work | p_work)
      in
      end
  end

(*------------------------------------------------------------------*)
