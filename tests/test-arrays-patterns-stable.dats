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

#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"
#include "quicksorts/HATS/stable-quicksort.hats"

%{^

#include <time.h>

atstype_ldouble
get_clock (void)
{
  return ((atstype_ldouble) clock ()) / CLOCKS_PER_SEC;
}

int
intcmp (const void *x, const void *y)
{
  const int i = *(const int *) x;
  const int j = *(const int *) y;
  return (i < j) ? -1 : ((i == j) ? 0 : 1);
}

%}

extern fn
get_clock :
  () -<> ldouble = "mac#"

(*------------------------------------------------------------------*)
(* A simple linear congruential generator.                          *)

(* The multiplier lcg_a comes from Steele, Guy; Vigna, Sebastiano (28
   September 2021). "Computationally easy, spectrally good multipliers
   for congruential pseudorandom number generators".
   arXiv:2001.05304v3 [cs.DS] *)
macdef lcg_a = $UN.cast{uint64} 0xf1357aea2e62a9c5LLU

(* lcg_c must be odd. *)
macdef lcg_c = $UN.cast{uint64} 0x1234567891234567LLU

var seed : uint64 = $UN.cast 0
val p_seed = addr@ seed

fn
random_double ()
    :<!wrt> double =
  let
    val (pf, fpf | p_seed) = $UN.ptr0_vtake{uint64} p_seed
    val old_seed = ptr_get<uint64> (pf | p_seed)

    (* IEEE "binary64" or "double" has 52 bits of precision. We will
       take the high 48 bits of the seed and divide it by 2**48, to
       get a number 0.0 <= randnum < 1.0 *)
    val high_48_bits = $UN.cast{double} (old_seed >> 16)
    val divisor = $UN.cast{double} (1LLU << 48)
    val randnum = high_48_bits / divisor

    (* The following operation is modulo 2**64, by virtue of standard
       C behavior for uint64_t. *)
    val new_seed = (lcg_a * old_seed) + lcg_c

    val () = ptr_set<uint64> (pf | p_seed, new_seed)
    prval () = fpf pf
  in
    randnum
  end

fn
random_int (m : int, n : int)
    :<!wrt> int =
  m + $UN.cast{int} (random_double () * (n - m + 1))

(*------------------------------------------------------------------*)

#define MAX_SZ 10000000

fn
array_stable_quicksort_int
            {n   : int}
            (arr : &array (int, n),
             n   : size_t n)
    :<!wrt> void =
  let
    implement
    array_stable_quicksort$lt<int> (x, y) =
      x < y

    (* implement *)
    (* array_stable_quicksort$pivot_index<int> (arr, n) = *)
    (*   array_stable_quicksort_pivot_index_median_of_three_random<int> *)
    (*     (arr, n) *)
  in
    array_stable_quicksort<int> {n} (arr, n)
  end

fn {}
test_arrays_with_int_keys () : void =
  let
    var sz : Size_t
  in
    for (sz := i2sz 0;
         sz <= i2sz MAX_SZ;
         sz := max (i2sz 1, i2sz 10 * sz))
      let
        val @(pf1, pfgc1 | p1) = array_ptr_alloc<int> sz
        val () = array_initize<int> (!p1, sz)

        val @(pf2, pfgc2 | p2) = array_ptr_alloc<int> sz
        val () = array_copy<int> (!p2, !p1, sz)
        val t11 = get_clock ()
        val () = $extfcall (void, "qsort", p2, sz, sizeof<int>,
                            $extval(ptr, "intcmp"))
        val t12 = get_clock ()
        val t1 = t12 - t11
        val lst2 = list_vt2t (array2list (!p2, sz))

        val @(pf3, pfgc3 | p3) = array_ptr_alloc<int> sz
        val () = array_copy<int> (!p3, !p1, sz)
        val t21 = get_clock ()
        val () = array_stable_quicksort_int (!p3, sz)
        val t22 = get_clock ()
        val t2 = t22 - t21
        val lst3 = list_vt2t (array2list (!p3, sz))
      in
        assertloc (lst2 = lst3);
        print! "  qsort:";
        print! t1;
        print! "  quick:";
        print! t2;
        print! "  ";
        print! sz;
        println! ();
        array_ptr_free (pf1, pfgc1 | p1);
        array_ptr_free (pf2, pfgc2 | p2);
        array_ptr_free (pf3, pfgc3 | p3)
      end
  end

fn
test_random_arrays_with_int_keys () : void =
  let
    implement
    array_initize$init<int> (i, x) =
      x := random_int (~1000, 1000)
  in
    println! "Random arrays:";
    test_arrays_with_int_keys<> ()
  end

fn
test_presorted_arrays_with_int_keys () : void =
  let
    implement
    array_initize$init<int> (i, x) =
      x := sz2i i
  in
    println! "Pre-sorted arrays:";
    test_arrays_with_int_keys<> ()
  end

fn
test_reverse_presorted_arrays_with_int_keys () : void =
  let
    implement
    array_initize$init<int> (i, x) =
      x := ~(sz2i i)
  in
    println! "Reverse pre-sorted arrays:";
    test_arrays_with_int_keys<> ()
  end

fn
test_sign_reversal_random_arrays_with_int_keys () : void =
  let
    implement
    array_initize$init<int> (i, x) =
      if i mod (i2sz 2) = i2sz 0 then
        x := random_int (1, 1000)
      else
        x := random_int (~1000, ~1)
  in
    println! "Sign-reversal random arrays:";
    test_arrays_with_int_keys<> ()
  end

fn
test_constant_arrays_with_int_keys () : void =
  let
    implement
    array_initize$init<int> (i, x) =
      x := 1
  in
    println! "Constant arrays:";
    test_arrays_with_int_keys<> ()
  end

fn
test_sign_reversal_constant_arrays_with_int_keys () : void =
  let
    implement
    array_initize$init<int> (i, x) =
      if i mod (i2sz 2) = i2sz 0 then
        x := 1
      else
        x := ~1
  in
    println! "Sign-reversal constant arrays:";
    test_arrays_with_int_keys<> ()
  end

(*------------------------------------------------------------------*)

implement
main0 () =
  begin
    test_random_arrays_with_int_keys ();
    test_presorted_arrays_with_int_keys ();
    test_reverse_presorted_arrays_with_int_keys ();
    test_sign_reversal_random_arrays_with_int_keys ();
    test_constant_arrays_with_int_keys ();
    test_sign_reversal_constant_arrays_with_int_keys ()
  end

(*------------------------------------------------------------------*)
