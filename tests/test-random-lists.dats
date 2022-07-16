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
#include "stable-quicksort/HATS/stable-quicksort.hats"

%{^

#include <time.h>

atstype_ldouble
get_clock (void)
{
  return ((atstype_ldouble) clock ()) / CLOCKS_PER_SEC;
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

#define NIL list_vt_nil ()
#define ::  list_vt_cons

implement
list_vt_mergesort$cmp<int> (x, y) =
  if x < y then
    ~1
  else if x = y then
    0
  else
    1

implement
list_vt_stable_quicksort$cmp<int> (x, y) =
  list_vt_mergesort$cmp<int> (x, y)

fn
test_random_lists () =
  let
    var sz : [i : nat] int i
  in
    for (sz := 0; sz <= MAX_SZ; sz := max (1, 10 * sz))
      let
        val sz_val = sz

        fun
        make_list {n   : nat}
                  (lst : list_vt (int, n),
                   n   : int n)
            : List_vt int =
          if n = sz_val then
            lst
          else
            make_list (random_int (~1000, 1000) :: lst, succ n)

        val lst1 = make_list (NIL, 0)
        val lst2 = list_vt_mergesort<int> (copy<int> lst1)
        val lst3 = list_vt_stable_quicksort<int> (copy<int> lst1)

        val () = println! "--------------------"
        val () = println! lst3

        val () = free lst1
        val () = free lst2
        val () = free lst3
      in
      end
  end

(*------------------------------------------------------------------*)

implement
main0 () =
  begin
    test_random_lists ()
  end

(*------------------------------------------------------------------*)
