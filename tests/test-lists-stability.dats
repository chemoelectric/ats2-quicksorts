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

(*------------------------------------------------------------------*)

typedef String4 = [n : int | 4 <= n] string n

fn
String4_to_uint64
          (s : String4)
    :<> uint64 =
  let
    val c3 = string_get_at (s, 0)
    val c2 = string_get_at (s, 1)
    val c1 = string_get_at (s, 2)
    val c0 = string_get_at (s, 3)
  in
    ($UN.cast{uint64} c3 << 24) lor
      ($UN.cast{uint64} c2 << 16) lor
        ($UN.cast{uint64} c1 << 8) lor
          ($UN.cast{uint64} c0)
  end

implement
list_vt_stable_quicksort$cmp<String4> (x, y) =
  (* Sort strings by their first four characters. *)
  let
    val sx = String4_to_uint64 x
    and sy = String4_to_uint64 y
  in
    if sx < sy then
      ~1
    else if sx = sy then
      0
    else
      1
  end

fn
test_stability () =
  let
    val data =
      $list ("forewarned", "overshoot", "pansy", "forewarn",
             "forecastle", "pans", "pansophies", "overbear",
             "forest", "overt", "foreclose", "pansexuality",
             "overly", "overopinionated", "pansexual",
             "pansophy", "forelorn", "overbearing", "fore")

    val expected =
      $list ("forewarned", "forewarn", "forecastle", "forest",
             "foreclose", "forelorn", "fore", "overshoot",
             "overbear", "overt", "overly", "overopinionated",
             "overbearing", "pansy", "pans", "pansophies",
             "pansexuality", "pansexual", "pansophy")

    val lst = $UN.castvwtp0{list_vt (String4, 19)} data
    val lst = list_vt_stable_quicksort<String4> lst
    val lst = list_vt2t lst

    var i : [i : nat | i <= 19] int i
  in
    for (i := 0; i <> 19; i := succ i)
      begin
        println! ("\"", lst[i], "\"");
        assertloc (lst[i] = expected[i])
      end
  end

(*------------------------------------------------------------------*)

implement
main0 () =
  begin
    test_stability ()
  end

(*------------------------------------------------------------------*)
