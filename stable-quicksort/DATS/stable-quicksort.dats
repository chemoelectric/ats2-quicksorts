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

#include "share/atspre_staload.hats"
staload "stable-quicksort/SATS/stable-quicksort.sats"
staload UN = "prelude/SATS/unsafe.sats"

#define NIL list_vt_nil ()
#define ::  list_vt_cons

(*------------------------------------------------------------------*)
(* A simple linear congruential generator, for pivot selection.     *)

%{
ats2_stable_quicksort_spinlock_t ats2_stable_quicksort_seed_lock;
uint64_t ats2_stable_quicksort_seed = 0;
%}

extern fn
random_uint64 () :<!wrt> uint64 = "mac#%"

(*------------------------------------------------------------------*)
(* An insertion sort for small sublists.                            *)

(* Inserting in reverse order minimizes the work for a list already
   nearly sorted, or for stably sorting a list whose entries often
   have equal keys. *)
fun {a : vt@ype}
list_vt_insert_reverse
          {m       : nat}
          {p_xnode : addr}
          {p_x     : addr}
          {p_xs    : addr}
          .<m>.
          (pf_x  : a @ p_x,
           pf_xs : list_vt (a, 0)? @ p_xs |
           dst   : &list_vt (a, m) >> list_vt (a, m + 1),
           xnode : list_vt_cons_unfold (p_xnode, p_x, p_xs),
           p_x   : ptr p_x,
           p_xs  : ptr p_xs)
    :<!wrt> void =
  (* dst is some tail of the current (reverse-order) destination list.
     xnode is the current node in the source list.
     p_x points to the node's CAR.
     p_xs points to the node's CDR. *)
  case+ dst of
  | @ (y :: ys) =>
    if list_vt_stable_quicksort$lt<a> (!p_x, y) then
      let                     (* Move to the next destination node. *)
        val () =
          list_vt_insert_reverse (pf_x, pf_xs | ys, xnode, p_x, p_xs)
        prval () = fold@ dst
      in
      end
    else
      let                       (* Insert xnode here. *)
        prval () = fold@ dst
        val () = !p_xs := dst
        val () = dst := xnode
        prval () = fold@ dst
      in
      end
  | ~ NIL =>
    let                         (* Put xnode at the end. *)
      val () = dst := xnode
      val () = !p_xs := NIL
      prval () = fold@ dst
    in
    end

(* An insertion sort that accepts a prefix of data already sorted in
   reverse. *)
fn {a : vt@ype}
list_vt_insertion_sort
          {m, n            : int}
          (lst             : list_vt (INV(a), m),
           reversed_prefix : list_vt (INV(a), n))
    :<!wrt> list_vt (a, m + n) =
  let
    fun                         (* Create a list sorted in reverse. *)
    loop {m, n : nat}
         .<m>.
         (src : list_vt (a, m),
          dst : &list_vt (a, n) >> list_vt (a, m + n))
        :<!wrt> void =
      case+ src of
      | @ (x :: xs) =>
        let
          val tail = xs
        in
          list_vt_insert_reverse<a>
            (view@ x, view@ xs | dst, src, addr@ x, addr@ xs);
          loop (tail, dst)
        end
      | ~ NIL => ()             (* We are done. *)

    prval () = lemma_list_vt_param lst
    prval () = lemma_list_vt_param reversed_prefix
    
    var dst : list_vt (a, n) = reversed_prefix
  in
    loop (lst, dst);
    list_vt_reverse<a> dst
  end

(*------------------------------------------------------------------*)

fn {a : vt@ype}
select_pivot_index
          {n   : pos}
          (lst : !list_vt (a, n),
           n   : int n)
    :<!wrt> [i : nat | i < n]
            int i =
  let
    val u64_n : uint64 n = g1i2u n
    val u64_rand : [i : nat] uint64 i = g1ofg0 (random_uint64 ())
    val u64_pivot = g1uint_mod (u64_rand, u64_n)
    val i_pivot : [i : nat | i < n] int i = g1u2i u64_pivot
  in
    i_pivot
  end

fn {a : vt@ype}
is_lt_pivot {m        : pos}
            {p_pivot  : addr | null < p_pivot}
            (x        : &a,
             p2_pivot : p2tr (list_vt (a, m), p_pivot))
    :<> bool =
  let
    val @(pf, fpf | p) = $UN.p2tr_vtake p2_pivot
    val+ @ (pivot :: _) = !p
    val is_lt = list_vt_stable_quicksort$lt<a> (x, pivot)
    prval () = fold@ (!p)
    prval () = fpf pf
  in
    is_lt
  end

fn {a : vt@ype}
head_is_lt_pivot
          {n        : pos}
          {m        : pos}
          {p_pivot  : addr | null < p_pivot}
          (lst      : &list_vt (a, n),
           p2_pivot : p2tr (list_vt (a, m), p_pivot))
    :<> bool =
  let
    val+ @ (head :: _) = lst
    val is_lt = is_lt_pivot<a> (head, p2_pivot)
    prval () = fold@ lst
  in
    is_lt
  end

absvt@ype extensible_list_vt (a : vt@ype+, n : int) =
  @(list_vt (a, n),
    P2tr1 (List0_vt a))

fn {a : vt@ype}
extensible_list_vt_nil ()
    :<> extensible_list_vt (a, 0) =
  $UN.castvwtp0 @(NIL, 0)

fn {a : vt@ype}
extensible_list_vt_append
          {n1, n2 : int | 0 <= n1; 1 <= n2}
          (lst1   : extensible_list_vt (a, n1),
           lst2   : extensible_list_vt (a, n2))
    :<!wrt> extensible_list_vt (a, n1 + n2) =
  let
    vtypedef elist_vt (n : int) = @(list_vt (a, n),
                                    P2tr1 (List1_vt a))
    val @(ls_1, p2_1) = $UN.castvwtp0{elist_vt n1} lst1
    val @(pf, fpf | p) = $UN.p2tr_vtake p2_1
    val+ @ (_ :: tail) = !p
    val @(ls_2, p2_2) = $UN.castvwtp0{elist_vt n2} lst2
    val- ~ NIL = tail     (* Extend only if the pointer is to the last
                             node. *)
    val () = tail := ls_2
    prval () = fold@ (!p)
    prval () = fpf pf
  in
    $UN.castvwtp0 @(ls_1, p2_2)
  end

fn {a : vt@ype}
extensible_list_vt_finalize
          {n   : nat}
          (lst : extensible_list_vt (a, n))
    :<!wrt> list_vt (a, n) =
  let
    vtypedef elist_vt (n : int) = @(list_vt (a, n),
                                    P2tr1 (List0_vt a))
    val @(ls_1, _) = $UN.castvwtp0{elist_vt n} lst
  in
    ls_1
  end

fn {a : vt@ype}
split_after_run
          {m        : pos}
          {np       : pos}
          {p        : addr | null < p}
          (lst      : list_vt (a, m),
           m        : int m,
           p2_pivot : p2tr (list_vt (a, np), p),
           is_lt    : bool)
    :<!wrt> [m1, m2 : int | 1 <= m1; 0 <= m2; m1 + m2 == m]
            @(extensible_list_vt (a, m1),
              list_vt (a, m2),
              int m1,
              int m2) =
  let
    fun
    loop {m : pos}
         .<m>.
         (lst1 : &list_vt (a, m) >> list_vt (a, m1),
          lst2 : &list_vt (a, 0)? >> list_vt (a, m2),
          m    : int m)
        :<!wrt> #[m1, m2 : int | 1 <= m1; 0 <= m2; m1 + m2 == m]
                @(int m2, P2tr1 (list_vt (a, 1))) =
      let
        val+ @ (head :: tail) = lst1
      in
        case+ tail of
        | NIL =>
          let
            val () = lst2 := NIL
            prval () = fold@ lst1
          in
            @(0, $UN.ptr2p2tr ($UN.cast2Ptr1 (addr@ lst1)))
          end
        | _ :: _ =>
          if head_is_lt_pivot<a> (tail, p2_pivot) = is_lt then
            let
              val retval = loop (tail, lst2, pred m)
              prval () = fold@ lst1
            in
              retval
            end
          else
            let
              val () = lst2 := tail
              val () = tail := NIL
              prval () = fold@ lst1
            in
              @(pred m, $UN.ptr2p2tr ($UN.cast2Ptr1 (addr@ lst1)))
            end
      end

    var lst1 = lst
    var lst2 : List_vt a
    val @(m2, p2_last) = loop (lst1, lst2, m)
  in
    @($UN.castvwtp0 @(lst1, p2_last), lst2, m - m2, m2)
  end

fn {a : vt@ype}
apply_pivot
          {m        : pos}
          {np       : pos}
          {p        : addr | null < p}
          (lst      : list_vt (a, m),
           m        : int m,
           p2_pivot : p2tr (list_vt (a, np), p),
           lst_low  : &list_vt (a, 0)? >> list_vt (a, m1),
           lst_high : &list_vt (a, 0)? >> list_vt (a, m2),
           m1       : &int? >> int m1,
           m2       : &int? >> int m2)
    :<!wrt> #[m1, m2 : int | m1 + m2 == m]
            void =
  let
    var elst_low : [n : nat] extensible_list_vt (a, n)
    var elst_high : [n : nat] extensible_list_vt (a, n)

    fn
    run_of_low {n        : pos}
               {m1, m2   : nat | m1 + m2 + n == m}
               (lst      : list_vt (a, n),
                n        : int n,
                elst_low : &extensible_list_vt (a, m1)
                            >> extensible_list_vt (a, mm1),
                m1       : &int m1 >> int mm1,
                m2       : int m2)
        :<!wrt> #[mm1, n2 : int | m1 < mm1; 0 <= n2; n2 < n;
                                  mm1 + m2 + n2 == m]
                @(list_vt (a, n2), int n2) =
      let
        val @(elst1, lst2, n1, n2) =
          split_after_run<a> (lst, n, p2_pivot, true)
      in
        elst_low := extensible_list_vt_append<a> (elst_low, elst1);
        m1 := m1 + n1;
        @(lst2, n2)
      end

    fn
    run_of_high {n         : pos}
                {m1, m2    : nat | m1 + m2 + n == m}
                (lst       : list_vt (a, n),
                 n         : int n,
                 elst_high : &extensible_list_vt (a, m2)
                              >> extensible_list_vt (a, mm2),
                 m1        : int m1,
                 m2        : &int m2 >> int mm2)
        :<!wrt> #[mm2, n2 : int | m2 < mm2; 0 <= n2; n2 < n;
                                  m1 + mm2 + n2 == m]
                @(list_vt (a, n2), int n2) =
      let
        val @(elst1, lst2, n1, n2) =
          split_after_run<a> (lst, n, p2_pivot, false)
      in
        elst_high := extensible_list_vt_append<a> (elst_high, elst1);
        m2 := m2 + n1;
        @(lst2, n2)
      end

    fun
    loop {n      : nat}
         {m1, m2 : nat | m1 + m2 + n == m}
         .<n>.
         (lst       : list_vt (a, n),
          n         : int n,
          is_lt     : bool,
          elst_low  : &extensible_list_vt (a, m1)
                       >> extensible_list_vt (a, mm1),
          elst_high : &extensible_list_vt (a, m2)
                       >> extensible_list_vt (a, mm2),
          m1        : &int m1 >> int mm1,
          m2        : &int m2 >> int mm2)
        :<!wrt> #[mm1, mm2 : nat | mm1 + mm2 == m]
                void =
      if n = 0 then
        let
          val+ ~ NIL = lst
        in
        end
      else if is_lt then
        let
          val @(lst, n) = run_of_low (lst, n, elst_low, m1, m2)
        in
          loop (lst, n, false, elst_low, elst_high, m1, m2)
        end
      else
        let
          val @(lst, n) = run_of_high (lst, n, elst_high, m1, m2)
        in
          loop (lst, n, true, elst_low, elst_high, m1, m2)
        end

    fn
    head_lt_pivot
              {n   : pos}
              (lst : list_vt (a, n))
        :<> @(bool, list_vt (a, n)) =
      let
        var lst = lst
      in
        @(head_is_lt_pivot<a> (lst, p2_pivot), lst)
      end

    val @(is_lt, lst) = head_lt_pivot lst
  in
    elst_low := extensible_list_vt_nil<a> ();
    elst_high := extensible_list_vt_nil<a> ();
    m1 := 0;
    m2 := 0;
    loop (lst, m, is_lt, elst_low, elst_high, m1, m2);
    lst_low := extensible_list_vt_finalize<a> elst_low;
    lst_high := extensible_list_vt_finalize<a> elst_high
  end

fn {a : vt@ype}
find_and_apply_pivot
          {n        : pos}
          (lst      : list_vt (a, n),
           n        : int n,
           lst_low  : &list_vt (a, 0)? >> list_vt (a, n_low),
           lst_high : &list_vt (a, 0)? >> list_vt (a, n_high),
           n_low    : &int? >> int n_low,
           n_high   : &int? >> int n_high)
    :<!wrt> #[n_low, n_high : int | n_low + n_high == n]
            void =
  let
    var lst = lst
    val i_pivot = select_pivot_index (lst, n)
    val p2_pivot = list_vt_getref_at<a> (lst, i_pivot)
  in
    apply_pivot<a> (lst, n, p2_pivot, lst_low, lst_high,
                    n_low, n_high)
  end

(*------------------------------------------------------------------*)
