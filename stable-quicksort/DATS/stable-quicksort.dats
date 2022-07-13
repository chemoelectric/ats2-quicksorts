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

(*
fn {a : vt@ype}
head_exists_and_is_lt_pivot
          {n        : nat}
          {np       : pos}
          {p        : addr | null < p}
          (lst      : &list_vt (a, n),
           p2_pivot : p2tr (list_vt (a, np), p))
    :<> bool =
  case+ lst of
  | NIL => false
  | @ (head :: _) =>
    let
      val is_lt = is_lt_pivot<a> (head, p2_pivot)
      prval () = fold@ lst
    in
      is_lt
    end
*)

(*
fun {a : vt@ype}
list_vt_append_node
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
  let                         (* Put xnode at the end. *)
    val () = dst := xnode
    val () = !p_xs := NIL
    prval () = fold@ dst
  in
  end
*)

(*
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
*)

fn {a : vt@ype}
split_after_run
          {m        : pos}
          {np       : pos}
          {p        : addr | null < p}
          (lst      : list_vt (a, m),
           m        : int m,
           p2_pivot : p2tr (list_vt (a, np), p),
           is_lt    : bool,
           lst1     : &list_vt (a, 0)? >> list_vt (a, n),
           n        : &int >> int n,
           p2_last  : &P2tr1 (list_vt (a, 1))?
                      >> P2tr1 (list_vt (a, 1)),
           lst2     : &list_vt (a, 0)? >> list_vt (a, m - n))
    :<!wrt> #[n : nat | n <= m] void =
  let
    fun
    loop {m : pos}
         .<m>.
         (lst1 : &list_vt (a, m) >> list_vt (a, m1),
          lst2 : &list_vt (a, 0)? >> list_vt (a, m2),
          m    : int m)
        :<!wrt> #[m1, m2 : nat | m1 + m2 == m]
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
          if head_is_lt_pivot<a> (tail, p2_pivot) then
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
              @(m - 1, $UN.ptr2p2tr ($UN.cast2Ptr1 (addr@ lst1)))
            end
      end

    val () = lst1 := lst
    val @(m2, p2) = loop (lst1, lst2, m)
  in
    n := m - m2;
    p2_last := p2
  end

fn {a : vt@ype}
apply_pivot_index
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

    fun
    append_to_low_or_high
                {m : pos}
                .<m>.
                (lst      : &list_vt (a, m)
                            >> list_vt (a, m - m_low - m_high),
                 m        : int m,
                 head_lt_pivot : bool,
                 lst_low  : &list_vt (a, 0) >> list_vt (a, m_low),
                 lst_high : &list_vt (a, 0) >> list_vt (a, m_high),
                 m_low    : &int? >> int m_low,
                 m_high   : &int? >> int m_high)
        :<!wrt> #[m_low, m_high : nat | m_low + m_high <= m]
                void =
      let
        fn
        append_to_destination
                  {m      : pos}
                  (lst    : &list_vt (a, m) >> list_vt (a, m - m_dst),
                   dst    : &list_vt (a, 0) >> list_vt (a, m_dst),
                   m_dst  : &int? >> int m_dst)
            :<!wrt> #[m_dst : nat | m_dst <= m]
                    void =
          let
            val+ @ (head :: tail) = lst
(*
          in
            if head_exists_and_is_lt_pivot<a> (tail, p2_pivot) then
              let
                val tl = tail
                val () = tail := NIL
                prval () = fold@ lst
                val+ ~ NIL = dst
                val () = dst := lst
                val () = lst := tl
              in
                m_dst := 1
              end
            else
              let
*)
                val tl = tail
                val () = tail := NIL
                prval () = fold@ lst
                val+ ~ NIL = dst
                val () = dst := lst
                val () = lst := tl
              in
                m_dst := 1
              end
(*
          end
*)
      in
        if head_lt_pivot then
          begin
            append_to_destination (lst, lst_low, m_low);
            m_high := 0
          end
        else
          begin
            append_to_destination (lst, lst_high, m_high);
            m_low := 0
          end
      end

(*
    fun (* FIXME: Add currently-active-list info to reduce the amount of writing. *)
    loop {m : nat}
         .<m>.
         (lst      : &list_vt (a, m) >> list_vt (a, 0),
          m        : int m,
          lst_low  : &list_vt (a, 0)? >> list_vt (a, m_low),
          lst_high : &list_vt (a, 0)? >> list_vt (a, m - m_low))
        :<!wrt> #[m_low : nat | m_low <= m]
                int m_low =
      let
        val @ (head :: tail) = lst
      in
        if is_lt_pivot<a> (head, p2_pivot) then
          let
            val tl = tail
            prval () = fold@ lst
            val () = lst_low := lst
            val () = lst_high := NIL
            val () = lst := tl
*)
  in
    if head_is_lt_pivot<a> (lst, p2_pivot) then
      let
        val () = lst_low := lst
        val () = lst_high := NIL
        val n_lo = n
      in
        n_low := n_lo;
        n_high := n - n_lo
      end
    else
      let
        val () = lst_low := NIL
        val () = lst_high := lst
        val n_lo = 0
      in
        n_low := n_lo;
        n_high := n - n_lo
      end
  end

//    list_vt_getref_at<a> (lst, i_pivot)
(*
fn {a : vt@ype}
select_pivot
          {n          : pos}
          (lst        : list_vt (a, n),
           n          : int n,
           lst_before : &list_vt (a, 0)? >> list_vt (a, n_before),
           lst_pivot  : &list_vt (a, 0)? >> list_vt (a, 1),
           lst_after  : &list_vt (a, 0)? >> list_vt (a, n_after),
           n_before   : &int? >> int n_before,
           n_after    : &int? >> int n_after)
    :<!wrt> #[n_before, n_after : int | n_before + 1 + n_after == n]
            void =
  let
    val u64_n : uint64 n = g1i2u n
    val u64_rand : [i : nat] uint64 i = g1ofg0 (random_uint64 ())
    val u64_pivot = g1uint_mod (u64_rand, u64_n)
    val i_pivot : [i : nat | i < n] int i = g1u2i u64_pivot

    val @(left, right) = list_vt_split_at<a> (lst, i_pivot)
    val @(pivot, right) = list_vt_split_at<a> (right, 1)
  in
    lst_before := left;
    lst_pivot := pivot;
    lst_after := right;
    n_before := i_pivot;
    n_after := pred (n - i_pivot)
  end

fn {a : vt@ype}
head_is_lt_pivot
          {n         : pos}
          (lst       : &list_vt (a, n),
           lst_pivot : &list_vt (a, 1))
    :<> bool =
  let
    val+ @ (head :: _) = lst
    val+ @ (pivot :: _) = lst_pivot
    val is_lt = list_vt_stable_quicksort$lt<a> (head, pivot)
    prval () = fold@ lst_pivot
    prval () = fold@ lst
  in
    is_lt
  end

(*
fn {a : vt@ype}
scan_run_of_lt_pivot
          {n         : pos}
          (lst       : &list_vt (a, n) >> list_vt (a, m),
           n         : int n,
           m         : &int? >> int m,
           lst_pivot : &list_vt (a, 1))
    :<!wrt> #[m : pos | m <= n] void =
  (* Scan to the last node of the run, but not past it. The first node
     is assumed to be less than the pivot. *)
  let
    fun
    loop {i : pos | i <= n}
         .<i>.
         (lst       : &list_vt (a, i) >> list_vt (a, m),
          i         : int i,
          lst_pivot : &list_vt (a, 1))
        :<!wrt> #[m : pos | m <= i] int m =
      let
        val+ @ (first :: rest) = lst
      in
        case+ rest of
        | NIL =>
          let
            prval () = fold@ lst
          in
            i
          end
        | @ (head :: _) =>
          if ~is_lt_pivot<a> (head, lst_pivot) then
            let
              prval () = fold@ rest
              prval () = fold@ lst
            in
              i
            end
          else
            let
              prval () = fold@ rest
//              val rest1 = rest
//              val () = lst := rest
              prval () = fold@ lst
//              val i1 = loop (lst, pred i, lst_pivot)
val i1 = i
            in
              i1
            end
      end
  in
    m := loop (lst, n, lst_pivot)
  end
*)

(*
fn {a : vt@ype}
apply_pivot_to_list
          {n        : int}
          (lst      : list_vt (a, n),
           n        : int n,
           lst_low  : &list_vt (a, 0)? >> list_vt (a, n_low),
           lst_high : &list_vt (a, 0)? >> list_vt (a, n_high),
           n_low    : &int? >> int n_low,
           n_high   : &int? >> int n_high)
    :<!wrt> #[n_low, n_high : int | n_low + n_high == n]
            void =
  let
  in
    // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME
    lst_low := lst;
    lst_high := NIL;
    n_low := n;
    n_high := 0
  end
*)

fn {a : vt@ype}
apply_pivot
          {n_before, n_after : int}
          (lst_before : list_vt (a, n_before),
           lst_pivot  : list_vt (a, 1),
           lst_after  : list_vt (a, n_after),
           n_before   : int n_before,
           n_after    : int n_after,
           lst_low    : &list_vt (a, 0)? >> list_vt (a, n_low),
           lst_high   : &list_vt (a, 0)? >> list_vt (a, n_high),
           n_low      : &int? >> int n_low,
           n_high     : &int? >> int n_high)
    :<!wrt> #[n_low, n_high : int |
              n_low + n_high == n_before + 1 + n_after]
            void =
  let
    fun
    partition {n_before, n_after : nat}
              .<n_before>.
              (lst_before : list_vt (a, n_before),
               lst_pivot  : list_vt (a, 1),
               lst_after  : list_vt (a, n_after),
               n_before   : int n_before,
               n_after    : int n_after,
               lst_low    : &list_vt (a, 0)? >> list_vt (a, n_low),
               lst_high   : &list_vt (a, 0)? >> list_vt (a, n_high),
               n_low      : &int? >> int n_low,
               n_high     : &int? >> int n_high)
        :<!wrt> #[n_low, n_high : int |
                  n_low + n_high == n_before + 1 + n_after]
                void =
      case+ lst_before of
      | ~ NIL =>
        let
        in
        end
      let
      in
        // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME
        lst_low := lst_before;
        lst_high := list_vt_append (lst_pivot, lst_after);
        n_low := n_before;
        n_high := succ n_after
      end

    prval () = lemma_list_vt_param lst_before
    prval () = lemma_list_vt_param lst_after
  in
    partition (lst_before, lst_pivot, lst_after,
               n_before, n_after, lst_low, lst_high,
               n_low, n_high)
(*
    // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME
    lst_low := lst_before;
    lst_high := list_vt_append (lst_pivot, lst_after);
    n_low := n_before;
    n_high := succ n_after
*)
  end
*)

(*------------------------------------------------------------------*)
