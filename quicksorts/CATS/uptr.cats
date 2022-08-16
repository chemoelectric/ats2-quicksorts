/*
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
*/

#ifndef QUICKSORTS__CATS__UPTR_CATS__HEADER_GUARD__
#define QUICKSORTS__CATS__UPTR_CATS__HEADER_GUARD__

#include <stdint.h>
#include <inttypes.h>

#define ats2_quicksorts_uptr_inline ATSinline ()

#if defined __GNUC__
#define ats2_quicksorts_uptr_memmove __builtin_memmove
#else
#define ats2_quicksorts_uptr_memmove memmove
#endif

ats2_quicksorts_uptr_inline atstype_uintptr
ats2_quicksorts_uptr_ptr2uptr_anchor__ (atstype_ptr p)
{
  return (uintptr_t) p;
}

ats2_quicksorts_uptr_inline atstype_ptr
ats2_quicksorts_uptr_uptr_anchor2ptr (atstype_uintptr up)
{
  return (void *) up;
}

ats2_quicksorts_uptr_inline atstype_ptr
ats2_quicksorts_uptr_uptr2ptr__ (atstype_uintptr anchor,
                                 atstype_uintptr up)
{
  return (void *) ((char *) (void *) anchor + (up - anchor));
}

ats2_quicksorts_uptr_inline atstype_uintptr
ats2_quicksorts_uptr_uptr_add_size__ (atstype_uintptr up,
                                      atstype_size j,
                                      atstype_size elemsz)
{
  return (uintptr_t) (up + (j * elemsz));
}

ats2_quicksorts_uptr_inline atstype_uintptr
ats2_quicksorts_uptr_uptr_add_ssize__ (atstype_uintptr up,
                                       atstype_ssize j,
                                       atstype_size elemsz)
{
  return (uintptr_t) (up + (j * elemsz));
}

ats2_quicksorts_uptr_inline atstype_uintptr
ats2_quicksorts_uptr_uptr_sub_size__ (atstype_uintptr up,
                                      atstype_size j,
                                      atstype_size elemsz)
{
  return (uintptr_t) (up - (j * elemsz));
}

ats2_quicksorts_uptr_inline atstype_uintptr
ats2_quicksorts_uptr_uptr_sub_ssize__ (atstype_uintptr up,
                                       atstype_ssize j,
                                       atstype_size elemsz)
{
  return (uintptr_t) (up - (j * elemsz));
}

ats2_quicksorts_uptr_inline atstype_uintptr
ats2_quicksorts_uptr_uptr_succ__ (atstype_uintptr up,
                                  atstype_size elemsz)
{
  return (uintptr_t) (up + elemsz);
}

ats2_quicksorts_uptr_inline atstype_uintptr
ats2_quicksorts_uptr_uptr_pred__ (atstype_uintptr up,
                                  atstype_size elemsz)
{
  return (uintptr_t) (up - elemsz);
}

ats2_quicksorts_uptr_inline atstype_ssize
ats2_quicksorts_uptr_uptr_diff__ (atstype_uintptr up,
                                  atstype_uintptr uq,
                                  atstype_size elemsz)
{
  return (up - uq) / elemsz;
}

ats2_quicksorts_uptr_inline atstype_size
ats2_quicksorts_uptr_uptr_diff_unsigned__ (atstype_uintptr up,
                                           atstype_uintptr uq,
                                           atstype_size elemsz)
{
  return ((size_t) (up - uq)) / elemsz;
}

ats2_quicksorts_uptr_inline atstype_bool
ats2_quicksorts_uptr_lt_uptr_uptr (atstype_uintptr up,
                                   atstype_uintptr uq)
{
  return (up < uq);
}

ats2_quicksorts_uptr_inline atstype_bool
ats2_quicksorts_uptr_lte_uptr_uptr (atstype_uintptr up,
                                    atstype_uintptr uq)
{
  return (up <= uq);
}

ats2_quicksorts_uptr_inline atstype_bool
ats2_quicksorts_uptr_gt_uptr_uptr (atstype_uintptr up,
                                   atstype_uintptr uq)
{
  return (up > uq);
}

ats2_quicksorts_uptr_inline atstype_bool
ats2_quicksorts_uptr_gte_uptr_uptr (atstype_uintptr up,
                                    atstype_uintptr uq)
{
  return (up >= uq);
}

ats2_quicksorts_uptr_inline atstype_bool
ats2_quicksorts_uptr_eq_uptr_uptr (atstype_uintptr up,
                                   atstype_uintptr uq)
{
  return (up == uq);
}

ats2_quicksorts_uptr_inline atstype_bool
ats2_quicksorts_uptr_neq_uptr_uptr (atstype_uintptr up,
                                    atstype_uintptr uq)
{
  return (up != uq);
}

ats2_quicksorts_uptr_inline atstype_int
ats2_quicksorts_uptr_compare_uptr_uptr (atstype_uintptr up,
                                        atstype_uintptr uq)
{
  return ((up < uq) ? (-1) : ((up > uq) ? 1 : 0));
}

#endif /* QUICKSORTS__CATS__UPTR_CATS__HEADER_GUARD__ */
