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

#ifndef QUICKSORTS__CATS__QUICKSORTS_CATS__HEADER_GUARD__
#define QUICKSORTS__CATS__QUICKSORTS_CATS__HEADER_GUARD__

#include <inttypes.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <string.h>

#define ats2_quicksorts_inline ATSinline ()

#if defined __GNUC__
#define ats2_quicksorts_bswap64 __builtin_bswap64
#else
#define ats2_quicksorts_bswap64(x)                  \
  ((((x) & UINT64_C (0x00000000000000FF)) << 56) |  \
   (((x) & UINT64_C (0x000000000000FF00)) << 40) |  \
   (((x) & UINT64_C (0x0000000000FF0000)) << 24) |  \
   (((x) & UINT64_C (0x00000000FF000000)) << 8) |   \
   (((x) & UINT64_C (0x000000FF00000000)) >> 8) |   \
   (((x) & UINT64_C (0x0000FF0000000000)) >> 24) |  \
   (((x) & UINT64_C (0x00FF000000000000)) >> 40) |  \
   (((x) & UINT64_C (0xFF00000000000000)) >> 56))
#endif

#if defined __GNUC__
#define ats2_quicksorts_memcpy __builtin_memcpy
#define ats2_quicksorts_memmove __builtin_memmove
#else
#define ats2_quicksorts_memcpy memcpy
#define ats2_quicksorts_memmove memmove
#endif

ats2_quicksorts_inline void
ats2_quicksorts_copy_bytes (atstype_ptr p_dst,
                            atstype_ptr p_src,
                            atstype_size n)
{
  (void) ats2_quicksorts_memcpy (p_dst, p_src, n);
}

ats2_quicksorts_inline void
ats2_quicksorts_move_bytes_right (atstype_ptr p,
                                  atstype_size n, 
                                  atstype_size k)
{
  (void) ats2_quicksorts_memmove (((atstype_byte *) p) + k,
                                  p, n);
}

ats2_quicksorts_inline atstype_uint64
ats2_quicksorts_g1uint_mod_uint64 (atstype_uint64 x,
                                   atstype_uint64 y)
{
  return (x % y);
}

/*------------------------------------------------------------------*/
/* Spinlocks for random number generator seeds.                     */

typedef struct
{
  /* Use unsigned integers, so they will wrap around when they
     overflow. */
  atomic_size_t active;
  atomic_size_t available;
} ats2_quicksorts_spinlock_t;

ats2_quicksorts_inline void
ats2_quicksorts_obtain_spinlock
  (ats2_quicksorts_spinlock_t *lock)
{
  size_t my_ticket =
    atomic_fetch_add_explicit (&lock->available, 1,
                               memory_order_seq_cst);
  bool done = false;
  while (!done)
    {
      size_t active_ticket =
        atomic_load_explicit (&lock->active, memory_order_seq_cst);
      done = (my_ticket == active_ticket);
      /* if (!done)                        */
      /*   optionally_put_a_pause_here (); */
    }
  atomic_thread_fence (memory_order_seq_cst);
}

ats2_quicksorts_inline void
ats2_quicksorts_release_spinlock
  (ats2_quicksorts_spinlock_t *lock)
{
  atomic_thread_fence (memory_order_seq_cst);
  (void) atomic_fetch_add_explicit (&lock->active, 1,
                                    memory_order_seq_cst);
}

/*------------------------------------------------------------------*/
/* A simple linear congruential generator, for pivot selection.     */

/* The multiplier LCG_A comes from Steele, Guy; Vigna, Sebastiano (28
   September 2021). "Computationally easy, spectrally good multipliers
   for congruential pseudorandom number generators".
   arXiv:2001.05304v3 [cs.DS] */
#define ats2_quicksorts_LCG_A (UINT64_C (0xf1357aea2e62a9c5))

/* LCG_C must be odd. (The value 1 may get optimized to an increment
   instruction.) */
#define ats2_quicksorts_LCG_C (UINT64_C (1))

extern ats2_quicksorts_spinlock_t ats2_quicksorts_seed_lock;
extern uint64_t ats2_quicksorts_seed;

ats2_quicksorts_inline atstype_uint64
ats2_quicksorts_random_uint64 (void)
{
  ats2_quicksorts_obtain_spinlock (&ats2_quicksorts_seed_lock);

  uint64_t old_seed = ats2_quicksorts_seed;

  /* The following operation is modulo 2**64, by virtue of standard C
     behavior for uint64_t. */
  ats2_quicksorts_seed =
    (ats2_quicksorts_LCG_A * old_seed) + ats2_quicksorts_LCG_C;

  ats2_quicksorts_release_spinlock (&ats2_quicksorts_seed_lock);

  /* Reverse the bytes, because least significant bits of LCG output
     tend to be bad. Indeed, the very least significant bit literally
     switches back and forth between 0 and 1. */
  return ats2_quicksorts_bswap64 (old_seed);
}

/*------------------------------------------------------------------*/

#endif /* QUICKSORTS__CATS__QUICKSORTS_CATS__HEADER_GUARD__ */
