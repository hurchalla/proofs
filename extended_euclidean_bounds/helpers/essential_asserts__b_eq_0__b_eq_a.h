// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

// This file is a trimmed copy of extended_euclidean__b_eq_0__b_eq_a.h.
// It contains only the essential assertion results, without any of the proofs.

#ifndef ESSENTIAL_ASSERTS__B_EQ_0__B_EQ_A
#define ESSENTIAL_ASSERTS__B_EQ_0__B_EQ_A  1

#ifndef NDEBUG
#  include "assert_helper_gcd.h"
#endif
#include <assert.h>
#include <limits>

#if defined(assert_precondition)
#  error "assert_precondition was already defined"
#endif
// assert aliases will help self-document the code
#define assert_precondition  assert


template <typename T>
void essential_asserts__b_eq_0__b_eq_a(T a, T b, T* pGcd, T* pX, T* pY)
{
   static_assert(std::numeric_limits<T>::is_integer, "");
   static_assert(std::numeric_limits<T>::is_signed, "");
   assert_precondition(b == a);
   assert_precondition(b == 0);
      assert(gcd(a,b) == 0);
   T x0 = 1, y0 = 0, a0 = a;
   T x1 = 0, y1 = 1, a1 = b;

      assert(a1 == 0);
   while (a1 != 0) {
      // The loop will never be taken, so the loop content is not shown.
   }
      assert(x1 == 0);
      assert(y1 == 1);
      assert(x0 == 1);
      assert(y0 == 0);
      assert(a0 == gcd(a,b));
      assert(a*x0 + b*y0 == gcd(a,b));
   *pX = x0;
   *pY = y0;
   *pGcd = a0;
}

#undef assert_precondition

#endif
