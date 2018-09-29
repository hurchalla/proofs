// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

// This file is a trimmed copy of extended_euclidean__a_ge_0__b_gt_a.h.
// It contains only the essential assertion results, without any of the proofs.

#ifndef ESSENTIAL_ASSERTS__A_GE_0__B_GT_A
#define ESSENTIAL_ASSERTS__A_GE_0__B_GT_A  1

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
void essential_asserts__a_ge_0__b_gt_a(T a, T b, T* pGcd, T* pX, T* pY)
{
   static_assert(std::numeric_limits<T>::is_integer, "");
   static_assert(std::numeric_limits<T>::is_signed, "");
   assert_precondition(b > a);
   assert_precondition(a >= 0);
      assert(gcd(a,b) >= 1);
   T x0 = 1, y0 = 0, a0 = a;
   T x1 = 0, y1 = 1, a1 = b;

   // The peeled-out first iteration:
   {
      T q = a0/a1;
         assert(q == 0);
      T a2 = a0 - q*a1;
         assert(q*a1 == 0);
         assert(0 <= a2 && a2 < a1);
         assert(q <= a0/2);
      T x2 = x0 - q*x1;
         assert(abs(q*x1) <= abs(x2));
         assert(abs(x1) <= abs(x2));
      T y2 = y0 - q*y1;
         assert(abs(q*y1) <= abs(y2));
         assert(y1 == 1);
      x0=x1; y0=y1; a0=a1;
      x1=x2; y1=y2; a1=a2;
   }
   while (a1 != 0) {
      T q = a0/a1;
         assert(1 <= q && q <= a0);
      T a2 = a0 - q*a1;
         assert(0 < (q*a1) && (q*a1) <= a0);
         assert(0 <= a2 && a2 < a1);
         if (a2 != 0) assert(q <= a0/2);
      T x2 = x0 - q*x1;
         assert(abs(q*x1) <= abs(x2));
         assert(abs(x1) <= abs(x2));
      T y2 = y0 - q*y1;
         assert(abs(q*y1) <= abs(y2));
         assert(abs(y1) <= abs(y2));
      x0=x1; y0=y1; a0=a1;
      x1=x2; y1=y2; a1=a2;
   }
      assert(abs(x1) == b/gcd(a,b));
      assert(abs(y1) == a/gcd(a,b));
      assert(abs(x0) <= (b/gcd(a,b))/2);
      assert(y0 == 1 || abs(y0) <= (a/gcd(a,b))/2);
      assert(a0 == gcd(a,b));
      assert(a*x0 + b*y0 == gcd(a,b));
   *pX = x0;
   *pY = y0;
   *pGcd = a0;
}

#undef assert_precondition

#endif
