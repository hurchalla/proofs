// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef EXTENDED_EUCLIDEAN_PROOF
#define EXTENDED_EUCLIDEAN_PROOF 1

#include <assert.h>
#include <limits>
#include "bounds_only_collins.h"
#include "bounds_only_extended_euclidean_complete.h"
#include "extended_euclidean_collins.h"
#include "helpers\bounds_only__a_ge_0__b_gt_a.h"
#include "helpers\bounds_only__a_ge_0__b_gt_a__simplified.h"
#include "helpers\bounds_only__b_eq_0__b_eq_a.h"
#include "helpers\bounds_only__b_gt_0__b_eq_a.h"
#include "helpers\extended_euclidean__a_ge_0__b_gt_a.h"
#include "helpers\extended_euclidean__b_eq_0__b_eq_a.h"
#include "helpers\extended_euclidean__b_gt_0__b_eq_a.h"


template <typename T>
void extended_euclidean_proof(T a, T b, T* pGcd, T* pX, T* pY)
{
	static_assert(std::numeric_limits<T>::is_integer, "");
	static_assert(std::numeric_limits<T>::is_signed, "");
    assert(a >= 0);
    assert(b >= 0);

    // function that asserts bounds for any case where a>=0 and b>=0
    bounds_only_extended_euclidean_complete(a, b, pGcd, pX, pY);

    if (b < a) {
        // full proof for the case 0 <= b < a
        extended_euclidean_collins(a, b, pGcd, pX, pY);
        // pruned version of the above with only bounds assertions.
        bounds_only_collins(a, b, pGcd, pX, pY);
    }
    else if (b == a) {
        if (b > 0) {
            // full proof for the case 0 < b == a
            extended_euclidean__b_gt_0__b_eq_a(a, b, pGcd, pX, pY);
            // pruned version of the above with only bounds assertions.
            bounds_only__b_gt_0__b_eq_a(a, b, pGcd, pX, pY);
        }
        else {
            // full proof for the case 0 == b == a
            extended_euclidean__b_eq_0__b_eq_a(a, b, pGcd, pX, pY);
            // pruned version of the above with only bounds assertions.
            bounds_only__b_eq_0__b_eq_a(a, b, pGcd, pX, pY);
        }
    }
    else {  // b > a
        // full proof for the case 0 <= a < b
        extended_euclidean__a_ge_0__b_gt_a(a, b, pGcd, pX, pY);
        // pruned version of the above with only bounds assertions.
        bounds_only__a_ge_0__b_gt_a(a, b, pGcd, pX, pY);
        // simplified version of the bounds only function above.
        bounds_only__a_ge_0__b_gt_a__simplified(a, b, pGcd, pX, pY);
    }
}

#endif
