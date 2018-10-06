// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

// This file redirects any call to the appropriate part of the full proof
// (the extended_euclidean header files), and also runs the essential_assert
// functions that were derived from each proof part.

#ifndef EXTENDED_EUCLIDEAN_PROOF
#define EXTENDED_EUCLIDEAN_PROOF 1

#include <assert.h>
#include <limits>

#include "extended_euclidean_collins.h"
#include "helpers/extended_euclidean__a_ge_0__b_gt_a.h"
#include "helpers/extended_euclidean__b_eq_0__b_eq_a.h"
#include "helpers/extended_euclidean__b_gt_0__b_eq_a.h"

#include "essential_asserts_collins.h"
#include "helpers/essential_asserts__a_ge_0__b_gt_a.h"
#include "helpers/essential_asserts__a_ge_0__b_gt_a__improved.h"
#include "helpers/essential_asserts__b_eq_0__b_eq_a.h"
#include "helpers/essential_asserts__b_gt_0__b_eq_a.h"

#include "essential_asserts_combined.h"

#include "final_bounds/improved_bounds.h"
#include "final_bounds/essential_asserts_improved.h"
#include "final_bounds/final_bounds.h"
#include "final_bounds/essential_asserts_final.h"


template <typename T>
void extended_euclidean_proof(T a, T b, T* pGcd, T* pX, T* pY)
{
	static_assert(std::numeric_limits<T>::is_integer, "");
	static_assert(std::numeric_limits<T>::is_signed, "");
    assert(a >= 0);
    assert(b >= 0);

    // Function with the essential asserts covering all cases of the
    // Extended Euclidean algorithm (with preconditions a>=0 and b>=0).
    essential_asserts_combined(a, b, pGcd, pX, pY);

    // A version of essential_asserts_combined() with improved bounds.
    improved_bounds(a, b, pGcd, pX, pY);
    // A version of improved_bounds() with only the essential assertions.
    essential_asserts_improved(a, b, pGcd, pX, pY);
    // A version of essential_asserts_improved() that achieves the goal of
    // providing the final desired bounds (in terms of inputs a and b).
    final_bounds(a, b, pGcd, pX, pY);
    // A version of final_bounds() with only the essential assertions.
    essential_asserts_final(a, b, pGcd, pX, pY);

    if (b < a) {
        // full proof for the case 0 <= b < a
        extended_euclidean_collins(a, b, pGcd, pX, pY);
        // pruned version of the above with only essential assertions.
        essential_asserts_collins(a, b, pGcd, pX, pY);
    }
    else if (b == a) {
        if (b > 0) {
            // full proof for the case 0 < b == a
            extended_euclidean__b_gt_0__b_eq_a(a, b, pGcd, pX, pY);
            // pruned version of the above with only essential assertions.
            essential_asserts__b_gt_0__b_eq_a(a, b, pGcd, pX, pY);
        }
        else {
            // full proof for the case 0 == b == a
            extended_euclidean__b_eq_0__b_eq_a(a, b, pGcd, pX, pY);
            // pruned version of the above with only essential assertions.
            essential_asserts__b_eq_0__b_eq_a(a, b, pGcd, pX, pY);
        }
    }
    else {  // b > a
        // full proof for the case 0 <= a < b
        extended_euclidean__a_ge_0__b_gt_a(a, b, pGcd, pX, pY);
        // pruned version of the above with only essential assertions.
        essential_asserts__a_ge_0__b_gt_a(a, b, pGcd, pX, pY);
        // simplified version of the function above.
        essential_asserts__a_ge_0__b_gt_a__improved(a, b, pGcd, pX, pY);
    }
}

#endif
