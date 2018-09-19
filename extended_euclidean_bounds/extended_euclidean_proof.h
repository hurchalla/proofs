// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef EXTENDED_EUCLIDEAN_PROOF
#define EXTENDED_EUCLIDEAN_PROOF 1

#include <assert.h>
#include "extended_euclidean_collins.h"
#include "helpers\extended_euclidean__b_gt_0__b_eq_a.h"
#include "helpers\extended_euclidean__b_eq_0__b_eq_a.h"
#include "helpers\extended_euclidean__a_ge_0__b_gt_a.h"


template <typename T>
void extended_euclidean_proof(T a, T b, T* pGcd, T* pX, T* pY)
{
    assert(a >= 0);
    assert(b >= 0);

    if (b < a) {
            extended_euclidean_collins(a, b, pGcd, pX, pY);
            // extended_euclidean_collins is  extended_euclidean__b_ge_0__b_lt_a
    }
    else if (b == a) {
        if (b > 0)
            extended_euclidean__b_gt_0__b_eq_a(a, b, pGcd, pX, pY);
        else    // a == b == 0
            extended_euclidean__b_eq_0__b_eq_a(a, b, pGcd, pX, pY);
    }
    else {  // b > a
        extended_euclidean__a_ge_0__b_gt_a(a, b, pGcd, pX, pY);
    }
}

#endif
