// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---


// For Definitions and Theorems P1, P2, P3, P4, P5, P6, see
// extended_euclidean_collins.h


#ifndef EXTENDED_EUCLIDEAN__A_GE_0__B_GT_A
#define EXTENDED_EUCLIDEAN__A_GE_0__B_GT_A  1

#ifndef NDEBUG
#  include "assert_helper_gcd.h"
#endif
#include <assert.h>
#include <limits>

#if defined(assert_invariant) || defined(assert_precondition)
#  error "assert_invariant and/or assert_precondition were already defined"
#endif
// assert aliases will help self-document the code
#define assert_invariant     assert
#define assert_precondition  assert


template <typename T>
void extended_euclidean__a_ge_0__b_gt_a(T a, T b, T* pGcd, T* pX, T* pY)
{
        static_assert(std::numeric_limits<T>::is_integer, "");
	    static_assert(std::numeric_limits<T>::is_signed, "");
/*01*/     assert_precondition(b > a);
/*02*/     assert_precondition(a >= 0);
/*03*/  T x0 = 1;
/*04*/  T y0 = 0;
/*05*/  T a0 = a;
/*06*/  T x1 = 0;
/*07*/  T y1 = 1;
/*08*/  T a1 = b;

/*09*/     assert(b > 0);                      // By [01, 02]

        // This loop would be taken at least once, since by [08, 09] a1 > 0.
        // So we will peel out the first iteration from the loop, and place it
        // prior to the start of the loop.
//      while (a1 != 0) {
//         T q = a0/a1;
//         T a2 = a0 - q*a1;
//         T x2 = x0 - q*x1;
//         T y2 = y0 - q*y1;
//
//         x0 = x1;
//         y0 = y1;
//         a0 = a1;
//         x1 = x2;
//         y1 = y2;
//         a1 = a2;
//      }

        // The peeled-out first iteration:
        {
/*10*/     T q = a0/a1;
/*11*/        assert(q == 0);
              // Proof: By [01, 02] b > a >= 0.  By [08,05] a1 == b and a0 == a,
              // thus a1 > a0 >= 0.  By [10] q == a0/a1, thus q == 0.
              // Note: We do NOT have (1 <= q && q <= a0), since by [11] q == 0.
/*12*/     T a2 = a0 - q*a1;
/*H0*/        assert(q <= a0/2);
              // Proof: By [11, 02, 05] q == 0 == 0/2 <= a/2 == a0/2
/*13*/        assert(q*a1 == 0);               // By [11]
              // Note: We do NOT have (0 < (q*a1) && (q*a1) <= a0), since by
              // [13] 0 == q*a1.
/*14*/        assert(a2 == a);
              // Proof: By [05, 13] a0 == a  and  q*a1 == 0.  By [12],
              // a2 == a0 - q*a1,  so  a2 == a - 0 == a.
/*15*/        assert(0 <= a2 && a2 < a1);
              // By [14, 02] a2 == a >= 0,  so  0 <= a2.  By [08, 01, 14],
              // a1 == b > a == a2,  so  a2 < a1.
/*16*/     T x2 = x0 - q*x1;
/*17*/        assert(x2 == 1);
              // Proof: By [03, 11] x0 == 1  and  q == 0.  By [16],
              // x2 == x0 - q*x1 == 1 - 0*x1 == 1.
/*18*/        assert(abs(q*x1) <= abs(x2));
              // Proof: By [11, 17] q == 0  and  x2 == 1, so
              // abs(q*x1) == abs(0*x1) == 0 <= 1 == abs(x2).
/*19*/        assert(abs(x1) <= abs(x2));
              // Proof: By [06, 17] abs(x1) == 0 <= 1 == abs(x2).
/*20*/     T y2 = y0 - q*y1;
/*21*/        assert(y2 == 0);
              // Proof: By [04, 11] y0 == 0  and  q == 0.  By [20],
              // y2 == y0 - q*y1 == 0 - 0*y1 == 0.
/*22*/        assert(abs(q*y1) <= abs(y2));
              // Proof: By [11, 21] q == 0  and  y2 == 0, so
              // abs(q*y1) == abs(0*y1) == 0 <= 0 == abs(y2).
              // Note: We do NOT have (abs(y1) <= abs(y2)), since by [07, 21],
              // abs(y1) == 1 > 0 == abs(y2).
/*H1*/        assert(y1 == 1);                 // By [07]

/*23*/     x0 = x1;
/*24*/     y0 = y1;
/*25*/     a0 = a1;
/*26*/        assert(x0 == 0);                 // By [23, 06] x0 == x1 == 0.
/*27*/        assert(y0 == 1);                 // By [24, 07] y0 == y1 == 1.
/*28*/        assert(a0 == b);                 // By [25, 08] a0 == a1 == b.
/*29*/     x1 = x2;
/*30*/     y1 = y2;
/*31*/     a1 = a2;
/*32*/        assert(x1 == 1);                 // By [29, 17] x1 == x2 == 1.
/*33*/        assert(y1 == 0);                 // By [30, 21] y1 == y2 == 0.
/*34*/        assert(a1 == a);                 // By [31, 14] a1 == a2 == a.

/*35*/     assert(a >= 0);                     // By [02]
/*36*/     assert(a < b);                      // By [01]
        }

        // Informally, we can note that we now have the same program state that
        // exists at the start of the extended_euclidean_collins() routine, with
        // the difference that inputs a and b are swapped, and the x recurrence
        // and y recurrence are swapped.
        // It seems possible that the rest of this proof might formally
        // reference this relationship, resulting in perhaps a short proof.
        // But instead, in order to quickly prove the results, I simply will
        // replicate the basic logic from the extended_euclidean_collins proof.
        // Unfortunately this means the proof will be similarly long.


/*37*/     assert_invariant(b > 0);            // By [36, 35]
/*38*/     assert_invariant(gcd(a,b) >= 1);
           // Proof: By [37] b > 0, so gcd(a,b) != gcd(0,0).  Since 1 is a
           // common divisor of both a and b, gcd(a,b) >= 1

/*39*/     assert_invariant(a0 > 0);           // By [28, 37]
/*40*/     assert(a1 >= 0);                    // By [34, 35]
/*41*/     assert_invariant(a1 < a0);          // By [34, 28, 36]
/*42*/     assert_invariant(a*x0 + b*y0 == a0);// Proof: By [26, 27, 28],
                                               // a*x0+b*y0 == a*0+b*1 == b== a0
/*43*/     assert_invariant(a*x1 + b*y1 == a1);// Proof: By [32, 33, 34],
                                               // a*x1+b*y1 == a*1+b*0 == a== a1
/*44*/     assert_invariant(gcd(a0,a1) == gcd(a,b));  // By [28, 34]

/*45*/     assert_invariant(abs(y0*x1 - x0*y1) == 1); // Proof: By [27,32,26,33]
                                                      // abs(y0*x1 - x0*y1) ==
                                                      // abs(1*1 - 0*0) == 1
/*46*/     T s0 = 1;    // informally, s0 represents the sign of y0.
/*47*/     T s1 = -1;   // the sign of y1 (values <= 0 treated as negative)
/*48*/     assert_invariant(s1 == -s0);        // By [46, 47]
/*49*/     assert_invariant(abs(s0) == 1);     // By [46]
/*50*/     assert_invariant(s0*abs(y0) == y0); // By [27, 46], y0 == 1, s0 == 1.
                                               // s0*abs(y0) == 1*1 == 1 == y0
/*51*/     assert_invariant(s1*abs(y1) == y1); // By [33,47], y1 == 0, s1 == -1.
                                               // s1*abs(y1) == -1*0 == 0 == y1
/*52*/     assert_invariant(-s0*abs(x0) == x0);// By [26, 46], x0 == 0, s0 == 1.
                                               // -s0*abs(x0) == -1*0 == 0 == x0
/*53*/     assert_invariant(-s1*abs(x1) == x1);// By [32,47], x1 == 1, s1 == -1.
                                               // -s1*abs(x1) == 1*1 == 1 == x1

/*54*/     assert(abs(x1) >= 2*abs(x0));       // By [32, 26], x1 == 1, x0 == 0.
                                               // abs(x1) == 1 >= 0 == 2*abs(x0)
/*55*/     assert_invariant(gcd(x1,y1) == 1);  // By [32, 33], x1 == 1, y1 == 0.
                                               // gcd(x1,y1) == gcd(1,0) == 

        // The remaining iterations of the loop:
/*56*/  while (a1 != 0) {
/*57*/        assert_invariant(a0 > 0);                   // By [39, M8]
/*58*/        assert(a1 > 0);
              // Proof: By [40, M9] a1 >= 0, and by [56] a1 != 0, so  a1 > 0.
/*59*/        assert_invariant(a1 < a0);                  // By [41, N0]
/*60*/        assert_invariant(a*x0 + b*y0 == a0);        // By [42, N1]
/*61*/        assert_invariant(a*x1 + b*y1 == a1);        // By [43, N2]
/*62*/        assert_invariant(gcd(a0,a1) == gcd(a,b));   // By [44, N3]
/*63*/        assert_invariant(abs(y0*x1 - x0*y1) == 1);  // By [45, N4]
/*64*/        assert_invariant(s1 == -s0);                // By [48, N5]
/*65*/        assert_invariant(abs(s0) == 1);             // By [49, N6]
/*66*/        assert_invariant(s0*abs(y0) == y0);         // By [50, N7]
/*67*/        assert_invariant(s1*abs(y1) == y1);         // By [51, N8]
/*68*/        assert_invariant(-s0*abs(x0) == x0);        // By [52, N9]
/*69*/        assert_invariant(-s1*abs(x1) == x1);        // By [53, W0]
/*70*/        assert(abs(s1) == 1); // By [64,65] s1== -s0. abs(s1)==abs(s0)== 1
/*71*/     T q = a0/a1;
/*72*/        assert(1 <= q && q <= a0);
              // Proof:  By [71]  q == a0/a1  (note that a1 might not divide a0)
              // By [58, 59]  a1>0  and  a1<a0,  so  0 < a1 < a0,  and thus,
              // q == a0/a1 >= 1.
              // Since  0 < a1  implies  a1 >= 1,  we have  q == a0/a1 <= a0.
/*73*/     T a2 = a0 - q*a1;
              if (a2 != 0) {
/*74*/            assert(q <= a0 / 2);
                  // Proof : Assume a1 == 1.  Then by [71],  q == a0/a1 == a0.
                  // By [73],  a2 == a0 - q*a1, and since  q == a0,
                  // a2 == a0 - a0*a1.  Thus, given the assumption a1 == 1,
                  // a2 == a0 - a0*1 == 0.  But a2 == 0 is a contradiction, 
                  // because entering this clause requires  a2 != 0.  Therefore,
                  //    a1 != 1
                  // By [58]  a1 > 0,  and so, since a1 != 1,  a1 >= 2
                  // Since  q == a0/a1  and  a1 >= 2  and by [57] a0 > 0,
                  // q <= a0 / 2
              }
/*75*/        assert(0 < (q*a1) && (q*a1) <= a0);
              // Proof: By [72, 58],  q >= 1  and  a1 > 0,  so  q*a1 > 0.
              // By [71], q == a0/a1, and by [57, 58], a0 > 0 and a1 > 0.
              // Hence by [P3], q*a1 <= a0.
/*76*/        assert(0 <= a2 && a2 < a1);
              // Proof: By [57, 58], a0 > 0 and a1 > 0, and by [71] q == a0/a1,
              // so by [P1] q satisfies a0 == a1*q + r,  with 0 <= r < a1.
              // Thus, a0 - q*a1 == r.  By [73]  a0 - q*a1 == a2, so  a2 == r.
              // Since 0 <= r < a1, we know 0 <= a2 < a1
/*77*/        assert(gcd(a0,a1) == gcd(a1,a2));
              // Proof: By definition d = gcd(a0,a1) divides both a0 and a1.  So
              // since by [73]  a2 == a0 - q*a1,  d must also divide a2.  Thus d
              // is a common divisor of a1 and a2, and so d divides gcd(a1,a2).
              // Thus gcd(a0,a1) divides gcd(a1,a2).
              // Similarly, c = gcd(a1,a2) divides both a1 and a2, and since
              // by [73]  a0 == a2 + q*a1,  c must also divide a0.  Thus c is a
              // common divisor of a0 and a1, and so c divides gcd(a0,a1).  Thus
              // gcd(a1,a2) divides gcd(a0,a1).  Since both gcd(a0,a1) divides
              // gcd(a1,a2), and gcd(a1,a2) divides gcd(a0,a1), we know by [P5],
              //     gcd(a0,a1) == +- gcd(a1,a2).
              // Since gcds are never negative, gcd(a0,a1) == gcd(a1,a2).
/*78*/        assert(gcd(a1,a2) == gcd(a,b));
              // Proof: By [77] gcd(a0,a1) == gcd(a1,a2). And by [62]
              // gcd(a0,a1) == gcd(a,b). Therefore  gcd(a1,a2) == gcd(a,b).
/*79*/     T x2 = x0 - q*x1;
/*80*/        assert(x2 == -s0*(abs(x0) + abs(q*x1)));
              // Proof: By [68, 69],  x0 == -s0*abs(x0)  and  x1 == -s1*abs(x1).
              // By [79], x2 == x0 - q*x1,  so  x2 == -s0*abs(x0) + q*s1*abs(x1)
              // By [64], s1 == -s0,  so  x2 == -s0*abs(x0) - q*s0*abs(x1).
              // And thus  x2 == -s0*(abs(x0) + q*abs(x1)).  By [72], q >= 1, so
              // x2 == -s0*(abs(x0) + abs(q*x1))
/*81*/        assert(abs(x2) == abs(x0) + abs(q*x1));
              // Proof: By [80],  x2 == -s0*(abs(x0) + abs(q*x1)),  so
              // abs(x2) == abs(-s0)*abs(abs(x0) + abs(q*x1))
              // abs(x2) == abs(s0)*(abs(x0) + abs(q*x1)
              // Since by [65], abs(s0) == 1,  abs(x2) == abs(x0) + abs(q*x1).
/*82*/        assert(abs(q*x1) <= abs(x2));     // By [81]
/*83*/        assert(abs(x1) <= abs(x2));
              // Proof: By [72], q >= 1, so  abs(x1) <= abs(q*x1)
              // By [82], abs(q*x1) <= abs(x2), thus
              // abs(x1) <= abs(q*x1) <= abs(x2)
/*84*/     T y2 = y0 - q*y1;
/*85*/        assert(y2 == s0*(abs(y0) + abs(q*y1)));
              // Proof: By [66, 67],  y0 == s0*abs(y0)  and  y1 == s1*abs(y1).
              // By [84], y2 == y0 - q*y1,  so  y2 == s0*abs(y0) - q*s1*abs(y1)
              // By [64], s1 == -s0,  so  y2 == s0*abs(y0) + q*s0*abs(y1).
              // And thus  y2 == s0*(abs(y0) + q*abs(y1)).  By [72], q >= 1, so
              // y2 == s0*(abs(y0) + abs(q*y1))
/*86*/        assert(abs(y2) == abs(y0) + abs(q*y1));
              // Proof: By [85],  y2 == s0*(abs(y0) + abs(q*y1)),  so
              // abs(y2) == abs(s0)*abs(abs(y0) + abs(q*y1))
              // abs(y2) == abs(s0)*(abs(y0) + abs(q*y1))
              // Since by [65], abs(s0) == 1,  abs(y2) == abs(y0) + abs(q*y1).
/*87*/        assert(abs(q*y1) <= abs(y2));     // By [86]
/*88*/        assert(abs(y1) <= abs(y2));
              // Proof: By [72], q >= 1, so  abs(y1) <= abs(q*y1)
              // By [87], abs(q*y1) <= abs(y2), thus
              // abs(y1) <= abs(q*y1) <= abs(y2)

/*89*/        T s2 = -s1;
/*90*/        assert(s2 == s0);                // By [89, 64]
/*91*/        assert(-s2*abs(x2) == x2);
              // Proof: By [81], abs(x2) == (abs(x0) + abs(q*x1)).
              // By [80], x2 == -s0*(abs(x0) + abs(q*x1)), so  x2 == -s0*abs(x2).
              // By [90], s2 == s0,  thus  x2 == -s2*abs(x2).
/*92*/        assert(s2*abs(y2) == y2);
              // Proof: By [86], abs(y2) == (abs(y0) + abs(q*y1))
              // By [85], y2 == s0*(abs(y0) + abs(q*y1)),  so  y2 == s0*abs(y2)
              // By [90], s2 == s0,  thus  y2 == s2*abs(y2).
/*93*/        if (a2 == 0) {
/*94*/            assert(q >= 2);
                  // Proof: By [73], a2 == a0 - q*a1
                  // Hence by [93],  0 == a0 - q*a1  and  a0 == q*a1.
                  // If we assume  q==1, then since we just showed  a0 == q*a1,
                  // we would have  a0 == a1,  which contradicts [59]  a1 < a0.
                  // Therefore q!=1, and since by [72], q >= 1, we know  q >= 2.
/*95*/            assert(abs(x2) >= 2*abs(x1));
                  // Proof: By [82], abs(x2) >= abs(q*x1). Since by [94] q >= 2,
                  // abs(x2) >= q*abs(x1) >= 2*abs(x1).
/*96*/            assert(abs(y2) >= 2*abs(y1));
                  // Proof: By [87], abs(y2) >= abs(q*y1). Since by [94] q >= 2,
                  // abs(y2) >= q*abs(y1) >= 2*abs(y1).
              }
/*97*/        assert((y1*x2 - x1*y2) == -(y0*x1 - x0*y1));
              // Proof: Let  D0 = y0*x1 - x0*y1  and let  D1 = y1*x2 - x1*y2.
              // By [79, 84],
              //    D1 == y1*(x0 - q*x1) - x1*(y0 - q*y1)
              //    D1 == y1*x0 - x1*q*y1 - x1*y0 + x1*q*y1
              //    D1 == y1*x0 - x1*y0
              //    D1 == -D0
/*98*/        assert(abs(y1*x2 - x1*y2) == 1);
              // Proof: By [63],  abs(y0*x1 - x0*y1) == 1
              // By [97],  (y1*x2 - x1*y2) == -(y0*x1 - x0*y1)
              // Thus,  abs(y1*x2 - x1*y2) == abs(y0*x1 - x0*y1) == 1
/*99*/        assert(a*x2 + b*y2 == a2);
              // Proof: By [73],  a2 == a0 - q*a1
              // and thus by [60, 61],
              //    a2 == a*x0 + b*y0 - q*(a*x1 + b*y1)
              //    a2 == a*x0 - q*a*x1 + b*y0 - q*b*y1
              //    a2 == a*(x0 - q*x1) + b*(y0 - q*y1)
              // and by [79, 84],
              //    a2 == a*x2 + b*y2

/*M0*/     x0 = x1;
/*M1*/     y0 = y1;
/*M2*/     a0 = a1;
/*M3*/     x1 = x2;
/*M4*/     y1 = y2;
/*M5*/     a1 = a2;
/*M6*/        s0 = s1;
/*M7*/        s1 = s2;
              // trivially, we know at this point
/*M8*/        assert_invariant(a0 > 0);               // By [58, M2]
/*M9*/        assert(a1 >= 0);                        // By [76, M5]
/*N0*/        assert_invariant(a1 < a0);              // By [76, M2, M5]
/*N1*/        assert_invariant(a*x0 + b*y0 == a0);    // By [61, M0, M1, M2]
/*N2*/        assert_invariant(a*x1 + b*y1 == a1);    // By [99, M3, M4, M5]
/*N3*/        assert_invariant(gcd(a0,a1) == gcd(a,b));  // By [78, M2, M5]
/*N4*/        assert_invariant(abs(y0*x1 - x0*y1) == 1); // By [98,M1,M3,M0,M4]
/*N5*/        assert_invariant(s1 == -s0);            // By [89, M7, M6]
/*N6*/        assert_invariant(abs(s0) == 1);         // By [70, M6]
/*N7*/        assert_invariant(s0*abs(y0) == y0);     // By [67, M6, M1]
/*N8*/        assert_invariant(s1*abs(y1) == y1);     // By [92, M7, M4]
/*N9*/        assert_invariant(-s0*abs(x0) == x0);    // By [69, M6, M0]
/*W0*/        assert_invariant(-s1*abs(x1) == x1);    // By [91, M7, M3]


/*W1*/        assert(abs(x1) >= abs(x0));             // By [83, M3, M0]
/*W2*/        assert(abs(y1) >= abs(y0));             // By [88, M4, M1]
/*W3*/        if (a1 == 0) {
/*W4*/             assert(abs(x1) >= 2*abs(x0));      // By [93, 95, M5, M3, M0]
/*W5*/             assert(abs(y1) >= 2*abs(y0));      // By [93, 96, M5, M4, M1]
              }
              // Less trivially,
/*W6*/        assert_invariant(gcd(x1, y1) == 1);
              // Proof: By [N4]  y0*x1 - x0*y1 == +-1,  so there obviously
              // exist integers u and v such that u*x1 + v*y1 == 1.
              // Let d be any common divisor of x1 and y1 (we know a common
              // divisor exists since 1 divides x1 and y1).  Since d divides
              // both x1 and y1,  d divides u*x1 + v*y1 == 1,  and thus
              // d divides 1.  Since d divides 1, d == +-1.  Thus a common 
              // divisor of x1 and y1 can only be -1 or 1, and since 1 is a
              // common divisor of x1 and y1, the greatest common divisor of x1
              // and y1 is 1.  For a similar proof see 
              // http://people.sju.edu/~pklingsb/rp.fta.pdf
        }

/*W7*/     assert(a1 == 0);
           // Since we finished the loop, we know a1 == 0 at this point.
/*W8*/     assert(x1*(a/gcd(a,b)) == -y1*(b/gcd(a,b)));
           // Proof: By [43,N2],  a*x1 + b*y1 == a1,  and so by [W7]
           //    a*x1 + b*y1 == 0
           //    x1*a == -y1*b
           // Letting d = gcd(a,b), by [38] d >= 1.  Since d divides a and b,
           // and x1*a == -y1*b,  we know  x1*(a/d) == -y1*(b/d)
/*W9*/     assert(gcd(a/gcd(a,b), b/gcd(a,b)) == 1);
           // Proof: Letting d=gcd(a,b), by [38] d >= 1.  Since d contains all
           // the common divisors of a and b, d divides both a and b, and the
           // quotients of a/d and b/d have no common divisors except 1 and -1.
           // Therefore gcd(a/d, b/d) == 1.
/*Z0*/     assert(abs(x1) == b/gcd(a,b));
           // Proof: Letting d = gcd(a,b), by [W8]  x1*(a/d) == -y1*(b/d).
           // By [W9] (a/d) and (b/d) are coprime, and by [55,W6] x1 and -y1 are
           // coprime.  So by [P6], abs(a/d)==abs(-y1)  and  abs(x1)==abs(b/d).
           // By [38,37],  d>0 and b>0,  so  abs(b/d) == b/d.
           // Thus, abs(x1) == abs(b/d) == b/d
/*Z1*/     assert(abs(y1) == a/gcd(a,b));
           // Proof: Letting d = gcd(a,b), by [W8]  x1*(a/d) == -y1*(b/d).
           // By [W9] (a/d) and (b/d) are coprime, and by [55,W6] x1 and -y1 are
           // coprime.  So by [P6], abs(a/d)==abs(-y1)  and  abs(x1)==abs(b/d).
           // By [38,35],  d>0 and a>=0,  so  abs(a/d) == a/d.
           // Thus, abs(y1) == abs(-y1) == abs(a/d) == a/d
/*Z2*/     assert((y0 == 1 && y1 == 0) || (abs(y1) >= 2*abs(y0)));
           // Proof: By [27, 33, W3, W5, W7]
/*Z3*/     assert(abs(x1) >= 2*abs(x0));           // By [54, W3, W4, W7]
/*Z4*/     assert(y0 == 1 || abs(y0) <= (a/gcd(a,b))/2);
           // Proof: By [Z2], (y0 == 1 && y1 == 0) || (abs(y1) >= 2*abs(y0)),
           // Assume (y0 == 1 && y1 == 0).  Then we would have  y0 == 1.
           // Assume instead  (abs(y1) >= 2*abs(y0)).  By [Z1],
           // abs(y1) == a/gcd(a,b).  Thus we would have 
           // a/gcd(a,b) == abs(y1) >= 2*abs(y0).  Letting d = gcd(a,b), we
           // would have  abs(y0)*2 <= a/d.  By [35,38] a >= 0 and d > 0, so
           // (a/d) >= 0.  Since (a/d) >= 0 and 2 > 0 and abs(y0)*2 <= (a/d),
           // by [P2] we would have  abs(y0) <= (a/d)/2.
           // Thus y0 == 1, or abs(y0) <= (a/d)/2.
/*Z5*/     assert(abs(x0) <= (b/gcd(a,b))/2);
           // Proof: By [Z3], abs(x1) >= 2*abs(x0), and by [Z0],
           // abs(x1) == b/gcd(a,b).  Thus,  b/gcd(a,b) == abs(x1) >= 2*abs(x0).
           // Letting d = gcd(a,b),  abs(x0)*2 <= b/d.  By [37, 38] b > 0 and
           // d > 0, so (b/d) >= 0.  Since (b/d) >= 0 and 2 > 0 and
           // abs(x0)*2 <= (b/d), by [P2]  abs(x0) <= (b/d)/2.
/*Z6*/     assert(a0 == gcd(a,b));
           // Proof: By [W7] a1 == 0, and by [39,M8] a0 > 0, so
           // gcd(a0,a1) == gcd(a0,0) == a0.
           // By [44,N3] gcd(a0,a1) == gcd(a,b).  Therefore,
           // a0 == gcd(a0,a1) == gcd(a,b)
/*Z7*/     assert(a*x0 + b*y0 == gcd(a,b));
           // By [42,N1] a*x0 + b*y0 == a0, and so by [Z6],
           // a*x0 + b*y0 == a0 == gcd(a,b)
           // Note: Since a*x0 + b*y0 == gcd(a,b), we know x0 and y0 are the
           // Bezout coefficients.
        *pX = x0;
        *pY = y0;
        *pGcd = a0;
}

#undef assert_invariant
#undef assert_precondition

#endif
