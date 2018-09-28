# --- This file is distributed under the MIT Open Source License, as detailed
# in the file "LICENSE.TXT" in the root of this repository ---

if(TARGET test_extended_euclidean_proof)
    return()
endif()

cmake_minimum_required(VERSION 3.12)
project(test_extended_euclidean_proof VERSION 1.0.0 LANGUAGES CXX)


if (NOT CMAKE_BUILD_TYPE OR CMAKE_BUILD_TYPE STREQUAL "")
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "" FORCE)
endif()

add_executable(test_extended_euclidean_proof
               test_extended_euclidean_proof.cpp
               bounds_only_collins.h
               bounds_only_extended_euclidean_complete.h
               extended_euclidean_proof.h
               extended_euclidean_collins.h
               helpers/assert_helper_gcd.h
               helpers/bounds_only__a_ge_0__b_gt_a.h
               helpers/bounds_only__a_ge_0__b_gt_a__simplified.h
               helpers/bounds_only__b_eq_0__b_eq_a.h
               helpers/bounds_only__b_gt_0__b_eq_a.h
               helpers/extended_euclidean__a_ge_0__b_gt_a.h
               helpers/extended_euclidean__b_eq_0__b_eq_a.h
               helpers/extended_euclidean__b_gt_0__b_eq_a.h
               )

if(WIN32)
    set_property(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                 PROPERTY VS_STARTUP_PROJECT test_extended_euclidean_proof)
endif(WIN32)
