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
               essential_asserts_collins.h
               essential_asserts_full.h
               extended_euclidean_proof.h
               extended_euclidean_collins.h
               helpers/assert_helper_gcd.h
               helpers/essential_asserts__a_ge_0__b_gt_a.h
               helpers/essential_asserts__a_ge_0__b_gt_a__improved.h
               helpers/essential_asserts__b_eq_0__b_eq_a.h
               helpers/essential_asserts__b_gt_0__b_eq_a.h
               helpers/extended_euclidean__a_ge_0__b_gt_a.h
               helpers/extended_euclidean__b_eq_0__b_eq_a.h
               helpers/extended_euclidean__b_gt_0__b_eq_a.h
               )

if(WIN32)
    set_property(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                 PROPERTY VS_STARTUP_PROJECT test_extended_euclidean_proof)
endif(WIN32)
