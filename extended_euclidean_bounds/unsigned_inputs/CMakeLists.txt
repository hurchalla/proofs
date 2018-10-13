# --- This file is distributed under the MIT Open Source License, as detailed
# in the file "LICENSE.TXT" in the root of this repository ---

if(TARGET test_unsigned_extended_euclidean)
    return()
endif()

cmake_minimum_required(VERSION 3.12)
project(test_unsigned_extended_euclidean VERSION 1.0.0 LANGUAGES CXX)


if(NOT CMAKE_BUILD_TYPE OR CMAKE_BUILD_TYPE STREQUAL "")
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "" FORCE)
endif()

add_executable(test_unsigned_extended_euclidean
               test_unsigned_extended_euclidean.cpp
               signed_extended_euclidean.h
               unsigned_extended_euclidean.h
               )

if(WIN32)
    set_property(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                 PROPERTY VS_STARTUP_PROJECT test_unsigned_extended_euclidean)
endif(WIN32)
