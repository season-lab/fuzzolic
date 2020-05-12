cmake_minimum_required(VERSION 3.7)

project(Solver)

add_executable(solver-smt main.c i386.c branch_coverage.c opts.c xxHash/xxhash.c)
add_executable(solver-fuzzy main.c i386.c branch_coverage.c opts.c xxHash/xxhash.c)

target_compile_definitions(solver-smt PRIVATE USE_FUZZY_SOLVER=0)
target_compile_definitions(solver-fuzzy PRIVATE USE_FUZZY_SOLVER=1)

# z3
target_link_libraries(solver-smt z3)
target_link_libraries(solver-fuzzy z3)

# fuzzy
target_link_libraries(solver-smt ${CMAKE_SOURCE_DIR}/fuzzy-sat/libZ3Fuzzy.a)
target_link_libraries(solver-fuzzy ${CMAKE_SOURCE_DIR}/fuzzy-sat/libZ3Fuzzy.a)

# glib
find_package(PkgConfig REQUIRED)
pkg_search_module(GLIB REQUIRED glib-2.0)
target_include_directories(solver-smt PRIVATE ${GLIB_INCLUDE_DIRS})
target_include_directories(solver-fuzzy PRIVATE ${GLIB_INCLUDE_DIRS})
target_link_libraries(solver-smt ${GLIB_LDFLAGS})
target_link_libraries(solver-fuzzy ${GLIB_LDFLAGS})

set(CMAKE_CXX_FLAGS "-Wall -Wextra -O3 -g")
#set(CMAKE_CXX_FLAGS_DEBUG "-g")
#set(CMAKE_CXX_FLAGS_RELEASE "-O3")
