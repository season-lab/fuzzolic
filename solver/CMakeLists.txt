cmake_minimum_required(VERSION 3.10)

project(Solver)

add_executable(solver main.c i386.c)

# z3
target_link_libraries(solver z3)

# glib
find_package(PkgConfig REQUIRED)
pkg_search_module(GLIB REQUIRED glib-2.0)
target_include_directories(solver PRIVATE ${GLIB_INCLUDE_DIRS})
target_link_libraries(solver ${GLIB_LDFLAGS})