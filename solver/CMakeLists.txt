cmake_minimum_required(VERSION 3.7)

project(Solver)

add_executable(solver main.c i386.c)

# z3
find_package(Z3
  REQUIRED
  CONFIG
  # `NO_DEFAULT_PATH` is set so that -DZ3_DIR has to be passed to find Z3.
  # This should prevent us from accidentally picking up an installed
  # copy of Z3. This is here to benefit Z3's build system when building
  # this project. When making your own project you probably shouldn't
  # use this option.
  NO_DEFAULT_PATH
)
target_include_directories(solver PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(solver PRIVATE ${Z3_LIBRARIES})

# glib
find_package(PkgConfig REQUIRED)
pkg_search_module(GLIB REQUIRED glib-2.0)
target_include_directories(solver PRIVATE ${GLIB_INCLUDE_DIRS})
target_link_libraries(solver ${GLIB_LDFLAGS})
