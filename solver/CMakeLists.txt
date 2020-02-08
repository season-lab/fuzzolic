cmake_minimum_required(VERSION 3.10)

project(Solver)

add_executable(solver main.c i386.c)

target_link_libraries(solver z3)