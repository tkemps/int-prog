cmake_minimum_required (VERSION 2.6)
project (EMPS)

# add the binary tree to the search path for include files
# so that we will find TutorialConfig.h
include_directories("${PROJECT_BINARY_DIR}")

add_executable(emps emps.c)
