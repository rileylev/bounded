cmake_minimum_required(VERSION 3.20)

project(
  bounded
  VERSION 0.0.0
  LANGUAGES CXX)

  include(early_hook.cmake)

add_library(bounded INTERFACE)
add_library(bounded::bounded ALIAS bounded)
target_include_directories(bounded INTERFACE include)
target_compile_features(bounded INTERFACE cxx_std_20)

add_subdirectory(test)
