cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

project(minisat)

#--------------------------------------------------------------------------------------------------
# Configurable options:

option(STATIC_BINARIES "Link binaries statically." ON)
option(USE_SORELEASE   "Use SORELEASE in shared library filename." ON)

#--------------------------------------------------------------------------------------------------
# Library version:

set(MINISAT_SOMAJOR   2)
set(MINISAT_SOMINOR   1)
set(MINISAT_SORELEASE 0)

# Compute VERSION and SOVERSION:
if (USE_SORELEASE)
  set(MINISAT_VERSION ${MINISAT_SOMAJOR}.${MINISAT_SOMINOR}.${MINISAT_SORELEASE})
else()
  set(MINISAT_VERSION ${MINISAT_SOMAJOR}.${MINISAT_SOMINOR})
endif()
set(MINISAT_SOVERSION ${MINISAT_SOMAJOR})

#--------------------------------------------------------------------------------------------------
# Dependencies:

find_package(ZLIB)
include_directories(${ZLIB_INCLUDE_DIR})
include_directories(${minisat_SOURCE_DIR})

#--------------------------------------------------------------------------------------------------
# Compile flags:

set(CMAKE_POSITION_INDEPENDENT_CODE ON)
add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -Wno-literal-suffix)

#--------------------------------------------------------------------------------------------------
# Build Targets:

set(MINISAT_LIB_SOURCES
    minisat/utils/Options.cc
    minisat/utils/System.cc
    minisat/core/Solver.cc
    minisat/simp/SimpSolver.cc)

add_library(minisat-lib-static STATIC ${MINISAT_LIB_SOURCES})
add_library(minisat-lib-shared SHARED ${MINISAT_LIB_SOURCES})

target_link_libraries(minisat-lib-shared ${ZLIB_LIBRARY})
target_link_libraries(minisat-lib-static ${ZLIB_LIBRARY})

add_executable(minisat_core minisat/core/Main.cc)
add_executable(minisat_simp minisat/simp/Main.cc)
add_executable(fuzz test/fuzz.cc)

if(STATIC_BINARIES)
  target_link_libraries(minisat_core minisat-lib-static)
  target_link_libraries(minisat_simp minisat-lib-static)
  target_link_libraries(fuzz minisat-lib-static)
else()
  target_link_libraries(minisat_core minisat-lib-shared)
  target_link_libraries(minisat_simp minisat-lib-shared)
  target_link_libraries(fuzz minisat-lib-shared)
endif()

set_target_properties(minisat-lib-static PROPERTIES OUTPUT_NAME "minisat")
set_target_properties(minisat-lib-shared
  PROPERTIES
    OUTPUT_NAME "minisat" 
    VERSION ${MINISAT_VERSION}
    SOVERSION ${MINISAT_SOVERSION})

set_target_properties(minisat_simp       PROPERTIES OUTPUT_NAME "minisat")

#--------------------------------------------------------------------------------------------------
# MinisatUP Package:

# build MinisatUP target
set(MINISATUP_LIB_SOURCES
    minisat/utils/Options.cc
    minisat/utils/System.cc
    minisat/core/Solver.cc
    minisat/minisatup.cc)

add_library(minisatup-lib-static STATIC ${MINISATUP_LIB_SOURCES})
set_target_properties(minisatup-lib-static PROPERTIES OUTPUT_NAME minisatup EXPORT_NAME MinisatUP)
add_library(MinisatUP::MinisatUP ALIAS minisatup-lib-static)

target_include_directories(minisatup-lib-static PUBLIC
  $<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>
)

install(FILES minisat/minisatup.h DESTINATION include)

# create MinisatUP package
include(CMakePackageConfigHelpers)

configure_package_config_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/cmake/MinisatUPConfig.cmake.in
  ${CMAKE_CURRENT_BINARY_DIR}/MinisatUPConfig.cmake
  INSTALL_DESTINATION lib/cmake/MinisatUP
)

write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/MinisatUPConfigVersion.cmake
  VERSION 1.0
  COMPATIBILITY SameMajorVersion
)

install(TARGETS minisatup-lib-static
  EXPORT MinisatUPTargets
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
  INCLUDES DESTINATION include
)

install(EXPORT MinisatUPTargets
  NAMESPACE MinisatUP::
  DESTINATION lib/cmake/MinisatUP
)

install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/MinisatUPConfig.cmake
  ${CMAKE_CURRENT_BINARY_DIR}/MinisatUPConfigVersion.cmake
  DESTINATION lib/cmake/MinisatUP
)

#--------------------------------------------------------------------------------------------------
# Installation targets:

install(TARGETS minisat-lib-static minisat-lib-shared minisat_core minisat_simp
        RUNTIME DESTINATION bin
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib)

install(DIRECTORY minisat/mtl minisat/utils minisat/core minisat/simp
        DESTINATION include/minisat
        FILES_MATCHING PATTERN "*.h")
