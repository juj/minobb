cmake_minimum_required(VERSION 3.15)
project(minobb_glb CXX)

# Optional default GLB to load. When set, it is used as the Visual Studio
# debug launch argument so you can just press F5:
#   cmake -B build -DOBB_TEST_GLB="C:/path/to/model.glb" -S .
# You can also override the argument from the VS "Debugging" project
# properties page without reconfiguring.
set(OBB_TEST_GLB "" CACHE STRING "GLB file passed as argv[1] when launching from Visual Studio")

add_executable(minobb_glb
    minobb.cpp
    test/minobb_glb.cpp
)

target_include_directories(minobb_glb PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_features(minobb_glb PRIVATE cxx_std_17)


if(MSVC)
    # /O2 conflicts with /RTC1 (Debug runtime checks), so optimize only
    # non-Debug configurations.
    target_compile_options(minobb_glb PRIVATE /W3
        $<$<NOT:$<CONFIG:Debug>>:/O2 /fp:fast>)

    # Run with the project root as working directory so relative GLB paths
    # resolve, and pre-fill the command-line arguments for F5 launches.
    set_target_properties(minobb_glb PROPERTIES
        VS_DEBUGGER_WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
    if(OBB_TEST_GLB)
        set_target_properties(minobb_glb PROPERTIES
            VS_DEBUGGER_COMMAND_ARGUMENTS "${OBB_TEST_GLB}")
    endif()
endif()
