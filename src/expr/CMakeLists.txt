file(GLOB_RECURSE sources "*.cpp" "*.h")

add_library(expr
  ${sources})

add_dependencies(expr util)

generic_includes(expr)

target_link_libraries(expr util big-int langapi)
