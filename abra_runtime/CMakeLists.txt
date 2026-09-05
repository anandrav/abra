include_directories(.)

add_library(abra_runtime SHARED
        abra_runtime.c)

set_target_properties(abra_runtime PROPERTIES
        LINKER_LANGUAGE C
        C_STANDARD 11)