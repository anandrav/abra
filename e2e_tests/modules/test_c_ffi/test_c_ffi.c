#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

#if defined(_WIN32)
#include <windows.h>
#else
#include <unistd.h>
#endif

typedef int64_t AbraInt;

typedef struct StringView {
    const char *ptr;
    size_t len;
} StringView;

typedef struct AbraVmFunctions {
    void (*push_int)(void *vm, AbraInt n);
    void (*push_float)(void *vm, double f);
    void (*push_bool)(void *vm, bool b);
    AbraInt (*pop_int)(void *vm);
    double (*pop_float)(void *vm);
    bool (*pop_bool)(void *vm);
    void (*pop)(void *vm);
    StringView (*view_string)(void *vm);
    void (*push_string)(void *vm, StringView string_view);
    void (*construct_struct)(void *vm, size_t arity);
    void (*construct_array)(void *vm, size_t len);
    void (*construct_variant)(void *vm, uint16_t tag);
    void (*deconstruct_struct)(void *vm);
    void (*deconstruct_array)(void *vm);
    void (*deconstruct_variant)(void *vm);
    size_t (*array_len)(void *vm);
} AbraVmFunctions;

#if defined(_WIN32)
#define ABRA_EXPORT __declspec(dllexport)
#else
#define ABRA_EXPORT __attribute__((visibility("default")))
#endif

ABRA_EXPORT void abra_ffi$test_c_ffi$add_ints(void *vm, const AbraVmFunctions *vm_funcs) {
    AbraInt b = vm_funcs->pop_int(vm);
    AbraInt a = vm_funcs->pop_int(vm);
    vm_funcs->push_int(vm, a + b);
}

ABRA_EXPORT void abra_ffi$test_c_ffi$not_bool(void *vm, const AbraVmFunctions *vm_funcs) {
    bool b = vm_funcs->pop_bool(vm);
    vm_funcs->push_bool(vm, !b);
}

ABRA_EXPORT void abra_ffi$test_c_ffi$sleep_ms(void *vm, const AbraVmFunctions *vm_funcs) {
    AbraInt ms = vm_funcs->pop_int(vm);
#if defined(_WIN32)
    Sleep((DWORD)ms);
#else
    usleep((useconds_t)(ms * 1000));
#endif
}
