#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
#else
#include <dlfcn.h>
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

typedef struct Color {
    unsigned char r;
    unsigned char g;
    unsigned char b;
    unsigned char a;
} Color;

#if defined(_WIN32)
#define ABRA_EXPORT __declspec(dllexport)
typedef HMODULE RaylibHandle;
#else
#define ABRA_EXPORT __attribute__((visibility("default")))
typedef void *RaylibHandle;
#endif

static RaylibHandle raylib_handle = NULL;

static unsigned char byte_from_int(AbraInt n) {
    if (n < 0) {
        return 0;
    }
    if (n > 255) {
        return 255;
    }
    return (unsigned char)n;
}

static char *pop_c_string(void *vm, const AbraVmFunctions *vm_funcs) {
    StringView view = vm_funcs->view_string(vm);
    char *copy = (char *)malloc(view.len + 1);
    if (copy == NULL) {
        fprintf(stderr, "raylib Abra module: out of memory while reading string\n");
        abort();
    }
    memcpy(copy, view.ptr, view.len);
    copy[view.len] = '\0';
    vm_funcs->pop(vm);
    return copy;
}

static Color pop_color(void *vm, const AbraVmFunctions *vm_funcs) {
    vm_funcs->deconstruct_struct(vm);
    AbraInt r = vm_funcs->pop_int(vm);
    AbraInt g = vm_funcs->pop_int(vm);
    AbraInt b = vm_funcs->pop_int(vm);
    AbraInt a = vm_funcs->pop_int(vm);
    Color color = {
        .r = byte_from_int(r),
        .g = byte_from_int(g),
        .b = byte_from_int(b),
        .a = byte_from_int(a),
    };
    return color;
}

static RaylibHandle open_raylib(void) {
    if (raylib_handle != NULL) {
        return raylib_handle;
    }

    const char *env_path = getenv("RAYLIB_LIBRARY");
    if (env_path != NULL && env_path[0] != '\0') {
#if defined(_WIN32)
        raylib_handle = LoadLibraryA(env_path);
#else
        raylib_handle = dlopen(env_path, RTLD_LAZY | RTLD_LOCAL);
#endif
        if (raylib_handle != NULL) {
            return raylib_handle;
        }
    }

#if defined(_WIN32)
    const char *candidates[] = {"raylib.dll", "libraylib.dll", NULL};
    for (size_t i = 0; candidates[i] != NULL; i++) {
        raylib_handle = LoadLibraryA(candidates[i]);
        if (raylib_handle != NULL) {
            return raylib_handle;
        }
    }
#elif defined(__APPLE__)
    const char *candidates[] = {
        "libraylib.dylib",
        "/opt/homebrew/lib/libraylib.dylib",
        "/usr/local/lib/libraylib.dylib",
        NULL,
    };
    for (size_t i = 0; candidates[i] != NULL; i++) {
        raylib_handle = dlopen(candidates[i], RTLD_LAZY | RTLD_LOCAL);
        if (raylib_handle != NULL) {
            return raylib_handle;
        }
    }
#else
    const char *candidates[] = {"libraylib.so", "libraylib.so.5", "libraylib.so.4", NULL};
    for (size_t i = 0; candidates[i] != NULL; i++) {
        raylib_handle = dlopen(candidates[i], RTLD_LAZY | RTLD_LOCAL);
        if (raylib_handle != NULL) {
            return raylib_handle;
        }
    }
#endif

    fprintf(stderr, "raylib Abra module: could not load Raylib. Set RAYLIB_LIBRARY to the Raylib dynamic library path.\n");
    abort();
}

static void *raylib_symbol(const char *name) {
    RaylibHandle handle = open_raylib();
#if defined(_WIN32)
    void *symbol = (void *)GetProcAddress(handle, name);
#else
    void *symbol = dlsym(handle, name);
#endif
    if (symbol == NULL) {
        fprintf(stderr, "raylib Abra module: could not load Raylib symbol `%s`\n", name);
        abort();
    }
    return symbol;
}

typedef void (*InitWindowFn)(int, int, const char *);
typedef void (*CloseWindowFn)(void);
typedef bool (*WindowShouldCloseFn)(void);
typedef void (*BeginDrawingFn)(void);
typedef void (*EndDrawingFn)(void);
typedef void (*ClearBackgroundFn)(Color);
typedef void (*SetTargetFPSFn)(int);
typedef float (*GetFrameTimeFn)(void);
typedef int (*GetScreenWidthFn)(void);
typedef int (*GetScreenHeightFn)(void);
typedef void (*DrawTextFn)(const char *, int, int, int, Color);
typedef void (*DrawRectangleFn)(int, int, int, int, Color);
typedef void (*DrawRectangleLinesFn)(int, int, int, int, Color);
typedef void (*DrawCircleFn)(int, int, float, Color);
typedef void (*DrawCircleLinesFn)(int, int, float, Color);
typedef void (*DrawLineFn)(int, int, int, int, Color);
typedef void (*DrawFPSFn)(int, int);
typedef bool (*IsKeyDownFn)(int);
typedef bool (*IsKeyPressedFn)(int);
typedef int (*GetMouseXFn)(void);
typedef int (*GetMouseYFn)(void);
typedef bool (*IsMouseButtonDownFn)(int);
typedef bool (*IsMouseButtonPressedFn)(int);
typedef double (*GetTimeFn)(void);
typedef int (*GetRandomValueFn)(int, int);

static InitWindowFn rl_InitWindow(void) {
    static InitWindowFn fn = NULL;
    if (fn == NULL) fn = (InitWindowFn)raylib_symbol("InitWindow");
    return fn;
}

static CloseWindowFn rl_CloseWindow(void) {
    static CloseWindowFn fn = NULL;
    if (fn == NULL) fn = (CloseWindowFn)raylib_symbol("CloseWindow");
    return fn;
}

static WindowShouldCloseFn rl_WindowShouldClose(void) {
    static WindowShouldCloseFn fn = NULL;
    if (fn == NULL) fn = (WindowShouldCloseFn)raylib_symbol("WindowShouldClose");
    return fn;
}

static BeginDrawingFn rl_BeginDrawing(void) {
    static BeginDrawingFn fn = NULL;
    if (fn == NULL) fn = (BeginDrawingFn)raylib_symbol("BeginDrawing");
    return fn;
}

static EndDrawingFn rl_EndDrawing(void) {
    static EndDrawingFn fn = NULL;
    if (fn == NULL) fn = (EndDrawingFn)raylib_symbol("EndDrawing");
    return fn;
}

static ClearBackgroundFn rl_ClearBackground(void) {
    static ClearBackgroundFn fn = NULL;
    if (fn == NULL) fn = (ClearBackgroundFn)raylib_symbol("ClearBackground");
    return fn;
}

static SetTargetFPSFn rl_SetTargetFPS(void) {
    static SetTargetFPSFn fn = NULL;
    if (fn == NULL) fn = (SetTargetFPSFn)raylib_symbol("SetTargetFPS");
    return fn;
}

static GetFrameTimeFn rl_GetFrameTime(void) {
    static GetFrameTimeFn fn = NULL;
    if (fn == NULL) fn = (GetFrameTimeFn)raylib_symbol("GetFrameTime");
    return fn;
}

static GetScreenWidthFn rl_GetScreenWidth(void) {
    static GetScreenWidthFn fn = NULL;
    if (fn == NULL) fn = (GetScreenWidthFn)raylib_symbol("GetScreenWidth");
    return fn;
}

static GetScreenHeightFn rl_GetScreenHeight(void) {
    static GetScreenHeightFn fn = NULL;
    if (fn == NULL) fn = (GetScreenHeightFn)raylib_symbol("GetScreenHeight");
    return fn;
}

static DrawTextFn rl_DrawText(void) {
    static DrawTextFn fn = NULL;
    if (fn == NULL) fn = (DrawTextFn)raylib_symbol("DrawText");
    return fn;
}

static DrawRectangleFn rl_DrawRectangle(void) {
    static DrawRectangleFn fn = NULL;
    if (fn == NULL) fn = (DrawRectangleFn)raylib_symbol("DrawRectangle");
    return fn;
}

static DrawRectangleLinesFn rl_DrawRectangleLines(void) {
    static DrawRectangleLinesFn fn = NULL;
    if (fn == NULL) fn = (DrawRectangleLinesFn)raylib_symbol("DrawRectangleLines");
    return fn;
}

static DrawCircleFn rl_DrawCircle(void) {
    static DrawCircleFn fn = NULL;
    if (fn == NULL) fn = (DrawCircleFn)raylib_symbol("DrawCircle");
    return fn;
}

static DrawCircleLinesFn rl_DrawCircleLines(void) {
    static DrawCircleLinesFn fn = NULL;
    if (fn == NULL) fn = (DrawCircleLinesFn)raylib_symbol("DrawCircleLines");
    return fn;
}

static DrawLineFn rl_DrawLine(void) {
    static DrawLineFn fn = NULL;
    if (fn == NULL) fn = (DrawLineFn)raylib_symbol("DrawLine");
    return fn;
}

static DrawFPSFn rl_DrawFPS(void) {
    static DrawFPSFn fn = NULL;
    if (fn == NULL) fn = (DrawFPSFn)raylib_symbol("DrawFPS");
    return fn;
}

static IsKeyDownFn rl_IsKeyDown(void) {
    static IsKeyDownFn fn = NULL;
    if (fn == NULL) fn = (IsKeyDownFn)raylib_symbol("IsKeyDown");
    return fn;
}

static IsKeyPressedFn rl_IsKeyPressed(void) {
    static IsKeyPressedFn fn = NULL;
    if (fn == NULL) fn = (IsKeyPressedFn)raylib_symbol("IsKeyPressed");
    return fn;
}

static GetMouseXFn rl_GetMouseX(void) {
    static GetMouseXFn fn = NULL;
    if (fn == NULL) fn = (GetMouseXFn)raylib_symbol("GetMouseX");
    return fn;
}

static GetMouseYFn rl_GetMouseY(void) {
    static GetMouseYFn fn = NULL;
    if (fn == NULL) fn = (GetMouseYFn)raylib_symbol("GetMouseY");
    return fn;
}

static IsMouseButtonDownFn rl_IsMouseButtonDown(void) {
    static IsMouseButtonDownFn fn = NULL;
    if (fn == NULL) fn = (IsMouseButtonDownFn)raylib_symbol("IsMouseButtonDown");
    return fn;
}

static IsMouseButtonPressedFn rl_IsMouseButtonPressed(void) {
    static IsMouseButtonPressedFn fn = NULL;
    if (fn == NULL) fn = (IsMouseButtonPressedFn)raylib_symbol("IsMouseButtonPressed");
    return fn;
}

static GetTimeFn rl_GetTime(void) {
    static GetTimeFn fn = NULL;
    if (fn == NULL) fn = (GetTimeFn)raylib_symbol("GetTime");
    return fn;
}

static GetRandomValueFn rl_GetRandomValue(void) {
    static GetRandomValueFn fn = NULL;
    if (fn == NULL) fn = (GetRandomValueFn)raylib_symbol("GetRandomValue");
    return fn;
}

ABRA_EXPORT void abra_ffi$raylib$init_window(void *vm, const AbraVmFunctions *vm_funcs) {
    char *title = pop_c_string(vm, vm_funcs);
    int height = (int)vm_funcs->pop_int(vm);
    int width = (int)vm_funcs->pop_int(vm);
    rl_InitWindow()(width, height, title);
    free(title);
}

ABRA_EXPORT void abra_ffi$raylib$close_window(void *vm, const AbraVmFunctions *vm_funcs) {
    (void)vm;
    (void)vm_funcs;
    rl_CloseWindow()();
}

ABRA_EXPORT void abra_ffi$raylib$window_should_close(void *vm, const AbraVmFunctions *vm_funcs) {
    vm_funcs->push_bool(vm, rl_WindowShouldClose()());
}

ABRA_EXPORT void abra_ffi$raylib$begin_drawing(void *vm, const AbraVmFunctions *vm_funcs) {
    (void)vm;
    (void)vm_funcs;
    rl_BeginDrawing()();
}

ABRA_EXPORT void abra_ffi$raylib$end_drawing(void *vm, const AbraVmFunctions *vm_funcs) {
    (void)vm;
    (void)vm_funcs;
    rl_EndDrawing()();
}

ABRA_EXPORT void abra_ffi$raylib$clear_background(void *vm, const AbraVmFunctions *vm_funcs) {
    Color color = pop_color(vm, vm_funcs);
    rl_ClearBackground()(color);
}

ABRA_EXPORT void abra_ffi$raylib$set_target_fps(void *vm, const AbraVmFunctions *vm_funcs) {
    int fps = (int)vm_funcs->pop_int(vm);
    rl_SetTargetFPS()(fps);
}

ABRA_EXPORT void abra_ffi$raylib$get_frame_time(void *vm, const AbraVmFunctions *vm_funcs) {
    vm_funcs->push_float(vm, (double)rl_GetFrameTime()());
}

ABRA_EXPORT void abra_ffi$raylib$get_screen_width(void *vm, const AbraVmFunctions *vm_funcs) {
    vm_funcs->push_int(vm, (AbraInt)rl_GetScreenWidth()());
}

ABRA_EXPORT void abra_ffi$raylib$get_screen_height(void *vm, const AbraVmFunctions *vm_funcs) {
    vm_funcs->push_int(vm, (AbraInt)rl_GetScreenHeight()());
}

ABRA_EXPORT void abra_ffi$raylib$draw_text(void *vm, const AbraVmFunctions *vm_funcs) {
    Color color = pop_color(vm, vm_funcs);
    int font_size = (int)vm_funcs->pop_int(vm);
    int y = (int)vm_funcs->pop_int(vm);
    int x = (int)vm_funcs->pop_int(vm);
    char *text = pop_c_string(vm, vm_funcs);
    rl_DrawText()(text, x, y, font_size, color);
    free(text);
}

ABRA_EXPORT void abra_ffi$raylib$draw_rectangle(void *vm, const AbraVmFunctions *vm_funcs) {
    Color color = pop_color(vm, vm_funcs);
    int height = (int)vm_funcs->pop_int(vm);
    int width = (int)vm_funcs->pop_int(vm);
    int y = (int)vm_funcs->pop_int(vm);
    int x = (int)vm_funcs->pop_int(vm);
    rl_DrawRectangle()(x, y, width, height, color);
}

ABRA_EXPORT void abra_ffi$raylib$draw_rectangle_lines(void *vm, const AbraVmFunctions *vm_funcs) {
    Color color = pop_color(vm, vm_funcs);
    int height = (int)vm_funcs->pop_int(vm);
    int width = (int)vm_funcs->pop_int(vm);
    int y = (int)vm_funcs->pop_int(vm);
    int x = (int)vm_funcs->pop_int(vm);
    rl_DrawRectangleLines()(x, y, width, height, color);
}

ABRA_EXPORT void abra_ffi$raylib$draw_circle(void *vm, const AbraVmFunctions *vm_funcs) {
    Color color = pop_color(vm, vm_funcs);
    float radius = (float)vm_funcs->pop_float(vm);
    int center_y = (int)vm_funcs->pop_int(vm);
    int center_x = (int)vm_funcs->pop_int(vm);
    rl_DrawCircle()(center_x, center_y, radius, color);
}

ABRA_EXPORT void abra_ffi$raylib$draw_circle_lines(void *vm, const AbraVmFunctions *vm_funcs) {
    Color color = pop_color(vm, vm_funcs);
    float radius = (float)vm_funcs->pop_float(vm);
    int center_y = (int)vm_funcs->pop_int(vm);
    int center_x = (int)vm_funcs->pop_int(vm);
    rl_DrawCircleLines()(center_x, center_y, radius, color);
}

ABRA_EXPORT void abra_ffi$raylib$draw_line(void *vm, const AbraVmFunctions *vm_funcs) {
    Color color = pop_color(vm, vm_funcs);
    int end_y = (int)vm_funcs->pop_int(vm);
    int end_x = (int)vm_funcs->pop_int(vm);
    int start_y = (int)vm_funcs->pop_int(vm);
    int start_x = (int)vm_funcs->pop_int(vm);
    rl_DrawLine()(start_x, start_y, end_x, end_y, color);
}

ABRA_EXPORT void abra_ffi$raylib$draw_fps(void *vm, const AbraVmFunctions *vm_funcs) {
    int y = (int)vm_funcs->pop_int(vm);
    int x = (int)vm_funcs->pop_int(vm);
    rl_DrawFPS()(x, y);
}

ABRA_EXPORT void abra_ffi$raylib$is_key_down(void *vm, const AbraVmFunctions *vm_funcs) {
    int key = (int)vm_funcs->pop_int(vm);
    vm_funcs->push_bool(vm, rl_IsKeyDown()(key));
}

ABRA_EXPORT void abra_ffi$raylib$is_key_pressed(void *vm, const AbraVmFunctions *vm_funcs) {
    int key = (int)vm_funcs->pop_int(vm);
    vm_funcs->push_bool(vm, rl_IsKeyPressed()(key));
}

ABRA_EXPORT void abra_ffi$raylib$get_mouse_x(void *vm, const AbraVmFunctions *vm_funcs) {
    vm_funcs->push_int(vm, (AbraInt)rl_GetMouseX()());
}

ABRA_EXPORT void abra_ffi$raylib$get_mouse_y(void *vm, const AbraVmFunctions *vm_funcs) {
    vm_funcs->push_int(vm, (AbraInt)rl_GetMouseY()());
}

ABRA_EXPORT void abra_ffi$raylib$is_mouse_button_down(void *vm, const AbraVmFunctions *vm_funcs) {
    int button = (int)vm_funcs->pop_int(vm);
    vm_funcs->push_bool(vm, rl_IsMouseButtonDown()(button));
}

ABRA_EXPORT void abra_ffi$raylib$is_mouse_button_pressed(void *vm, const AbraVmFunctions *vm_funcs) {
    int button = (int)vm_funcs->pop_int(vm);
    vm_funcs->push_bool(vm, rl_IsMouseButtonPressed()(button));
}

ABRA_EXPORT void abra_ffi$raylib$get_time(void *vm, const AbraVmFunctions *vm_funcs) {
    vm_funcs->push_float(vm, rl_GetTime()());
}

ABRA_EXPORT void abra_ffi$raylib$get_random_value(void *vm, const AbraVmFunctions *vm_funcs) {
    int max = (int)vm_funcs->pop_int(vm);
    int min = (int)vm_funcs->pop_int(vm);
    vm_funcs->push_int(vm, (AbraInt)rl_GetRandomValue()(min, max));
}
