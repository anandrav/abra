#include "build/generated/abra_raylib.h"

#include <stdio.h>
#include <stdlib.h>

#if defined(_WIN32)
#include <windows.h>
#else
#include <dlfcn.h>
#endif

typedef struct RaylibColor {
    unsigned char r;
    unsigned char g;
    unsigned char b;
    unsigned char a;
} RaylibColor;

#if defined(_WIN32)
typedef HMODULE RaylibHandle;
#else
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

static RaylibColor raylib_color(Color color) {
    RaylibColor ret = {
        .r = byte_from_int(color.r),
        .g = byte_from_int(color.g),
        .b = byte_from_int(color.b),
        .a = byte_from_int(color.a),
    };
    return ret;
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
typedef void (*ClearBackgroundFn)(RaylibColor);
typedef void (*SetTargetFPSFn)(int);
typedef float (*GetFrameTimeFn)(void);
typedef int (*GetScreenWidthFn)(void);
typedef int (*GetScreenHeightFn)(void);
typedef void (*DrawTextFn)(const char *, int, int, int, RaylibColor);
typedef void (*DrawRectangleFn)(int, int, int, int, RaylibColor);
typedef void (*DrawRectangleLinesFn)(int, int, int, int, RaylibColor);
typedef void (*DrawCircleFn)(int, int, float, RaylibColor);
typedef void (*DrawCircleLinesFn)(int, int, float, RaylibColor);
typedef void (*DrawLineFn)(int, int, int, int, RaylibColor);
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

void abra_impl_raylib_init_window(AbraInt width, AbraInt height, AbraString title) {
    rl_InitWindow()((int)width, (int)height, title.ptr);
}

void abra_impl_raylib_close_window(void) {
    rl_CloseWindow()();
}

bool abra_impl_raylib_window_should_close(void) {
    return rl_WindowShouldClose()();
}

void abra_impl_raylib_begin_drawing(void) {
    rl_BeginDrawing()();
}

void abra_impl_raylib_end_drawing(void) {
    rl_EndDrawing()();
}

void abra_impl_raylib_clear_background(Color color) {
    rl_ClearBackground()(raylib_color(color));
}

void abra_impl_raylib_set_target_fps(AbraInt fps) {
    rl_SetTargetFPS()((int)fps);
}

double abra_impl_raylib_get_frame_time(void) {
    return (double)rl_GetFrameTime()();
}

AbraInt abra_impl_raylib_get_screen_width(void) {
    return (AbraInt)rl_GetScreenWidth()();
}

AbraInt abra_impl_raylib_get_screen_height(void) {
    return (AbraInt)rl_GetScreenHeight()();
}

void abra_impl_raylib_draw_text(AbraString text, AbraInt x, AbraInt y, AbraInt font_size, Color color) {
    rl_DrawText()(text.ptr, (int)x, (int)y, (int)font_size, raylib_color(color));
}

void abra_impl_raylib_draw_rectangle(AbraInt x, AbraInt y, AbraInt width, AbraInt height, Color color) {
    rl_DrawRectangle()((int)x, (int)y, (int)width, (int)height, raylib_color(color));
}

void abra_impl_raylib_draw_rectangle_lines(AbraInt x, AbraInt y, AbraInt width, AbraInt height, Color color) {
    rl_DrawRectangleLines()((int)x, (int)y, (int)width, (int)height, raylib_color(color));
}

void abra_impl_raylib_draw_circle(AbraInt center_x, AbraInt center_y, double radius, Color color) {
    rl_DrawCircle()((int)center_x, (int)center_y, (float)radius, raylib_color(color));
}

void abra_impl_raylib_draw_circle_lines(AbraInt center_x, AbraInt center_y, double radius, Color color) {
    rl_DrawCircleLines()((int)center_x, (int)center_y, (float)radius, raylib_color(color));
}

void abra_impl_raylib_draw_line(AbraInt start_x, AbraInt start_y, AbraInt end_x, AbraInt end_y, Color color) {
    rl_DrawLine()((int)start_x, (int)start_y, (int)end_x, (int)end_y, raylib_color(color));
}

void abra_impl_raylib_draw_fps(AbraInt x, AbraInt y) {
    rl_DrawFPS()((int)x, (int)y);
}

bool abra_impl_raylib_is_key_down(AbraInt key) {
    return rl_IsKeyDown()((int)key);
}

bool abra_impl_raylib_is_key_pressed(AbraInt key) {
    return rl_IsKeyPressed()((int)key);
}

AbraInt abra_impl_raylib_get_mouse_x(void) {
    return (AbraInt)rl_GetMouseX()();
}

AbraInt abra_impl_raylib_get_mouse_y(void) {
    return (AbraInt)rl_GetMouseY()();
}

bool abra_impl_raylib_is_mouse_button_down(AbraInt button) {
    return rl_IsMouseButtonDown()((int)button);
}

bool abra_impl_raylib_is_mouse_button_pressed(AbraInt button) {
    return rl_IsMouseButtonPressed()((int)button);
}

double abra_impl_raylib_get_time(void) {
    return rl_GetTime()();
}

AbraInt abra_impl_raylib_get_random_value(AbraInt min, AbraInt max) {
    return (AbraInt)rl_GetRandomValue()((int)min, (int)max);
}
