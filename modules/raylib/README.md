# Raylib Abra Module

This is a pure C Abra foreign module. Its Cargo build script regenerates the C
Abra glue from `../raylib.abra`, compiles that generated glue with `raylib.c`,
and loads Raylib dynamically when a Raylib function is first called.

Build the Abra module dynamic library:

```sh
cargo build --package abra_module_raylib
```

`abra_foreign_module.txt` contains the resulting dynamic library path
(`build/{library_prefix}abra_module_raylib{library_suffix}`).

If Raylib is not in the platform dynamic loader path, point the module at it:

```sh
export RAYLIB_LIBRARY=/path/to/libraylib.dylib
```

Then use it from Abra:

```abra
use raylib

init_window(800, 450, "Abra + Raylib")
set_target_fps(60)

while not window_should_close() {
    begin_drawing()
    clear_background(ray_white())
    draw_text("hello from Abra", 190, 200, 24, black())
    end_drawing()
}

close_window()
```

Raylib windowing and drawing APIs expect calls from one consistent UI thread.
The Abra declarations in `raylib.abra` use `#foreign(sync)` so these calls run
on the VM thread instead of the default async FFI thread.
