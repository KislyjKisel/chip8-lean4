#include <lean/lean.h>
#include <raylib.h>
#include <raylib_lean.h>

static void lean_chip8_audioSine(void* buffer, unsigned int frames) {
    const int frequency = 220;
    const int loop = 44100 / frequency;
    static int x = 0;
    for(size_t i = 0; i < frames; ++i) {
        ((short*)buffer)[i] = (short)(32200 * (x > (loop / 2) ? 1 : -1));
        x += 1;
        if (x > loop) x -= loop;
    }
}

LEAN_EXPORT lean_obj_res lean_chip8_AudioStream_setSine(b_lean_obj_arg stream, lean_obj_arg world) {
    lean_raylib_AudioStream_setCallback(stream, lean_chip8_audioSine);
    return lean_io_result_mk_ok(lean_box(0));
}
