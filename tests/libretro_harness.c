/* libretro_harness.c - Generic libretro core driver with A/V capture
 * Loads any libretro .so via dlopen, runs N frames, captures per-frame
 * video/audio CRC32 hashes into a binary .avlog file.
 *
 * Adapted for Neo Geo CD: path-only loading (CHD files are huge),
 * configurable system directory, and core option injection.
 *
 * Copyright (c) 2026 Romain Tisserand
 * MIT License */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>
#include <dlfcn.h>
#include <math.h>

#include "libretro.h"

/* ================================================================
 * CRC32 (table-based, self-contained)
 * ================================================================ */
static uint32_t crc32_table[256];
static int crc32_table_init = 0;

static void crc32_init(void) {
    if (crc32_table_init) return;
    for (uint32_t i = 0; i < 256; i++) {
        uint32_t c = i;
        for (int j = 0; j < 8; j++)
            c = (c >> 1) ^ (c & 1 ? 0xEDB88320u : 0);
        crc32_table[i] = c;
    }
    crc32_table_init = 1;
}

static uint32_t crc32_buf(const void *buf, size_t len) {
    const uint8_t *p = (const uint8_t *)buf;
    uint32_t crc = 0xFFFFFFFF;
    for (size_t i = 0; i < len; i++)
        crc = crc32_table[(crc ^ p[i]) & 0xFF] ^ (crc >> 8);
    return crc ^ 0xFFFFFFFF;
}

/* ================================================================
 * .avlog binary format
 * ================================================================ */
#define AVLOG_MAGIC  0x474C5641  /* "AVLG" little-endian */
#define AVLOG_VERSION 3

#pragma pack(push, 1)
typedef struct {
    uint32_t magic;
    uint32_t version;
    uint32_t num_frames;
    uint32_t reserved;
} avlog_header_t;

typedef struct {
    uint32_t frame_num;
    uint32_t video_crc;
    uint16_t width;
    uint16_t height;
    uint32_t audio_crc;
    uint32_t audio_frames;
    uint32_t audio_energy;
    uint32_t band_energy[4];
} avlog_entry_t;  /* 40 bytes */
#pragma pack(pop)

/* ================================================================
 * Core options injection
 * ================================================================ */
#define MAX_OPTIONS 64

typedef struct {
    char key[128];
    char value[128];
} option_kv_t;

static option_kv_t user_options[MAX_OPTIONS];
static int num_user_options = 0;

static const char *find_user_option(const char *key) {
    for (int i = 0; i < num_user_options; i++)
        if (strcmp(user_options[i].key, key) == 0)
            return user_options[i].value;
    return NULL;
}

static void add_user_option(const char *kv) {
    if (num_user_options >= MAX_OPTIONS) return;
    const char *eq = strchr(kv, '=');
    if (!eq) return;
    size_t klen = (size_t)(eq - kv);
    if (klen >= sizeof(user_options[0].key)) return;
    memcpy(user_options[num_user_options].key, kv, klen);
    user_options[num_user_options].key[klen] = '\0';
    strncpy(user_options[num_user_options].value, eq + 1,
            sizeof(user_options[0].value) - 1);
    user_options[num_user_options].value[sizeof(user_options[0].value) - 1] = '\0';
    num_user_options++;
}

/* ================================================================
 * Input script
 * ================================================================ */
#define MAX_INPUT_EVENTS 4096

typedef struct {
    uint32_t frame;
    uint8_t  port;
    int      press;
    uint16_t button;
} input_event_t;

static input_event_t input_events[MAX_INPUT_EVENTS];
static int num_input_events = 0;
static uint16_t input_buttons[2] = {0, 0};

static uint16_t button_name_to_bit(const char *name) {
    static const struct { const char *name; uint16_t bit; } map[] = {
        {"B",      1 << RETRO_DEVICE_ID_JOYPAD_B},
        {"Y",      1 << RETRO_DEVICE_ID_JOYPAD_Y},
        {"SELECT", 1 << RETRO_DEVICE_ID_JOYPAD_SELECT},
        {"START",  1 << RETRO_DEVICE_ID_JOYPAD_START},
        {"UP",     1 << RETRO_DEVICE_ID_JOYPAD_UP},
        {"DOWN",   1 << RETRO_DEVICE_ID_JOYPAD_DOWN},
        {"LEFT",   1 << RETRO_DEVICE_ID_JOYPAD_LEFT},
        {"RIGHT",  1 << RETRO_DEVICE_ID_JOYPAD_RIGHT},
        {"A",      1 << RETRO_DEVICE_ID_JOYPAD_A},
        {"X",      1 << RETRO_DEVICE_ID_JOYPAD_X},
        {"L",      1 << RETRO_DEVICE_ID_JOYPAD_L},
        {"R",      1 << RETRO_DEVICE_ID_JOYPAD_R},
        {NULL, 0}
    };
    for (int i = 0; map[i].name; i++)
        if (strcmp(name, map[i].name) == 0)
            return map[i].bit;
    return 0;
}

static int load_input_script(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) return -1;
    char line[256];
    num_input_events = 0;
    while (fgets(line, sizeof(line), f) && num_input_events < MAX_INPUT_EVENTS) {
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        uint32_t frame;
        unsigned port;
        char action, btn_name[32];
        if (sscanf(line, "%u %u %c %31s", &frame, &port, &action, btn_name) == 4) {
            if (port > 1) continue;
            uint16_t bit = button_name_to_bit(btn_name);
            if (!bit) continue;
            input_events[num_input_events].frame = frame;
            input_events[num_input_events].port = (uint8_t)port;
            input_events[num_input_events].press = (action == '+') ? 1 : 0;
            input_events[num_input_events].button = bit;
            num_input_events++;
        }
    }
    fclose(f);
    return num_input_events;
}

static void apply_input_events(uint32_t frame) {
    for (int i = 0; i < num_input_events; i++) {
        if (input_events[i].frame == frame) {
            if (input_events[i].press)
                input_buttons[input_events[i].port] |= input_events[i].button;
            else
                input_buttons[input_events[i].port] &= ~input_events[i].button;
        }
    }
}

/* ================================================================
 * Per-frame A/V capture state
 * ================================================================ */
static uint32_t cur_video_crc = 0;
static uint16_t cur_video_w = 0, cur_video_h = 0;
static uint32_t cur_audio_crc = 0;
static uint32_t cur_audio_frames = 0;
static uint64_t cur_audio_energy = 0;

#define AUDIO_DFT_SIZE 512
#define NUM_AUDIO_BANDS 4
static float audio_dft_buf[AUDIO_DFT_SIZE];
static int audio_dft_pos = 0;
static const int band_edge[NUM_AUDIO_BANDS + 1] = {0, 4, 20, 60, 180};

static void compute_band_energies(const float *buf, int n, uint64_t band_out[NUM_AUDIO_BANDS]) {
    float padded[AUDIO_DFT_SIZE];
    for (int i = 0; i < AUDIO_DFT_SIZE; i++)
        padded[i] = (i < n) ? buf[i] : 0.0f;

    for (int i = 0; i < AUDIO_DFT_SIZE; i++) {
        float w = 0.5f * (1.0f - cosf(2.0f * (float)M_PI * i / AUDIO_DFT_SIZE));
        padded[i] *= w;
    }

    double band_accum[NUM_AUDIO_BANDS] = {0};
    int max_bin = band_edge[NUM_AUDIO_BANDS];

    for (int k = 0; k < max_bin; k++) {
        float coeff = 2.0f * cosf(2.0f * (float)M_PI * k / AUDIO_DFT_SIZE);
        float s0 = 0, s1 = 0, s2 = 0;
        for (int i = 0; i < AUDIO_DFT_SIZE; i++) {
            s0 = padded[i] + coeff * s1 - s2;
            s2 = s1;
            s1 = s0;
        }
        double power = (double)s1 * s1 + (double)s2 * s2 - (double)coeff * s1 * s2;

        int band = NUM_AUDIO_BANDS - 1;
        for (int b = 0; b < NUM_AUDIO_BANDS; b++) {
            if (k < band_edge[b + 1]) { band = b; break; }
        }
        band_accum[band] += power;
    }

    for (int b = 0; b < NUM_AUDIO_BANDS; b++)
        band_out[b] = (uint64_t)(sqrt(band_accum[b] / max_bin));
}

static enum retro_pixel_format pixel_format = RETRO_PIXEL_FORMAT_0RGB1555;

/* Frame dumping */
static int dump_frames[64];
static int num_dump_frames = 0;
static int cur_frame_num = 0;
static const char *dump_prefix = NULL;

static void save_frame_ppm(const void *data, unsigned width, unsigned height, size_t pitch, int frame) {
    if (!data || !dump_prefix) return;
    char path[512];
    snprintf(path, sizeof(path), "%s_f%05d.ppm", dump_prefix, frame);
    FILE *f = fopen(path, "wb");
    if (!f) return;
    fprintf(f, "P6\n%u %u\n255\n", width, height);
    const uint8_t *p = (const uint8_t *)data;
    for (unsigned y = 0; y < height; y++) {
        const uint8_t *row = p + y * pitch;
        for (unsigned x = 0; x < width; x++) {
            uint8_t r, g, b;
            if (pixel_format == RETRO_PIXEL_FORMAT_XRGB8888) {
                uint32_t px = ((const uint32_t *)row)[x];
                r = (px >> 16) & 0xFF;
                g = (px >> 8) & 0xFF;
                b = px & 0xFF;
            } else { /* RGB565 */
                uint16_t px = ((const uint16_t *)row)[x];
                r = ((px >> 11) & 0x1F) << 3;
                g = ((px >> 5) & 0x3F) << 2;
                b = (px & 0x1F) << 3;
            }
            uint8_t rgb[3] = {r, g, b};
            fwrite(rgb, 1, 3, f);
        }
    }
    fclose(f);
    fprintf(stderr, "Dumped frame %d -> %s (%ux%u)\n", frame, path, width, height);
}

static int should_dump_frame(int frame) {
    for (int i = 0; i < num_dump_frames; i++)
        if (dump_frames[i] == frame) return 1;
    return 0;
}

/* ================================================================
 * System directory (for BIOS files)
 * ================================================================ */
static const char *system_dir = ".";
static const char *save_dir = ".";

/* ================================================================
 * libretro callbacks
 * ================================================================ */
static int verbose_log = 0;
static int benchmark_mode = 0;
static void log_printf(enum retro_log_level level, const char *fmt, ...) {
    if (!verbose_log) return;
    (void)level;
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
}

static bool env_cb(unsigned cmd, void *data) {
    switch (cmd) {
    case RETRO_ENVIRONMENT_SET_PIXEL_FORMAT:
        pixel_format = *(enum retro_pixel_format *)data;
        return 1;
    case RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY:
        *(const char **)data = system_dir;
        return 1;
    case RETRO_ENVIRONMENT_GET_SAVE_DIRECTORY:
        *(const char **)data = save_dir;
        return 1;
    case RETRO_ENVIRONMENT_GET_LOG_INTERFACE: {
        struct retro_log_callback *cb = (struct retro_log_callback *)data;
        cb->log = log_printf;
        return 1;
    }
    case RETRO_ENVIRONMENT_GET_VARIABLE: {
        struct retro_variable *var = (struct retro_variable *)data;
        if (var && var->key) {
            const char *val = find_user_option(var->key);
            var->value = val;  /* NULL if not found */
        }
        return 1;
    }
    case 17: /* GET_VARIABLE_UPDATE */
        *(bool *)data = false;
        return 1;
    case RETRO_ENVIRONMENT_SET_SUPPORT_NO_GAME:
        return 1;
    case 36: /* SET_CONTROLLER_INFO */
    case 65: /* GET_INPUT_BITMASKS */
        return 1;
    case 58: /* GET_GAME_INFO_EXT */
        return 0;
    case RETRO_ENVIRONMENT_SET_VARIABLES: /* also SET_INPUT_DESCRIPTORS (16) */
        return 1;
    case 47: /* SET_CORE_OPTIONS_V2 */
        return 1;
    case 53: /* SET_CORE_OPTIONS_V2_INTL */
        return 1;
    case 67: /* SET_CORE_OPTIONS_UPDATE_DISPLAY_CALLBACK */
        return 1;
    case 52: /* SET_FASTFORWARDING_OVERRIDE */
        return 1;
    default:
        return 0;
    }
}

static void video_cb(const void *data, unsigned width, unsigned height, size_t pitch) {
    if (!data) {
        cur_video_crc = 0;
        cur_video_w = 0;
        cur_video_h = 0;
        return;
    }

    cur_video_w = (uint16_t)width;
    cur_video_h = (uint16_t)height;

    if (benchmark_mode) {
        cur_video_crc = 0;
        return;
    }

    /* Compute CRC over normalized RGB555 to make pixel format irrelevant.
     * Both XRGB8888 and RGB565 are reduced to 5-bit-per-channel values. */
    uint32_t crc = 0xFFFFFFFF;
    const uint8_t *p = (const uint8_t *)data;
    for (unsigned y = 0; y < height; y++) {
        const uint8_t *row = p + y * pitch;
        for (unsigned x = 0; x < width; x++) {
            uint8_t r5, g5, b5;
            if (pixel_format == RETRO_PIXEL_FORMAT_XRGB8888) {
                uint32_t px = ((const uint32_t *)row)[x];
                r5 = (uint8_t)((px >> 19) & 0x1F);
                g5 = (uint8_t)((px >> 11) & 0x1F);
                b5 = (uint8_t)((px >> 3) & 0x1F);
            } else { /* RGB565 */
                uint16_t px = ((const uint16_t *)row)[x];
                r5 = (uint8_t)((px >> 11) & 0x1F);
                g5 = (uint8_t)((px >> 6) & 0x1F); /* 6-bit green → 5-bit */
                b5 = (uint8_t)(px & 0x1F);
            }
            uint16_t rgb555 = (uint16_t)((r5 << 10) | (g5 << 5) | b5);
            crc = crc32_table[(crc ^ (rgb555 & 0xFF)) & 0xFF] ^ (crc >> 8);
            crc = crc32_table[(crc ^ (rgb555 >> 8)) & 0xFF] ^ (crc >> 8);
        }
    }
    cur_video_crc = crc ^ 0xFFFFFFFF;

    if (should_dump_frame(cur_frame_num))
        save_frame_ppm(data, width, height, pitch, cur_frame_num);
}

static void audio_sample_cb(int16_t left, int16_t right) {
    (void)left; (void)right;
}

static size_t audio_batch_cb(const int16_t *data, size_t frames) {
    if (frames > 0) {
        cur_audio_frames = (uint32_t)frames;

        if (benchmark_mode) {
            cur_audio_crc = 0;
            cur_audio_energy = 0;
            return frames;
        }

        size_t bytes = frames * 2 * sizeof(int16_t);
        cur_audio_crc = crc32_buf(data, bytes);

        uint64_t energy = 0;
        for (size_t i = 0; i < frames * 2; i++) {
            int32_t s = data[i];
            energy += (uint64_t)(s * s);
        }
        cur_audio_energy = energy;

        for (size_t i = 0; i < frames && audio_dft_pos < AUDIO_DFT_SIZE; i++) {
            float mono = ((float)data[i*2] + (float)data[i*2+1]) * 0.5f;
            audio_dft_buf[audio_dft_pos++] = mono;
        }
    }
    return frames;
}

static void input_poll_cb(void) { /* nothing */ }

static int16_t input_state_cb(unsigned port, unsigned device, unsigned index, unsigned id) {
    (void)index;
    if (device != RETRO_DEVICE_JOYPAD || port > 1) return 0;
    return (input_buttons[port] >> id) & 1;
}

/* ================================================================
 * dlopen helpers
 * ================================================================ */
typedef void    (*pf_retro_init)(void);
typedef void    (*pf_retro_deinit)(void);
typedef void    (*pf_retro_get_system_info)(struct retro_system_info *);
typedef void    (*pf_retro_get_system_av_info)(struct retro_system_av_info *);
typedef void    (*pf_retro_set_environment)(retro_environment_t);
typedef void    (*pf_retro_set_video_refresh)(retro_video_refresh_t);
typedef void    (*pf_retro_set_audio_sample)(retro_audio_sample_t);
typedef void    (*pf_retro_set_audio_sample_batch)(retro_audio_sample_batch_t);
typedef void    (*pf_retro_set_input_poll)(retro_input_poll_t);
typedef void    (*pf_retro_set_input_state)(retro_input_state_t);
typedef int     (*pf_retro_load_game)(const struct retro_game_info *);
typedef void    (*pf_retro_unload_game)(void);
typedef void    (*pf_retro_run)(void);
typedef void    (*pf_retro_reset)(void);

typedef struct {
    void *handle;
    pf_retro_init                init;
    pf_retro_deinit              deinit;
    pf_retro_get_system_info     get_system_info;
    pf_retro_get_system_av_info  get_system_av_info;
    pf_retro_set_environment     set_environment;
    pf_retro_set_video_refresh   set_video_refresh;
    pf_retro_set_audio_sample    set_audio_sample;
    pf_retro_set_audio_sample_batch set_audio_sample_batch;
    pf_retro_set_input_poll      set_input_poll;
    pf_retro_set_input_state     set_input_state;
    pf_retro_load_game           load_game;
    pf_retro_unload_game         unload_game;
    pf_retro_run                 run;
    pf_retro_reset               reset;
} core_t;

#define LOAD_SYM(dst, name) do { \
    *(void **)(&(dst)) = dlsym(c->handle, #name); \
    if (!(dst)) { fprintf(stderr, "Missing symbol: %s\n", #name); return -1; } \
} while(0)

static int core_load(core_t *c, const char *path) {
    c->handle = dlopen(path, RTLD_NOW);
    if (!c->handle) {
        fprintf(stderr, "dlopen(%s): %s\n", path, dlerror());
        return -1;
    }
    LOAD_SYM(c->init, retro_init);
    LOAD_SYM(c->deinit, retro_deinit);
    LOAD_SYM(c->get_system_info, retro_get_system_info);
    LOAD_SYM(c->get_system_av_info, retro_get_system_av_info);
    LOAD_SYM(c->set_environment, retro_set_environment);
    LOAD_SYM(c->set_video_refresh, retro_set_video_refresh);
    LOAD_SYM(c->set_audio_sample, retro_set_audio_sample);
    LOAD_SYM(c->set_audio_sample_batch, retro_set_audio_sample_batch);
    LOAD_SYM(c->set_input_poll, retro_set_input_poll);
    LOAD_SYM(c->set_input_state, retro_set_input_state);
    LOAD_SYM(c->load_game, retro_load_game);
    LOAD_SYM(c->unload_game, retro_unload_game);
    LOAD_SYM(c->run, retro_run);
    LOAD_SYM(c->reset, retro_reset);
    return 0;
}

static void core_unload(core_t *c) {
    if (c->handle) {
        c->deinit();
        dlclose(c->handle);
        c->handle = NULL;
    }
}

/* ================================================================
 * Main
 * ================================================================ */
static void usage(const char *argv0) {
    fprintf(stderr,
        "Usage: %s <core.so> <rom> <frames> <output.avlog>\n"
        "       [input_script.txt]\n"
        "       [--system-dir DIR] [--save-dir DIR]\n"
        "       [--option key=value] ...\n"
        "       [--dump-frames 1,2,3 --dump-prefix path]\n",
        argv0);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        usage(argv[0]);
        return 1;
    }

    const char *core_path   = argv[1];
    const char *rom_path    = argv[2];
    int num_frames          = atoi(argv[3]);
    const char *output_path = argv[4];
    const char *input_path  = NULL;

    /* Parse optional arguments */
    for (int i = 5; i < argc; i++) {
        if (strcmp(argv[i], "--system-dir") == 0 && i + 1 < argc) {
            system_dir = argv[++i];
        } else if (strcmp(argv[i], "--save-dir") == 0 && i + 1 < argc) {
            save_dir = argv[++i];
        } else if (strcmp(argv[i], "--option") == 0 && i + 1 < argc) {
            add_user_option(argv[++i]);
        } else if (strcmp(argv[i], "--dump-frames") == 0 && i + 1 < argc) {
            char *s = argv[++i];
            while (*s && num_dump_frames < 64) {
                dump_frames[num_dump_frames++] = atoi(s);
                char *comma = strchr(s, ',');
                if (!comma) break;
                s = comma + 1;
            }
        } else if (strcmp(argv[i], "--dump-prefix") == 0 && i + 1 < argc) {
            dump_prefix = argv[++i];
        } else if (strcmp(argv[i], "--verbose") == 0) {
            verbose_log = 1;
        } else if (strcmp(argv[i], "--benchmark") == 0) {
            benchmark_mode = 1;
        } else if (argv[i][0] != '-' && !input_path) {
            input_path = argv[i];
        }
    }

    if (num_frames <= 0 || num_frames > 1000000) {
        fprintf(stderr, "Invalid frame count: %d\n", num_frames);
        return 1;
    }

    crc32_init();

    if (input_path) {
        int n = load_input_script(input_path);
        if (n < 0) {
            fprintf(stderr, "Cannot open input script: %s\n", input_path);
            return 1;
        }
    }

    /* Load core */
    core_t core;
    memset(&core, 0, sizeof(core));
    if (core_load(&core, core_path) != 0)
        return 1;

    /* Check if core needs fullpath (both Neo Geo CD cores do) */
    struct retro_system_info sysinfo;
    memset(&sysinfo, 0, sizeof(sysinfo));
    core.get_system_info(&sysinfo);

    /* Initialize core */
    core.set_environment(env_cb);
    core.init();
    core.set_video_refresh(video_cb);
    core.set_audio_sample(audio_sample_cb);
    core.set_audio_sample_batch(audio_batch_cb);
    core.set_input_poll(input_poll_cb);
    core.set_input_state(input_state_cb);

    /* Load game - path only for need_fullpath cores (CHD files are huge) */
    struct retro_game_info info;
    memset(&info, 0, sizeof(info));
    info.path = rom_path;
    info.meta = NULL;

    if (sysinfo.need_fullpath) {
        /* Path-only: don't load file contents into memory */
        info.data = NULL;
        info.size = 0;
    } else {
        /* Load ROM data into memory */
        FILE *rf = fopen(rom_path, "rb");
        if (!rf) {
            fprintf(stderr, "Cannot open ROM: %s\n", rom_path);
            core_unload(&core);
            return 1;
        }
        fseek(rf, 0, SEEK_END);
        long rom_size = ftell(rf);
        fseek(rf, 0, SEEK_SET);
        uint8_t *rom_data = (uint8_t *)malloc((size_t)rom_size);
        if (!rom_data || fread(rom_data, 1, (size_t)rom_size, rf) != (size_t)rom_size) {
            fprintf(stderr, "Failed to read ROM\n");
            fclose(rf);
            free(rom_data);
            core_unload(&core);
            return 1;
        }
        fclose(rf);
        info.data = rom_data;
        info.size = (size_t)rom_size;
    }

    if (!core.load_game(&info)) {
        fprintf(stderr, "retro_load_game failed\n");
        if (info.data) free((void *)info.data);
        core_unload(&core);
        return 1;
    }

    /* Open output log */
    FILE *out = fopen(output_path, "wb");
    if (!out) {
        fprintf(stderr, "Cannot open output: %s\n", output_path);
        core.unload_game();
        if (info.data) free((void *)info.data);
        core_unload(&core);
        return 1;
    }

    /* Write header */
    avlog_header_t hdr = {AVLOG_MAGIC, AVLOG_VERSION, (uint32_t)num_frames, 0};
    fwrite(&hdr, sizeof(hdr), 1, out);

    /* Run frames */
    for (int f = 0; f < num_frames; f++) {
        apply_input_events((uint32_t)f);

        cur_video_crc = 0;
        cur_video_w = 0;
        cur_video_h = 0;
        cur_audio_crc = 0;
        cur_audio_frames = 0;
        cur_audio_energy = 0;
        audio_dft_pos = 0;
        cur_frame_num = f;

        core.run();

        uint64_t bands[NUM_AUDIO_BANDS] = {0};
        if (audio_dft_pos > 0)
            compute_band_energies(audio_dft_buf, audio_dft_pos, bands);

        avlog_entry_t entry;
        entry.frame_num = (uint32_t)f;
        entry.video_crc = cur_video_crc;
        entry.width = cur_video_w;
        entry.height = cur_video_h;
        entry.audio_crc = cur_audio_crc;
        entry.audio_frames = cur_audio_frames;
        if (cur_audio_frames > 0) {
            double rms = sqrt((double)cur_audio_energy / (cur_audio_frames * 2));
            entry.audio_energy = (uint32_t)(rms * 256.0);
        } else {
            entry.audio_energy = 0;
        }
        for (int b = 0; b < NUM_AUDIO_BANDS; b++)
            entry.band_energy[b] = (uint32_t)(bands[b] > 0xFFFFFFFF ? 0xFFFFFFFF : bands[b]);
        fwrite(&entry, sizeof(entry), 1, out);
    }

    fclose(out);
    core.unload_game();
    if (info.data) free((void *)info.data);
    core_unload(&core);

    fprintf(stderr, "OK: %d frames -> %s\n", num_frames, output_path);
    return 0;
}
