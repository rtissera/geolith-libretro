/*
Copyright (c) 2026 Romain Tisserand
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
   contributors may be used to endorse or promote products derived from
   this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#include <stdint.h>
#include <string.h>
#include <strings.h>

#include "geo.h"
#include "geo_disc.h"
#include "geo_chd.h"
#include "geo_cue.h"

#define BACKEND_NONE 0
#define BACKEND_CHD  1
#define BACKEND_CUE  2

static int backend = BACKEND_NONE;

static int detect_backend(const char *path) {
    const char *ext = strrchr(path, '.');
    if (!ext)
        return BACKEND_NONE;
    if (!strcasecmp(ext, ".chd"))
        return BACKEND_CHD;
    if (!strcasecmp(ext, ".cue"))
        return BACKEND_CUE;
    return BACKEND_NONE;
}

int geo_disc_open(const char *path) {
    backend = detect_backend(path);

    switch (backend) {
        case BACKEND_CHD:
            return geo_chd_open(path);
        case BACKEND_CUE:
            return geo_cue_open(path);
        default:
            geo_log(GEO_LOG_ERR, "Unsupported disc format: %s\n", path);
            return 0;
    }
}

void geo_disc_close(void) {
    switch (backend) {
        case BACKEND_CHD: geo_chd_close(); break;
        case BACKEND_CUE: geo_cue_close(); break;
    }
    backend = BACKEND_NONE;
}

int geo_disc_read_sector(uint32_t disc_lba, uint8_t *buf) {
    switch (backend) {
        case BACKEND_CHD: return geo_chd_read_sector(disc_lba, buf);
        case BACKEND_CUE: return geo_cue_read_sector(disc_lba, buf);
        default: return 0;
    }
}

int geo_disc_read_audio(uint32_t disc_lba, int16_t *buf) {
    switch (backend) {
        case BACKEND_CHD: return geo_chd_read_audio(disc_lba, buf);
        case BACKEND_CUE: return geo_cue_read_audio(disc_lba, buf);
        default: return 0;
    }
}

unsigned geo_disc_num_tracks(void) {
    switch (backend) {
        case BACKEND_CHD: return geo_chd_num_tracks();
        case BACKEND_CUE: return geo_cue_num_tracks();
        default: return 0;
    }
}

int geo_disc_track_is_audio(unsigned track) {
    switch (backend) {
        case BACKEND_CHD: return geo_chd_track_is_audio(track);
        case BACKEND_CUE: return geo_cue_track_is_audio(track);
        default: return 0;
    }
}

uint32_t geo_disc_track_start(unsigned track) {
    switch (backend) {
        case BACKEND_CHD: return geo_chd_track_start(track);
        case BACKEND_CUE: return geo_cue_track_start(track);
        default: return 0;
    }
}

uint32_t geo_disc_track_frames(unsigned track) {
    switch (backend) {
        case BACKEND_CHD: return geo_chd_track_frames(track);
        case BACKEND_CUE: return geo_cue_track_frames(track);
        default: return 0;
    }
}

uint32_t geo_disc_leadout(void) {
    switch (backend) {
        case BACKEND_CHD: return geo_chd_leadout();
        case BACKEND_CUE: return geo_cue_leadout();
        default: return 0;
    }
}

void geo_disc_lba_to_msf(uint32_t lba, uint8_t *m, uint8_t *s, uint8_t *f) {
    *m = lba / (60 * 75);
    *s = (lba / 75) % 60;
    *f = lba % 75;
}

uint32_t geo_disc_msf_to_lba(uint8_t m, uint8_t s, uint8_t f) {
    return (m * 60 * 75) + (s * 75) + f;
}
