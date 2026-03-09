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

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "m68k/m68k.h"
#include "m68k/m68kcpu.h"

#include "geo.h"
#include "geo_cd.h"
#include "geo_chd.h"
#include "geo_lspc.h"
#include "geo_m68k.h"
#include "geo_serial.h"
#include "geo_z80.h"

// CD RAM Buffers
static uint8_t pram[SIZE_2M];          // Program RAM (replaces P ROM + main RAM)
static uint8_t spr_dram[SIZE_4M];      // Sprite DRAM (replaces C ROM)
static uint8_t pcm_dram[SIZE_1M];      // PCM DRAM (replaces V ROMs)
static uint8_t z80_ram_cd[SIZE_64K];   // Z80 RAM (replaces M1 ROM + banking)
static uint8_t fix_ram[SIZE_128K];     // FIX layer RAM (replaces S ROM)
static uint8_t backup_ram[SIZE_8K];    // Backup RAM (replaces memory card area)

// ROM data pointer
static romdata_t *romdata = NULL;

// Vector table source: 0 = BIOS, 1 = Program RAM
static uint8_t vectable = 0;

// Transfer area (0xE00000) configuration
static uint8_t transfer_area = 0;      // 0=SPR, 1=PCM, 4=Z80, 5=FIX
static uint8_t spr_bank = 0;           // SPR bank (0-3, 1MB each)
static uint8_t pcm_bank = 0;           // PCM bank (0-1, 512K each)

// Layer enable flags
static uint8_t spr_disable = 0;
static uint8_t fix_disable = 0;
static uint8_t video_disable = 0;

// Bus request states
static uint8_t busreq_spr = 0;
static uint8_t busreq_pcm = 0;
static uint8_t busreq_z80 = 0;
static uint8_t busreq_fix = 0;

// Z80 reset/enable control
static uint8_t z80_enabled = 0;

// SRAM lock
static uint8_t reg_sramlock = 0;

// =========================================================================
// LC8951 CD Controller
// =========================================================================
typedef struct _lc8951_t {
    uint8_t regs[16];       // Registers 0-15
    uint8_t regptr;         // Current register pointer

    uint8_t buffer[SIZE_64K]; // 64K sector buffer (circular)
    uint16_t wal;           // Write address (where next sector goes)
    uint16_t ptl;           // Read pointer
    uint16_t dacl;          // Data address counter

    uint8_t ctrl0;
    uint8_t ctrl1;
    uint8_t ifstat;         // Interrupt flags
    uint8_t ifctrl;         // Interrupt control

    uint16_t dbc;           // Data byte count
    uint8_t head[4];        // Header (M, S, F, Mode)
    uint8_t stat0;          // Status 0 (CRCOK etc)

    uint8_t decoder_enabled;
    uint8_t transfer_busy;
} lc8951_t;

static lc8951_t lc;

// LC8951 IFSTAT bits
#define LC_IFSTAT_CMDI  0x80
#define LC_IFSTAT_DTEI  0x40
#define LC_IFSTAT_DECI  0x20
#define LC_IFSTAT_DTBSY 0x08
#define LC_IFSTAT_STBSY 0x04
#define LC_IFSTAT_DTEN  0x02

// LC8951 IFCTRL bits
#define LC_IFCTRL_CMDIEN  0x80
#define LC_IFCTRL_DTEIEN  0x40
#define LC_IFCTRL_DECIEN  0x20
#define LC_IFCTRL_DOUTEN  0x02

// LC8951 CTRL0 bits
#define LC_CTRL0_DECEN  0x80
#define LC_CTRL0_AUTORQ 0x10

// =========================================================================
// CD Communication Protocol
// =========================================================================
#define CD_STATUS_IDLE      0x00
#define CD_STATUS_PLAY      0x10
#define CD_STATUS_SEEK      0x20
#define CD_STATUS_SCAN      0x30
#define CD_STATUS_PAUSE     0x40
#define CD_STATUS_STOP      0x90
#define CD_STATUS_END       0xC0

typedef struct _cdcomm_t {
    uint8_t cmd[5];         // Command packet bytes
    uint8_t status[5];      // Response packet bytes
    uint8_t cmd_nibble;     // Current nibble in command (0-9)
    uint8_t stat_nibble;    // Current nibble in response (0-9)
    uint8_t strobe;         // Clock strobe state

    uint8_t drive_status;   // Current drive state
    uint32_t play_lba;      // Current play position (LBA)
    uint32_t target_lba;    // Target position
    uint8_t playing_audio;  // Is an audio track playing?
    uint8_t playing_data;   // Is a data track being read?
} cdcomm_t;

static cdcomm_t cd;

// =========================================================================
// DMA Engine
// =========================================================================
typedef struct _cddma_t {
    uint32_t src;
    uint32_t dst;
    uint32_t len;           // Transfer length (in words)
    uint16_t val;           // Fill value
    uint16_t config;        // DMA mode
    uint8_t enabled;
} cddma_t;

static cddma_t dma;

// =========================================================================
// CD IRQ state
// =========================================================================
static uint8_t cd_irq_mask = 0;        // FF000F acknowledge bits
static uint8_t cd_irq_enabled = 0;     // FF0181
static uint16_t irq_mask1 = 0;         // FF0002: CDROM interrupt mask
static uint16_t irq_mask2 = 0;         // FF0004: VBL interrupt mask (VITAL)
static int vbl_pending = 0;            // Latched VBL when irq_mask2 wasn't ready
uint32_t cd_irq_vector = 0;            // CD interrupt vector (0x54 or 0x58)

// Pending CD interrupt sources
#define CD_INT_DECODER      0x01
#define CD_INT_COMMUNICATION 0x02
uint8_t cd_pending_irq = 0;

// Re-evaluate CD IRQ level and vector based on pending sources
// Decoder has higher priority than communication (checked last = wins)
static void cd_update_interrupts(void) {
    int level = 0;

    // Priority order: decoder checked first, communication
    // checked last (communication wins when both pending)
    if (cd_pending_irq & CD_INT_DECODER) {
        level = 2;
        cd_irq_vector = 0x54;
    }
    if (cd_pending_irq & CD_INT_COMMUNICATION) {
        level = 2;
        cd_irq_vector = 0x58;
    }

    // Log when decoder is involved (separate counter from comm-only)
    if (level && (cd_pending_irq & CD_INT_DECODER)) {
        static int upd_dec_dbg = 0;
        if (++upd_dec_dbg <= 20)
            geo_log(GEO_LOG_DBG,
                "cd_update_int[DEC]: vec=0x%02x pend=%02x SR=%04x\n",
                cd_irq_vector, cd_pending_irq,
                m68k_get_reg(NULL, M68K_REG_SR));
    }

    if (level)
        geo_m68k_interrupt(IRQ_CD);
    else
        m68k_set_virq(IRQ_CD, 0);
}
static uint32_t cd_comm_counter = 0;   // Counter for 75Hz CD communication timer

// Bit-reverse table for CDDA sample registers
static const uint8_t bitrev[256] = {
    0x00,0x80,0x40,0xc0,0x20,0xa0,0x60,0xe0,
    0x10,0x90,0x50,0xd0,0x30,0xb0,0x70,0xf0,
    0x08,0x88,0x48,0xc8,0x28,0xa8,0x68,0xe8,
    0x18,0x98,0x58,0xd8,0x38,0xb8,0x78,0xf8,
    0x04,0x84,0x44,0xc4,0x24,0xa4,0x64,0xe4,
    0x14,0x94,0x54,0xd4,0x34,0xb4,0x74,0xf4,
    0x0c,0x8c,0x4c,0xcc,0x2c,0xac,0x6c,0xec,
    0x1c,0x9c,0x5c,0xdc,0x3c,0xbc,0x7c,0xfc,
    0x02,0x82,0x42,0xc2,0x22,0xa2,0x62,0xe2,
    0x12,0x92,0x52,0xd2,0x32,0xb2,0x72,0xf2,
    0x0a,0x8a,0x4a,0xca,0x2a,0xaa,0x6a,0xea,
    0x1a,0x9a,0x5a,0xda,0x3a,0xba,0x7a,0xfa,
    0x06,0x86,0x46,0xc6,0x26,0xa6,0x66,0xe6,
    0x16,0x96,0x56,0xd6,0x36,0xb6,0x76,0xf6,
    0x0e,0x8e,0x4e,0xce,0x2e,0xae,0x6e,0xee,
    0x1e,0x9e,0x5e,0xde,0x3e,0xbe,0x7e,0xfe,
    0x01,0x81,0x41,0xc1,0x21,0xa1,0x61,0xe1,
    0x11,0x91,0x51,0xd1,0x31,0xb1,0x71,0xf1,
    0x09,0x89,0x49,0xc9,0x29,0xa9,0x69,0xe9,
    0x19,0x99,0x59,0xd9,0x39,0xb9,0x79,0xf9,
    0x05,0x85,0x45,0xc5,0x25,0xa5,0x65,0xe5,
    0x15,0x95,0x55,0xd5,0x35,0xb5,0x75,0xf5,
    0x0d,0x8d,0x4d,0xcd,0x2d,0xad,0x6d,0xed,
    0x1d,0x9d,0x5d,0xdd,0x3d,0xbd,0x7d,0xfd,
    0x03,0x83,0x43,0xc3,0x23,0xa3,0x63,0xe3,
    0x13,0x93,0x53,0xd3,0x33,0xb3,0x73,0xf3,
    0x0b,0x8b,0x4b,0xcb,0x2b,0xab,0x6b,0xeb,
    0x1b,0x9b,0x5b,0xdb,0x3b,0xbb,0x7b,0xfb,
    0x07,0x87,0x47,0xc7,0x27,0xa7,0x67,0xe7,
    0x17,0x97,0x57,0xd7,0x37,0xb7,0x77,0xf7,
    0x0f,0x8f,0x4f,0xcf,0x2f,0xaf,0x6f,0xef,
    0x1f,0x9f,0x5f,0xdf,0x3f,0xbf,0x7f,0xff,
};

static inline uint16_t reverse_bits_16(uint16_t val) {
    return (bitrev[val & 0xff] << 8) | bitrev[val >> 8];
}

// =========================================================================
// CD timing
// =========================================================================
#define CD_SECTOR_RATE_IDLE (24000000 / 64)   // ~375000 master cycles (idle)
#define CD_SECTOR_RATE_1X   (24000000 / 75)   // ~320000 master cycles per sector
#define CD_SECTOR_RATE_2X   (24000000 / 150)  // ~160000 master cycles per sector

static uint32_t cd_sector_counter = 0;
static uint32_t cd_sector_rate = CD_SECTOR_RATE_1X;

static int speed_hack_enabled = 0;
static int bios_family = CD_BIOS_UNKNOWN;
static int sector_decoded_this_frame = 0;

// CDDA audio buffer — accumulates across multiple sector reads per video frame
#define CDDA_SAMPLES_PER_SECTOR 588
#define CDDA_BUF_MAXSAMPLES (CDDA_SAMPLES_PER_SECTOR * 3)
static int16_t cdda_buf[CDDA_BUF_MAXSAMPLES * 2]; // Stereo interleaved
static size_t cdda_samples = 0;
static uint8_t cdda_playing = 0;

// =========================================================================
// Helper functions
// =========================================================================
static inline uint8_t read08(uint8_t *ptr, uint32_t addr) {
    return ptr[addr];
}

static inline uint16_t read16(uint8_t *ptr, uint32_t addr) {
    return (ptr[addr] << 8) | ptr[addr + 1];
}

static inline void write08(uint8_t *ptr, uint32_t addr, uint8_t data) {
    ptr[addr] = data;
}

static inline void write16(uint8_t *ptr, uint32_t addr, uint16_t data) {
    ptr[addr + 1] = data & 0xff;
    ptr[addr] = data >> 8;
}

// BCD conversion helpers
static inline uint8_t to_bcd(uint8_t val) {
    return ((val / 10) << 4) | (val % 10);
}

static inline uint8_t from_bcd(uint8_t val) {
    return ((val >> 4) * 10) + (val & 0x0f);
}

// =========================================================================
// LC8951 Implementation
// =========================================================================
static void lc8951_reset(void) {
    memset(&lc, 0, sizeof(lc));
    lc.ifstat = 0xff; // All interrupt flags cleared (active low)
    // WAL/WAH initialized to 0x0930 (2352 = one raw sector size)
    lc.wal = 0x0930;
}

static uint8_t lc8951_reg_read(void) {
    uint8_t reg = lc.regptr;
    uint8_t val = 0;

    // Auto-increment except register 0
    if (lc.regptr > 0) {
        lc.regptr = (lc.regptr + 1) & 0x0f;
        if (lc.regptr == 0)
            lc.regptr = 1; // Skip 0 on wrap
    }

    switch (reg) {
        case 0x00: val = 0; break; // COMIN - not readable
        case 0x01: val = lc.ifstat; break;
        case 0x02: val = lc.dbc & 0xff; break;
        case 0x03: val = (lc.dbc >> 8) & 0x0f; break;
        case 0x04: // HEAD0 (returns 0 when SHDREN is set)
            val = (lc.ctrl1 & 0x01) ? 0 : lc.head[0];
            break;
        case 0x05: // HEAD1
            val = (lc.ctrl1 & 0x01) ? 0 : lc.head[1];
            break;
        case 0x06: // HEAD2
            val = (lc.ctrl1 & 0x01) ? 0 : lc.head[2];
            break;
        case 0x07: // HEAD3
            val = (lc.ctrl1 & 0x01) ? 0 : lc.head[3];
            break;
        case 0x08: val = lc.ptl & 0xff; break;
        case 0x09: val = (lc.ptl >> 8) & 0xff; break;
        case 0x0a: val = lc.wal & 0xff; break;
        case 0x0b: val = (lc.wal >> 8) & 0xff; break;
        case 0x0c: val = lc.stat0; break;
        case 0x0d: // STAT1
        case 0x0e: // STAT2
            val = 0; break;
        case 0x0f: // STAT3 - keep DECI pending on read
            lc.ifstat &= ~LC_IFSTAT_DECI;
            val = 0; break;
    }

    // Log reads of key registers only during playback (disabled for perf)
    //if ((cd.playing_data || cd.playing_audio) && (reg == 0x01 || reg >= 0x08))
    //    fprintf(stderr, "LC8951 read reg=%02x val=%02x @ PC=%06x\n",
    //        reg, val, m68k_get_reg(NULL, M68K_REG_PPC));

    return val;
}

static void lc8951_reg_write(uint8_t val) {
    uint8_t reg = lc.regptr;

    //if (cd.playing_data || cd.playing_audio)
    //    fprintf(stderr, "LC8951 write reg=%02x val=%02x @ PC=%06x\n",
    //        reg, val, m68k_get_reg(NULL, M68K_REG_PPC));

    // Auto-increment except register 0
    if (lc.regptr > 0) {
        lc.regptr = (lc.regptr + 1) & 0x0f;
        if (lc.regptr == 0)
            lc.regptr = 1;
    }

    switch (reg) {
        case 0x00: // SBOUT - not used
            break;
        case 0x01: // IFCTRL
            lc.ifctrl = val;
            break;
        case 0x02: // DBCL
            lc.dbc = (lc.dbc & 0xff00) | val;
            break;
        case 0x03: // DBCH
            lc.dbc = (lc.dbc & 0x00ff) | ((val & 0x0f) << 8);
            break;
        case 0x04: // DACL
            lc.dacl = (lc.dacl & 0xff00) | val;
            break;
        case 0x05: // DACH
            lc.dacl = (lc.dacl & 0x00ff) | (val << 8);
            break;
        case 0x06: // DTRG - triggers data transfer
            if (lc.ifctrl & LC_IFCTRL_DOUTEN)
                lc.ifstat &= ~LC_IFSTAT_DTBSY;
            lc.transfer_busy = 1;
            break;
        case 0x07: // DTACK - acknowledge transfer completion
            lc.ifstat |= LC_IFSTAT_DTEI; // Clear DTEI flag
            break;
        // NOTE: LC8951 write registers 0x08-0x0E differ from read registers!
        // Write: WAL(8) WAH(9) CTRL0(A) CTRL1(B) PTL(C) PTH(D) CTRL2(E)
        // Read:  PTL(8) PTH(9) WAL(A)   WAH(B)   STAT0-3(C-F)
        case 0x08: // WAL (write side)
            lc.wal = (lc.wal & 0xff00) | val;
            break;
        case 0x09: // WAH (write side)
            lc.wal = (lc.wal & 0x00ff) | (val << 8);
            break;
        case 0x0a: // CTRL0 (write side)
            lc.ctrl0 = val;
            lc.decoder_enabled = (val & LC_CTRL0_DECEN) ? 1 : 0;
            break;
        case 0x0b: // CTRL1 (write side)
            lc.ctrl1 = val;
            break;
        case 0x0c: // PTL (write side)
            lc.ptl = (lc.ptl & 0xff00) | val;
            break;
        case 0x0d: // PTH (write side)
            lc.ptl = (lc.ptl & 0x00ff) | (val << 8);
            break;
        case 0x0e: // CTRL2 (write side, no effect)
            break;
        case 0x0f: // Reset
            lc8951_reset();
            break;
    }
}

static void lc8951_sector_decoded(void) {
    // If decoder not enabled, nothing to do
    if (!lc.decoder_enabled)
        return;
    {
        static uint32_t sec_count = 0;
        if (++sec_count <= 20 || (sec_count % 500 == 0))
            geo_log(GEO_LOG_DBG, "sector_decoded #%u: lba=%u\n", sec_count, cd.play_lba);
    }

    // Update head registers with current position MSF
    uint8_t m, s, f;
    geo_chd_lba_to_msf(cd.play_lba + 150, &m, &s, &f);
    lc.head[0] = to_bcd(m);
    lc.head[1] = to_bcd(s);
    lc.head[2] = to_bcd(f);
    lc.head[3] = 0x01; // Mode 1

    // If current track is not data, nothing more to do
    if (cd.playing_audio)
        return;

    // Simplified LC8951: write 2048 bytes of user data at buffer[0]
    // DMA always reads from buffer[0], ignoring DACL register
    uint8_t sector[GEO_CHD_DATA_SIZE];
    if (geo_chd_read_sector(cd.play_lba, sector))
        memcpy(lc.buffer, sector, GEO_CHD_DATA_SIZE);

    // Advance write address and pointer by one raw sector (for BIOS register reads)
    lc.wal += GEO_CHD_SECTOR_SIZE;
    lc.ptl += GEO_CHD_SECTOR_SIZE;

    // Set STAT registers
    lc.stat0 = 0x80; // CRCOK

    // Set DECI flag (sector decoded interrupt pending)
    lc.ifstat &= ~LC_IFSTAT_DECI;
}

static void lc8951_end_transfer(void) {
    // Set DTBSY, update DAC/DBC, no interrupt
    lc.ifstat |= LC_IFSTAT_DTBSY;

    // DAC += DBC + 1 (advance data address counter)
    lc.dacl += lc.dbc + 1;

    // Clear DBC
    lc.dbc = 0;
}

// =========================================================================
// CD Communication Protocol
// =========================================================================
static void cd_comm_build_response(void);

static void cd_comm_reset(void) {
    memset(&cd, 0, sizeof(cd));
    cd.drive_status = CD_STATUS_IDLE;
    cd.cmd_nibble = 0;
    cd.stat_nibble = 9;
    cd.strobe = 1;
    // Set valid checksum on initial response packet
    cd.status[0] = cd.drive_status;
    cd_comm_build_response();
}

static uint8_t cd_comm_checksum(uint8_t *pkt) {
    uint8_t sum = 0;
    for (int i = 0; i < 4; ++i) {
        sum += (pkt[i] >> 4);
        sum += (pkt[i] & 0x0f);
    }
    sum += (pkt[4] >> 4);
    sum += 5;
    return (~sum) & 0x0f;
}

static void cd_comm_build_response(void) {
    cd.status[4] = (cd.status[4] & 0xf0) | cd_comm_checksum(cd.status);
}

static void cd_comm_process_command(void) {
    // Verify command checksum
    uint8_t expected = cd_comm_checksum(cd.cmd);
    if ((cd.cmd[4] & 0x0f) != expected) {
        geo_log(GEO_LOG_WRN, "CD command checksum mismatch\n");
        cd.status[0] = cd.drive_status;
        cd.status[1] = 0;
        cd.status[2] = 0;
        cd.status[3] = 0;
        cd.status[4] = 0;
        cd_comm_build_response();
        return;
    }

    uint8_t m, s, f;

    static int prot_done = 0;

    if (cd.cmd[0] != 0x00) {
        geo_log(GEO_LOG_DBG, "CD CMD: %02x %02x %02x %02x %02x\n",
            cd.cmd[0], cd.cmd[1], cd.cmd[2], cd.cmd[3], cd.cmd[4]);
    }

    switch (cd.cmd[0]) {
        case 0x00: { // Status
            cd.status[0] = (cd.status[0] & 0x0f) | cd.drive_status;
            extern uint32_t cd_vbl_counter;
            static int stat_count = 0;
            stat_count++;
            // Read BIOS state variables (a5=0x108000)
            uint8_t b76ac = pram[0x10F6AC];
            uint8_t b766a = pram[0x10F66A];
            uint8_t b7650 = pram[0x10F650];
            uint8_t b7651 = pram[0x10F651];
            (void)stat_count; (void)b76ac; (void)b766a; (void)b7650; (void)b7651;
            break;
        }

        case 0x10: // Stop
            cd.playing_audio = 0;
            cd.playing_data = 0;
            cdda_playing = 0;
            cd.drive_status = CD_STATUS_IDLE;
            cd.status[0] = cd.drive_status;
            cd.status[1] = 0;
            cd.status[2] = 0;
            cd.status[3] = 0;
            cd.status[4] = 0;
            break;

        case 0x20: { // Query TOC/position info
            uint8_t subcmd = cd.cmd[1] & 0x0f;
            if ((cd.drive_status == CD_STATUS_IDLE) &&
                geo_chd_num_tracks() > 0)
                cd.drive_status = CD_STATUS_STOP;

            switch (subcmd) {
                case 0x00: { // Current absolute position
                    geo_chd_lba_to_msf(cd.play_lba + 150, &m, &s, &f);
                    cd.status[0] = cd.drive_status;
                    cd.status[1] = to_bcd(m);
                    cd.status[2] = to_bcd(s);
                    cd.status[3] = to_bcd(f);
                    uint8_t is_data = 0;
                    for (unsigned i = 0; i < geo_chd_num_tracks(); ++i) {
                        if (cd.play_lba >= geo_chd_track_start(i + 1))
                            is_data = !geo_chd_track_is_audio(i + 1);
                    }
                    cd.status[4] = is_data ? 0x40 : 0x00;
                    break;
                }
                case 0x01: { // Current relative position
                    geo_chd_lba_to_msf(cd.play_lba + 150, &m, &s, &f);
                    cd.status[0] = cd.drive_status | 0x01;
                    cd.status[1] = to_bcd(m);
                    cd.status[2] = to_bcd(s);
                    cd.status[3] = to_bcd(f);
                    uint8_t is_data = 0;
                    for (unsigned i = 0; i < geo_chd_num_tracks(); ++i) {
                        if (cd.play_lba >= geo_chd_track_start(i + 1))
                            is_data = !geo_chd_track_is_audio(i + 1);
                    }
                    cd.status[4] = is_data ? 0x40 : 0x00;
                    break;
                }
                case 0x02: { // Current track
                    uint8_t track = 1;
                    for (unsigned i = 0; i < geo_chd_num_tracks(); ++i) {
                        if (cd.play_lba >= geo_chd_track_start(i + 1))
                            track = i + 1;
                    }
                    uint8_t is_data = !geo_chd_track_is_audio(track);
                    cd.status[0] = cd.drive_status | 0x02;
                    cd.status[1] = to_bcd(track);
                    cd.status[2] = to_bcd(1); // index
                    cd.status[3] = 0;
                    cd.status[4] = is_data ? 0x40 : 0x00;
                    break;
                }
                case 0x03: { // Leadout address
                    uint32_t lo = geo_chd_leadout();
                    geo_chd_lba_to_msf(lo + 150, &m, &s, &f);
                    cd.status[0] = cd.drive_status | 0x03;
                    cd.status[1] = to_bcd(m);
                    cd.status[2] = to_bcd(s);
                    cd.status[3] = to_bcd(f);
                    cd.status[4] = 0;
                    break;
                }
                case 0x04: { // First and last track
                    cd.status[0] = cd.drive_status | 0x04;
                    cd.status[1] = to_bcd(1);
                    cd.status[2] = to_bcd(geo_chd_num_tracks());
                    cd.status[3] = 0;
                    cd.status[4] = 0;
                    break;
                }
                case 0x05: { // Track N start time
                    uint8_t track = from_bcd(cd.cmd[2]);
                    uint32_t start = geo_chd_track_start(track);
                    geo_chd_lba_to_msf(start + 150, &m, &s, &f);
                    uint8_t is_data = !geo_chd_track_is_audio(track);
                    cd.status[0] = cd.drive_status | 0x05;
                    cd.status[1] = to_bcd(m);
                    cd.status[2] = to_bcd(s);
                    cd.status[3] = to_bcd(f) | (is_data ? 0x80 : 0x00);
                    cd.status[4] = cd.cmd[2] << 4;
                    break;
                }
                case 0x06: { // End of disc check
                    uint32_t lo = geo_chd_leadout();
                    if (cd.play_lba >= lo)
                        cd.drive_status = CD_STATUS_END;
                    cd.status[0] = cd.drive_status | 0x06;
                    cd.status[1] = 0;
                    cd.status[2] = 0;
                    cd.status[3] = 0;
                    uint8_t is_data = 0;
                    for (unsigned i = 0; i < geo_chd_num_tracks(); ++i) {
                        if (cd.play_lba >= geo_chd_track_start(i + 1))
                            is_data = !geo_chd_track_is_audio(i + 1);
                    }
                    cd.status[4] = is_data ? 0x40 : 0x00;
                    break;
                }
                case 0x07: // CDZ disc recognition (copy protection)
                    cd.status[0] = cd.drive_status | 0x07;
                    cd.status[1] = 0x02;
                    cd.status[2] = 0;
                    cd.status[3] = 0;
                    cd.status[4] = 0;
                    prot_done = 1;
                    geo_log(GEO_LOG_DBG, "Protection check done\n");
                    break;
                default:
                    cd.status[0] = cd.drive_status;
                    cd.status[1] = 0;
                    cd.status[2] = 0;
                    cd.status[3] = 0;
                    cd.status[4] = 0;
                    break;
            }
            break;
        }

        case 0x30: { // Play (from MSF)
            m = from_bcd(cd.cmd[1]);
            s = from_bcd(cd.cmd[2]);
            f = from_bcd(cd.cmd[3]);
            uint32_t lba = geo_chd_msf_to_lba(m, s, f);
            if (lba >= 150)
                lba -= 150;

            cd.play_lba = lba;
            cd.target_lba = lba;

            unsigned track = 0;
            for (unsigned i = 0; i < geo_chd_num_tracks(); ++i) {
                if (lba >= geo_chd_track_start(i + 1))
                    track = i + 1;
            }

            if (track > 0 && geo_chd_track_is_audio(track)) {
                cd.playing_audio = 1;
                cd.playing_data = 0;
                cdda_playing = 1;
            } else {
                cd.playing_audio = 0;
                cd.playing_data = 1;
                cdda_playing = 0;
            }

            geo_log(GEO_LOG_DBG, "Play: lba=%u data=%d audio=%d PC=%06x\n",
                cd.play_lba, cd.playing_data, cd.playing_audio,
                m68k_get_reg(NULL, M68K_REG_PPC));
            cd.drive_status = CD_STATUS_PLAY;
            cd.status[0] = cd.drive_status | 0x02;
            cd.status[1] = to_bcd(track);
            cd.status[2] = 0;
            cd.status[3] = 0;
            cd.status[4] = 0;
            break;
        }

        case 0x40: // Seek
            cd.playing_audio = 0;
            cd.playing_data = 0;
            cdda_playing = 0;
            cd.drive_status = CD_STATUS_PAUSE;
            cd.status[0] = CD_STATUS_SEEK;
            cd.status[1] = 0;
            cd.status[2] = 0;
            cd.status[3] = 0;
            cd.status[4] = 0;
            break;

        case 0x50: // Unknown (CDZ only)
            cd.status[0] = cd.drive_status;
            break;

        case 0x60: // Pause
            cd.playing_audio = 0;
            cd.playing_data = 0;
            cdda_playing = 0;
            cd.drive_status = CD_STATUS_PAUSE;
            cd.status[0] = cd.drive_status;
            break;

        case 0x70: // Resume
            if (cd.playing_audio || cd.playing_data) {
                cd.drive_status = CD_STATUS_PLAY;
                if (cd.playing_audio)
                    cdda_playing = 1;
            }
            cd.status[0] = cd.drive_status;
            break;

        case 0x80: // Scan forward
            cd.play_lba += 75;
            cd.drive_status = CD_STATUS_PLAY;
            cd.status[0] = CD_STATUS_SCAN;
            break;

        case 0x90: // Scan backward
            if (cd.play_lba >= 75)
                cd.play_lba -= 75;
            else
                cd.play_lba = 0;
            cd.drive_status = CD_STATUS_PLAY;
            cd.status[0] = CD_STATUS_SCAN;
            break;

        case 0xB0: { // Move to track
            uint8_t track = from_bcd(cd.cmd[1]);
            if (track >= 1 && track <= geo_chd_num_tracks()) {
                cd.play_lba = geo_chd_track_start(track);
            }
            cd.drive_status = CD_STATUS_PLAY;
            cd.status[0] = cd.drive_status | 0x02;
            cd.status[1] = to_bcd(track);
            cd.status[2] = 0;
            cd.status[3] = 0;
            cd.status[4] = 0;
            break;
        }

        // Protection-related commands (return status only)
        case 0x02: case 0x13: case 0x23: case 0x33:
        case 0x43: case 0x53: case 0x63: case 0xE2:
            cd.status[0] = cd.drive_status;
            cd.status[1] = 0;
            cd.status[2] = 0;
            cd.status[3] = 0;
            cd.status[4] = 0;
            if (cd.cmd[0] == 0xE2)
                prot_done = 2; // Phase 3: post-protection sequence
            break;

        default:
            geo_log(GEO_LOG_DBG, "Unknown CD command: %02x\n", cd.cmd[0]);
            cd.status[0] = cd.drive_status;
            cd.status[1] = 0;
            cd.status[2] = 0;
            cd.status[3] = 0;
            cd.status[4] = 0;
            break;
    }

    cd_comm_build_response();
}

// =========================================================================
// DMA Implementation
// =========================================================================
// Destination types for DMA
#define DMA_DEST_RAM     0
#define DMA_DEST_MAPPED  1
#define DMA_DEST_PALETTE 2

static int cd_dma_resolve_dest(uint32_t address, uint8_t **dst_ptr, uint32_t *dst_mask) {
    address &= 0xffffff;
    if (address < 0x200000) {
        // Program RAM
        *dst_ptr = pram;
        *dst_mask = SIZE_2M - 1;
        return DMA_DEST_RAM;
    } else if (address >= 0x400000 && address < 0x800000) {
        // Palette RAM — handled via geo_lspc_palram_wr16 for color conversion
        *dst_ptr = (uint8_t*)1; // non-NULL sentinel
        *dst_mask = 0x1fff; // 8K palette entries (16KB / 2)
        return DMA_DEST_PALETTE;
    } else if (address >= 0xe00000 && address <= 0xefffff) {
        // Mapped area — route based on transfer_area register
        switch (transfer_area) {
            case 0: // SPR
                *dst_ptr = spr_dram + (spr_bank * SIZE_1M);
                *dst_mask = SIZE_1M - 1;
                break;
            case 1: // PCM
                *dst_ptr = pcm_dram + (pcm_bank * SIZE_512K);
                *dst_mask = SIZE_512K - 1;
                break;
            case 4: // Z80
                *dst_ptr = z80_ram_cd;
                *dst_mask = SIZE_64K - 1;
                break;
            case 5: // FIX
                *dst_ptr = fix_ram;
                *dst_mask = SIZE_128K - 1;
                break;
            default:
                *dst_ptr = NULL;
                return DMA_DEST_RAM;
        }
        return DMA_DEST_MAPPED;
    } else {
        *dst_ptr = NULL;
        return DMA_DEST_RAM;
    }
}

// Write a 16-bit word to the DMA destination, advancing offset by 2.
// Handles mapped area address transformations for FIX/Z80/PCM (addr >> 1, low byte).
static void dma_write_word(uint8_t *ptr, uint32_t mask, uint32_t *offset,
                           uint16_t data, int dest_type) {
    switch (dest_type) {
        case DMA_DEST_MAPPED:
            switch (transfer_area) {
                case 0: { // SPR - big-endian word write
                    uint32_t addr = *offset & (mask & ~1u);
                    ptr[addr] = (data >> 8) & 0xff;
                    ptr[addr + 1] = data & 0xff;
                    break;
                }
                case 1: // PCM - address >> 1, low byte
                case 4: // Z80 - address >> 1, low byte
                case 5: { // FIX - address >> 1, low byte
                    uint32_t addr = (*offset >> 1) & mask;
                    ptr[addr] = data & 0xff;
                    break;
                }
            }
            break;
        case DMA_DEST_PALETTE:
            // Route through LSPC palette write for proper color conversion
            geo_lspc_palram_wr16(*offset, data);
            break;
        default:
            // Program RAM - big-endian word write
            ptr[*offset & mask] = (data >> 8) & 0xff;
            ptr[(*offset + 1) & mask] = data & 0xff;
            break;
    }
    *offset += 2;
}

static void cd_dma_execute(void) {
    if (!dma.enabled || dma.len == 0)
        return;

    uint8_t *dst_ptr = NULL;
    uint32_t dst_mask = 0;

    int dest_type = cd_dma_resolve_dest(dma.dst, &dst_ptr, &dst_mask);
    if (!dst_ptr) {
        geo_log(GEO_LOG_WRN, "DMA to unknown address: %06x area=%u\n", dma.dst, transfer_area);
        dma.enabled = 0;
        return;
    }

    switch (dma.config) {
        case 0xffc5:
        case 0xff89: {
            // Copy from LC8951 buffer to destination
            // Reads big-endian words from LC8951 buffer, writes via mapped handler
            uint16_t *source = (uint16_t*)lc.buffer;
            uint32_t dst = dma.dst;
            uint32_t len = dma.len;
            if (len > 0x400) len = 0x400;
            for (uint32_t i = 0; i < len; ++i) {
                uint16_t data = (source[i] >> 8) | (source[i] << 8); // big-endian
                dma_write_word(dst_ptr, dst_mask, &dst, data, dest_type);
            }
            lc8951_end_transfer();
            break;
        }
        case 0xfc2d: {
            // Copy from LC8951 buffer, odd bytes
            // Reads word from LC8951 buffer, writes 2 words per iteration
            // (high byte as word, low byte as word) through mapped handler
            uint16_t *source = (uint16_t*)lc.buffer;
            uint32_t dst = dma.dst;
            uint32_t len = dma.len;
            if (len > 0x400) len = 0x400;
            for (uint32_t i = 0; i < len; ++i) {
                uint16_t data = (source[i] >> 8) | (source[i] << 8); // big-endian
                dma_write_word(dst_ptr, dst_mask, &dst, data >> 8, dest_type);
                dma_write_word(dst_ptr, dst_mask, &dst, data, dest_type);
            }
            lc8951_end_transfer();
            break;
        }
        case 0xfe3d:
        case 0xfe6d: {
            // RAM to RAM copy — source and destination registers are REVERSED
            // Reads word from source, writes word to dest via mapped handler
            uint32_t src = dma.dst;   // Hardware "destination" register is actually source
            uint32_t dst = dma.src;   // Hardware "source" register is actually destination
            // Re-resolve destination from the actual destination address
            dest_type = cd_dma_resolve_dest(dst, &dst_ptr, &dst_mask);
            if (!dst_ptr) {
                geo_log(GEO_LOG_WRN, "DMA fe3d to unknown address: %06x\n", dst);
                break;
            }

            for (uint32_t i = 0; i < dma.len; ++i) {
                uint16_t w = read16(pram, src & (SIZE_2M - 1));
                dma_write_word(dst_ptr, dst_mask, &dst, w, dest_type);
                src += 2;
            }
            break;
        }
        case 0xfef5: {
            // Fill with incrementing addresses
            // Writes 2 words per iteration (addr>>16, addr), address increments by 4
            uint32_t address = dma.dst;
            uint32_t dst = dma.dst;
            for (uint32_t i = 0; i < dma.len; ++i) {
                dma_write_word(dst_ptr, dst_mask, &dst, (address >> 16), dest_type);
                dma_write_word(dst_ptr, dst_mask, &dst, address, dest_type);
                address += 4;
            }
            break;
        }
        case 0xffcd:
        case 0xffdd: {
            // Pattern fill
            // Writes pattern word per iteration via mapped handler
            uint32_t dst = dma.dst;
            for (uint32_t i = 0; i < dma.len; ++i) {
                dma_write_word(dst_ptr, dst_mask, &dst, dma.val, dest_type);
            }
            break;
        }
        case 0xe2dd:
        case 0xf2dd: {
            // Copy odd bytes — source and destination registers are REVERSED
            // Reads word, writes BYTE_SWAP_16(data) then data (2 words per iteration)
            uint32_t src = dma.dst;   // Hardware "destination" is actually source
            uint32_t dst = dma.src;   // Hardware "source" is actually destination

            // Re-resolve destination from the actual destination address
            dest_type = cd_dma_resolve_dest(dst, &dst_ptr, &dst_mask);
            if (!dst_ptr) {
                geo_log(GEO_LOG_WRN, "DMA e2dd to unknown address: %06x\n", dst);
                break;
            }

            for (uint32_t i = 0; i < dma.len; ++i) {
                uint16_t data = read16(pram, src & (SIZE_2M - 1));
                uint16_t swapped = (data >> 8) | (data << 8);
                dma_write_word(dst_ptr, dst_mask, &dst, swapped, dest_type);
                dma_write_word(dst_ptr, dst_mask, &dst, data, dest_type);
                src += 2;
            }
            break;
        }
        case 0xcffd: {
            // Fill odd bytes with incrementing addresses
            // Writes 4 words per iteration (addr bytes high to low), address increments by 8
            uint32_t address = dma.dst;
            uint32_t dst = dma.dst;
            for (uint32_t i = 0; i < dma.len; ++i) {
                dma_write_word(dst_ptr, dst_mask, &dst, (address >> 24), dest_type);
                dma_write_word(dst_ptr, dst_mask, &dst, (address >> 16), dest_type);
                dma_write_word(dst_ptr, dst_mask, &dst, (address >> 8), dest_type);
                dma_write_word(dst_ptr, dst_mask, &dst, address, dest_type);
                address += 8;
            }
            break;
        }
        default:
            geo_log(GEO_LOG_WRN, "Unknown DMA config: %04x\n", dma.config);
            break;
    }

    dma.enabled = 0;
}

// =========================================================================
// CD Register Read/Write (0xFF0000 - 0xFF01FF)
// =========================================================================
static uint8_t cd_reg_read_8(uint32_t addr) {
    addr &= 0x01ff;

    switch (addr) {
        case 0x000f: // IRQ Acknowledge status
            return cd_irq_mask;

        case 0x0017: // Unknown (front loader BIOS)
            return 0x00;

        case 0x0061: // DMA status (bit 6 = busy)
            return dma.enabled ? 0x40 : 0x00;

        case 0x0103: // LC8951 register data
            return lc8951_reg_read();

        case 0x0161: { // CD communication response read
            uint8_t nibble;
            if (cd.stat_nibble & 1)
                nibble = cd.status[cd.stat_nibble >> 1] & 0x0f;
            else
                nibble = (cd.status[cd.stat_nibble >> 1] >> 4) & 0x0f;
            return nibble | (cd.strobe << 4);
        }

        case 0x0167: // CD status lines
            return 0x00;
    }

    geo_log(GEO_LOG_DBG, "CD reg read 8: FF%04x @ PC=%06x\n",
        addr, m68k_get_reg(NULL, M68K_REG_PPC));
    return 0x00;
}

static uint16_t cd_reg_read_16(uint32_t addr) {
    addr &= 0x01ff;

    switch (addr) {
        case 0x0004: // VBL Interrupt Mask (VITAL - saved/restored on stack)
            return irq_mask2;

        case 0x011c: { // System Config
            // 00ST00NN 00000000
            // S = show eject button, N = nationality, T = tray
            uint16_t nat = (~geo_get_region()) & 0x07;
            uint16_t tray = 0x10; // CD: tray closed = 1
            if (geo_get_system() == SYSTEM_CDZ)
                tray = 0x00; // CDZ: inverted (0 = closed)
            return (nat | tray) << 8;
        }

        case 0x0188: // CDDA left channel (bit-reversed)
            if (cdda_playing && cdda_samples > 0)
                return reverse_bits_16((uint16_t)cdda_buf[0]);
            return 0;

        case 0x018a: // CDDA right channel (bit-reversed)
            if (cdda_playing && cdda_samples > 0)
                return reverse_bits_16((uint16_t)cdda_buf[1]);
            return 0;
    }

    // Fall through to byte handler for registers not word-specific
    uint8_t hi = cd_reg_read_8(addr);
    uint8_t lo = cd_reg_read_8(addr + 1);
    return (hi << 8) | lo;
}

static void cd_reg_write_8(uint32_t addr, uint8_t val) {
    addr &= 0x01ff;

    switch (addr) {
        case 0x000d: // Unknown registers (silently accepted)
        case 0x000e:
        case 0x0011:
        case 0x0015:
        case 0x0017:
        case 0x0167:
        case 0x016d:
            return;

        case 0x000f: { // IRQ Acknowledge
            if (val & 0x20) {
                cd_irq_mask &= ~0x20;
                cd_pending_irq &= ~CD_INT_DECODER;
            }
            if (val & 0x10) {
                cd_irq_mask &= ~0x10;
                cd_pending_irq &= ~CD_INT_COMMUNICATION;
            }
            cd_update_interrupts();
            return;
        }

        case 0x0061: // DMA control
            if (val == 0x40) {
                uint8_t handler = pram[0x10FE0F]; // 7E0F(a5) where a5=0x108000
                geo_log(GEO_LOG_DBG, "DMA: dst=%06x len=%04x cfg=%04x src=%06x h=%u buf=%02x%02x%02x%02x\n",
                    dma.dst, dma.len, dma.config, dma.src, handler,
                    lc.buffer[0], lc.buffer[1], lc.buffer[2], lc.buffer[3]);
                dma.enabled = 1;
                cd_dma_execute();
            } else if (val == 0x00) {
                dma.enabled = 0;
                memset(&dma, 0, sizeof(dma));
            }
            return;

        case 0x0101: // LC8951 register select
            lc.regptr = val & 0x0f;
            return;

        case 0x0103: // LC8951 register write
            lc8951_reg_write(val);
            return;

        case 0x0105: // Transfer area select
            transfer_area = val & 0x07;
            return;

        case 0x0111: // SPR enable/disable
            spr_disable = (val != 0);
            return;
        case 0x0115: // FIX enable/disable
            fix_disable = (val != 0);
            return;
        case 0x0119: // Video enable/disable
            video_disable = (val != 0);
            return;

        case 0x0121: busreq_spr = 1; return;
        case 0x0131: busreq_spr = 0; return;
        case 0x0123: busreq_pcm = 1; return;
        case 0x0133: busreq_pcm = 0; return;
        case 0x0127: busreq_z80 = 1; return;
        case 0x0137: busreq_z80 = 0; return;
        case 0x0129: busreq_fix = 1; return;
        case 0x0139: busreq_fix = 0; return;

        case 0x0141: busreq_spr = 0; return; // SPR bus release
        case 0x0143: busreq_pcm = 0; return; // PCM bus release
        case 0x0147: busreq_z80 = 0; return; // Z80 bus release
        case 0x0149: busreq_fix = 0; return; // FIX bus release

        case 0x0163: { // CD command write
            if (cd.cmd_nibble >= 10)
                cd.cmd_nibble = 0;
            uint8_t byte_idx = cd.cmd_nibble / 2;
            if (cd.cmd_nibble & 1)
                cd.cmd[byte_idx] = (cd.cmd[byte_idx] & 0xf0) | (val & 0x0f);
            else
                cd.cmd[byte_idx] = (cd.cmd[byte_idx] & 0x0f) | ((val & 0x0f) << 4);
            return;
        }

        case 0x0165: { // CD communication pointer control
            switch (val) {
                case 0x00: break; // No-op
                case 0x01: // Advance command pointer
                    cd.cmd_nibble = (cd.cmd_nibble + 1) % 10;
                    if (cd.cmd_nibble == 0) {
                        // 10 nibbles received, command complete
                        cd_comm_process_command();
                    }
                    break;
                case 0x02: // Advance response pointer
                    cd.strobe = 0;
                    cd.stat_nibble = (cd.stat_nibble + 1) % 10;
                    break;
                case 0x03: // Set strobe
                    cd.strobe = 1;
                    break;
            }
            return;
        }

        case 0x016f: // Watchdog timer: 0x00=enable, 0x01=disable
            geo_watchdog_enable(val == 0);
            return;

        case 0x0181: { // CD communication nReset (active low)
            cd_irq_enabled = (val != 0);
            // Reset packet pointers (commandPointer=0, responsePointer=9, strobe=1)
            cd.cmd_nibble = 0;
            cd.stat_nibble = 9;
            cd.strobe = 1;
            return;
        }
        case 0x0183: // Z80 reset/enable
            if (val == 0x00) {
                z80_enabled = 0;
            } else {
                z80_enabled = 1;
                geo_z80_reset();
            }
            return;

        case 0x01a1: // SPR bank select
            spr_bank = val & 0x03;
            return;

        case 0x01a3: // PCM bank select
            pcm_bank = val & 0x01;
            return;
    }

    geo_log(GEO_LOG_DBG, "CD reg write 8: FF%04x = %02x @ PC=%06x\n",
        addr, val, m68k_get_reg(NULL, M68K_REG_PPC));
}

static void cd_reg_write_16(uint32_t addr, uint16_t val) {
    addr &= 0x01ff;

    switch (addr) {
        case 0x0000: // CD-ROM drive reset
            cd.playing_audio = 0;
            cd.playing_data = 0;
            cdda_playing = 0;
            cd.drive_status = CD_STATUS_IDLE;
            return;

        case 0x0002: // CDROM Interrupt Mask
            irq_mask1 = val;
            return;

        case 0x0004: // VBL Interrupt Mask (VITAL)
            irq_mask2 = val;
            // Fire latched VBL if mask just became ready
            if (vbl_pending && (irq_mask2 & 0x030) == 0x030) {
                vbl_pending = 0;
                geo_m68k_interrupt(irq_vbl_level);
            }
            return;

        // Unknown word registers (silently accepted)
        case 0x0006:
        case 0x0008:
        case 0x000a:
            return;

        // DMA registers (word-addressed)
        case 0x0064: // DMA destination high
            dma.dst = (dma.dst & 0xffff) | ((uint32_t)val << 16);
            return;
        case 0x0066: // DMA destination low
            dma.dst = (dma.dst & 0xffff0000) | (uint32_t)val;
            return;
        case 0x0068: // DMA source high
            dma.src = (dma.src & 0xffff) | ((uint32_t)val << 16);
            return;
        case 0x006a: // DMA source low
            dma.src = (dma.src & 0xffff0000) | (uint32_t)val;
            return;
        case 0x006c: // DMA pattern/fill value
            dma.val = val;
            return;
        case 0x0070: // DMA length high
            dma.len = (dma.len & 0xffff) | ((uint32_t)val << 16);
            return;
        case 0x0072: // DMA length low
            dma.len = (dma.len & 0xffff0000) | (uint32_t)val;
            return;
        case 0x007e: // DMA config 0
            dma.config = val;
            return;
        case 0x0080: case 0x0082: case 0x0084: case 0x0086:
        case 0x0088: case 0x008a: case 0x008c: case 0x008e:
            return; // DMA config extension words
    }

    // Fall through to byte handler for byte-oriented registers
    cd_reg_write_8(addr, (val >> 8) & 0xff);
    cd_reg_write_8(addr + 1, val & 0xff);
}

// =========================================================================
// Transfer area read/write (0xE00000 - 0xEFFFFF)
// =========================================================================
static uint8_t transfer_read_8(uint32_t addr) {
    addr &= 0xfffff;

    switch (transfer_area) {
        case 0: // SPR
            return spr_dram[(spr_bank * SIZE_1M) + (addr & (SIZE_1M - 1))];
        case 1: // PCM - odd bytes only
            if (addr & 1)
                return pcm_dram[(pcm_bank * SIZE_512K) + ((addr >> 1) & (SIZE_512K - 1))];
            return 0xff;
        case 4: // Z80 - odd bytes only
            if (addr & 1)
                return z80_ram_cd[(addr >> 1) & (SIZE_64K - 1)];
            return 0xff;
        case 5: // FIX - odd bytes only
            if (addr & 1)
                return fix_ram[(addr >> 1) & (SIZE_128K - 1)];
            return 0xff;
    }
    return 0xff;
}

static uint16_t transfer_read_16(uint32_t addr) {
    addr &= 0xfffff;

    switch (transfer_area) {
        case 0: { // SPR - word read
            uint32_t spr_addr = (spr_bank * SIZE_1M) + (addr & (SIZE_1M - 2));
            return (spr_dram[spr_addr] << 8) | spr_dram[spr_addr + 1];
        }
        case 1: { // PCM
            uint32_t pcm_addr = (pcm_bank * SIZE_512K) + ((addr >> 1) & (SIZE_512K - 1));
            return pcm_dram[pcm_addr] | 0xff00;
        }
        case 4: { // Z80
            uint32_t z_addr = (addr >> 1) & (SIZE_64K - 1);
            return z80_ram_cd[z_addr] | 0xff00;
        }
        case 5: { // FIX
            uint32_t fix_addr = (addr >> 1) & (SIZE_128K - 1);
            return fix_ram[fix_addr] | 0xff00;
        }
    }
    return 0xffff;
}

static void transfer_write_8(uint32_t addr, uint8_t val) {
    addr &= 0xfffff;

    switch (transfer_area) {
        case 0: // SPR
            spr_dram[(spr_bank * SIZE_1M) + (addr & (SIZE_1M - 1))] = val;
            return;
        case 1: // PCM - odd bytes only
            if (addr & 1)
                pcm_dram[(pcm_bank * SIZE_512K) + ((addr >> 1) & (SIZE_512K - 1))] = val;
            return;
        case 4: // Z80 - odd bytes only
            if (addr & 1)
                z80_ram_cd[(addr >> 1) & (SIZE_64K - 1)] = val;
            return;
        case 5: // FIX - odd bytes only
            if (addr & 1)
                fix_ram[(addr >> 1) & (SIZE_128K - 1)] = val;
            return;
    }
}

static void transfer_write_16(uint32_t addr, uint16_t val) {
    addr &= 0xfffff;

    switch (transfer_area) {
        case 0: { // SPR - word write
            uint32_t spr_addr = (spr_bank * SIZE_1M) + (addr & (SIZE_1M - 2));
            spr_dram[spr_addr] = val >> 8;
            spr_dram[spr_addr + 1] = val & 0xff;
            return;
        }
        case 1: { // PCM
            uint32_t pcm_addr = (pcm_bank * SIZE_512K) + ((addr >> 1) & (SIZE_512K - 1));
            pcm_dram[pcm_addr] = val & 0xff;
            return;
        }
        case 4: { // Z80
            uint32_t z_addr = (addr >> 1) & (SIZE_64K - 1);
            z80_ram_cd[z_addr] = val & 0xff;
            return;
        }
        case 5: { // FIX
            uint32_t fix_addr = (addr >> 1) & (SIZE_128K - 1);
            fix_ram[fix_addr] = val & 0xff;
            return;
        }
    }
}

// =========================================================================
// CD Mode M68K Memory Map
// =========================================================================
unsigned geo_cd_m68k_read_8(unsigned address) {
    address &= 0xffffff;

    if (address < 0x000080) { // Vector Table
        m68k_modify_timeslice(1);
        return vectable ?
            read08(pram, address) : read08(romdata->b, address);
    }
    else if (address < 0x200000) { // Program RAM (2MB)
        return read08(pram, address);
    }
    else if (address < 0x300000) { // Unused
        return 0xff;
    }
    else if (address < 0x400000) { // Registers (same as cartridge)
        switch (address) {
            case 0x300000: return geo_input_cb[0](0);
            case 0x300001: return geo_input_sys_cb[3]();
            case 0x300081: return geo_input_sys_cb[2]() & ~0x40;
            case 0x320000: return ngsys.sound_reply;
            case 0x320001: return geo_input_sys_cb[0]();
            case 0x340000: return geo_input_cb[1](1);
            case 0x380000: return geo_input_sys_cb[1]();
            case 0x3c0000: case 0x3c0002: case 0x3c0008: case 0x3c000a:
            case 0x3c0004: case 0x3c000c:
            case 0x3c0006: case 0x3c000e:
                break;
        }
    }
    else if (address < 0x800000) { // Palette RAM
        return geo_lspc_palram_rd08(address);
    }
    else if (address < 0xc00000) { // Backup RAM (8K mirrored)
        if (address & 0x01)
            return backup_ram[(address >> 1) & 0x1fff];
        return 0xff;
    }
    else if (address < 0xd00000) { // BIOS ROM (512K mirrored)
        return read08(romdata->b, address & 0x7ffff);
    }
    else if (address < 0xe00000) { // NVRAM (64K mirrored)
        return read08(ngsys.nvram, address & 0xffff);
    }
    else if (address < 0xf00000) { // Transfer area
        return transfer_read_8(address);
    }
    else { // CD registers
        return cd_reg_read_8(address);
    }

    return 0xff;
}

unsigned geo_cd_m68k_read_16(unsigned address) {
    address &= 0xffffff;

    if (address < 0x000080) {
        m68k_modify_timeslice(1);
        return vectable ?
            read16(pram, address) : read16(romdata->b, address);
    }
    else if (address < 0x200000) {
        return read16(pram, address);
    }
    else if (address < 0x300000) {
        return 0xffff;
    }
    else if (address < 0x400000) {
        switch (address) {
            case 0x300000: {
                uint8_t val = geo_input_cb[0](0);
                return (val << 8) | val;
            }
            case 0x340000: {
                uint8_t val = geo_input_cb[1](1);
                return (val << 8) | val;
            }
            case 0x380000: {
                uint8_t val = geo_input_sys_cb[1]();
                return (val << 8) | val;
            }
            case 0x3c0000: case 0x3c0002: case 0x3c0008: case 0x3c000a:
                return geo_lspc_vram_rd();
            case 0x3c0004: case 0x3c000c:
                return geo_lspc_vrammod_rd();
            case 0x3c0006: case 0x3c000e:
                return geo_lspc_mode_rd();
        }
    }
    else if (address < 0x800000) {
        return geo_lspc_palram_rd16(address);
    }
    else if (address < 0xc00000) {
        return backup_ram[(address >> 1) & 0x1fff] | 0xff00;
    }
    else if (address < 0xd00000) {
        return read16(romdata->b, address & 0x7ffff);
    }
    else if (address < 0xe00000) {
        return read16(ngsys.nvram, address & 0xffff);
    }
    else if (address < 0xf00000) {
        return transfer_read_16(address);
    }
    else {
        return cd_reg_read_16(address);
    }

    return 0xffff;
}

void geo_cd_m68k_write_8(unsigned address, unsigned value) {
    address &= 0xffffff;

    if (address < 0x200000) { // Program RAM
        pram[address] = value;
    }
    else if (address < 0x300000) { // Unused
        return;
    }
    else if (address < 0x400000) { // Registers
        switch (address) {
            case 0x300001:
                geo_watchdog_reset();
                return;
            case 0x320000:
                ngsys.sound_code = value & 0xff;
                if (z80_enabled)
                    geo_z80_nmi();
                return;
            case 0x380051:
                return; // RTC control (no RTC on CD)

            case 0x3a0001: geo_lspc_shadow_wr(0); return;
            case 0x3a0003:
                if (vectable != 0) geo_log(GEO_LOG_DBG, "VECTABLE: -> BIOS (PC=%06x)\n", m68k_get_reg(NULL, M68K_REG_PPC));
                vectable = 0; return; // REG_SWPBIOS
            case 0x3a0005: return; // REG_CRDUNLOCK1
            case 0x3a0007: return; // REG_CRDLOCK2
            case 0x3a0009: return; // REG_CRDREGSEL
            case 0x3a000b: // REG_BRDFIX
                geo_lspc_set_fix(LSPC_FIX_BOARD);
                return;
            case 0x3a000d: reg_sramlock = 1; return;
            case 0x3a000f: geo_lspc_palram_bank(1); return;
            case 0x3a0011: geo_lspc_shadow_wr(1); return;
            case 0x3a0013:
                if (vectable != 1) geo_log(GEO_LOG_DBG, "VECTABLE: -> PRAM (PC=%06x)\n", m68k_get_reg(NULL, M68K_REG_PPC));
                vectable = 1; return; // REG_SWPROM (to PRAM)
            case 0x3a0015: return; // REG_CRDLOCK1
            case 0x3a0017: return; // REG_CRDUNLOCK2
            case 0x3a0019: return; // REG_CRDNORMAL
            case 0x3a001b: // REG_CRTFIX
                geo_lspc_set_fix(LSPC_FIX_CART);
                return;
            case 0x3a001d: reg_sramlock = 0; return;
            case 0x3a001f: geo_lspc_palram_bank(0); return;

            case 0x3c0000: case 0x3c0002: case 0x3c0004: case 0x3c0006:
            case 0x3c0008: case 0x3c000a: case 0x3c000c: case 0x3c000e:
                geo_cd_m68k_write_16(address, (value << 8) | (value & 0xff));
                return;
        }
    }
    else if (address < 0x800000) {
        geo_lspc_palram_wr08(address, value);
    }
    else if (address < 0xc00000) { // Backup RAM
        backup_ram[(address >> 1) & 0x1fff] = value;
    }
    else if (address < 0xd00000) { // BIOS ROM (read-only)
        return;
    }
    else if (address < 0xe00000) { // NVRAM
        if (!reg_sramlock)
            ngsys.nvram[address & 0xffff] = value;
    }
    else if (address < 0xf00000) { // Transfer area
        transfer_write_8(address, value);
    }
    else { // CD registers
        cd_reg_write_8(address, value);
    }
}

void geo_cd_m68k_write_16(unsigned address, unsigned value) {
    address &= 0xffffff;

    if (address < 0x200000) {
        write16(pram, address, value);
    }
    else if (address < 0x300000) {
        return;
    }
    else if (address < 0x400000) {
        switch (address) {
            case 0x300000: // Watchdog kick (word write)
                geo_watchdog_reset();
                return;
            case 0x320000:
                ngsys.sound_code = (value >> 8) & 0xff;
                if (z80_enabled)
                    geo_z80_nmi();
                return;
            case 0x3c0000: geo_lspc_vramaddr_wr(value); return;
            case 0x3c0002: geo_lspc_vram_wr(value); return;
            case 0x3c0004: geo_lspc_vrammod_wr((int16_t)value); return;
            case 0x3c0006: geo_lspc_mode_wr(value); return;
            case 0x3c0008:
                ngsys.irq2_reload =
                    (ngsys.irq2_reload & 0xffff) | (value << 16);
                return;
            case 0x3c000a:
                ngsys.irq2_reload =
                    (ngsys.irq2_reload & 0xffff0000) | (value & 0xffff);
                if (ngsys.irq2_ctrl & IRQ_TIMER_RELOAD_WRITE)
                    ngsys.irq2_counter = ngsys.irq2_reload;
                return;
            case 0x3c000c:
                if (value & 0x04) m68k_set_virq(irq_vbl_level, 0);
                if (value & 0x02) m68k_set_virq(irq_timer_level, 0);
                if (value & 0x01) m68k_set_virq(IRQ_RESET, 0);
                return;
            case 0x3c000e: return;
        }
    }
    else if (address < 0x800000) {
        geo_lspc_palram_wr16(address, value);
    }
    else if (address < 0xc00000) {
        backup_ram[(address >> 1) & 0x1fff] = value & 0xff;
    }
    else if (address < 0xd00000) {
        return;
    }
    else if (address < 0xe00000) {
        if (!reg_sramlock)
            write16(ngsys.nvram, address & 0xffff, value);
    }
    else if (address < 0xf00000) {
        transfer_write_16(address, value);
    }
    else {
        cd_reg_write_16(address, value);
    }
}

// =========================================================================
// CD Timing
// =========================================================================
// CD Communication IRQ rate: ~64Hz idle, ~75Hz during playback
// Using the sector timer (~75Hz) to also trigger communication IRQs

void geo_cd_tick(unsigned mcycles) {
    cd_sector_counter += mcycles;

    // Set timer rate based on play state
    int is_playing = cd.playing_data || cd.playing_audio;
    if (is_playing) {
        if (cd.playing_data && geo_get_system() == SYSTEM_CDZ)
            cd_sector_rate = CD_SECTOR_RATE_2X;
        else
            cd_sector_rate = CD_SECTOR_RATE_1X;
    } else {
        cd_sector_rate = CD_SECTOR_RATE_IDLE;
    }

    // Single timer handling sector decode, position advance, and communication
    // CD-ROM timer callback: handles sector decoding and IRQ processing
    while (cd_sector_counter >= cd_sector_rate) {
        cd_sector_counter -= cd_sector_rate;

        if (cd.playing_data || cd.playing_audio) {
            // Determine audio vs data from current LBA's track type
            int is_audio = 0;
            unsigned cur_track = 0;
            for (unsigned i = 0; i < geo_chd_num_tracks(); ++i) {
                if (cd.play_lba >= geo_chd_track_start(i + 1))
                    cur_track = i + 1;
            }
            if (cur_track > 0 && geo_chd_track_is_audio(cur_track))
                is_audio = 1;

            cd.playing_audio = is_audio;
            cd.playing_data = !is_audio;
            cdda_playing = is_audio;

            lc8951_sector_decoded();

            if (lc.decoder_enabled &&
                (irq_mask1 & 0x500) == 0x500 &&
                (lc.ifctrl & LC_IFCTRL_DECIEN) &&
                !(lc.ifstat & LC_IFSTAT_DECI)) {
                cd_irq_mask |= 0x20;
                cd_pending_irq |= CD_INT_DECODER;
                sector_decoded_this_frame = 1;
            }

            // Audio sector: accumulate CDDA samples
            if (cd.playing_audio && cd.play_lba < geo_chd_leadout()) {
                if (cdda_samples + CDDA_SAMPLES_PER_SECTOR <= CDDA_BUF_MAXSAMPLES) {
                    int16_t *dst = cdda_buf + (cdda_samples * 2);
                    if (geo_chd_read_audio(cd.play_lba, dst)) {
                        cdda_samples += CDDA_SAMPLES_PER_SECTOR;
                    } else {
                        memset(dst, 0, CDDA_SAMPLES_PER_SECTOR * 2 * sizeof(int16_t));
                        cdda_samples += CDDA_SAMPLES_PER_SECTOR;
                    }
                }
            }
            cd.play_lba++;
        }

        // Communication IRQ (fires every tick)
        if ((irq_mask1 & 0x50) == 0x50 && cd_irq_enabled) {
            cd_irq_mask |= 0x10;
            cd_pending_irq |= CD_INT_COMMUNICATION;
        }

        // Re-evaluate interrupts after setting all pending sources
        cd_update_interrupts();
    }
}

// =========================================================================
// VBL Masking
// =========================================================================
int geo_cd_vbl_enabled(void) {
    return (irq_mask2 & 0x030) == 0x030;
}

// Called by LSPC at VBL time — if mask isn't ready, latch as pending
void geo_cd_set_vbl_pending(void) {
    vbl_pending = 1;
}

// =========================================================================
// CDDA Audio Access
// =========================================================================
int geo_cd_is_playing_cdda(void) {
    return cdda_playing;
}

int16_t* geo_cd_get_cdda_buffer(void) {
    return cdda_buf;
}

size_t geo_cd_get_cdda_samples(void) {
    return cdda_samples;
}

void geo_cd_cdda_clear(void) {
    cdda_samples = 0;
}

void geo_cd_cdda_consume(size_t consumed) {
    if (consumed >= cdda_samples) {
        cdda_samples = 0;
        return;
    }
    size_t remaining = cdda_samples - consumed;
    memmove(cdda_buf, cdda_buf + consumed * 2, remaining * 2 * sizeof(int16_t));
    cdda_samples = remaining;
}

// =========================================================================
// Init/Reset/Deinit
// =========================================================================
// =========================================================================
// BIOS Detection and Patching
// =========================================================================

// Check for a pattern at a BIOS offset (addresses relative to C00000)
static int bios_pattern(uint8_t *bios, size_t sz, uint32_t offset,
                        const uint8_t *pat, size_t patsz) {
    if (offset + patsz > sz) return 0;
    return memcmp(bios + offset, pat, patsz) == 0;
}

// Apply a patch at a BIOS offset
static void bios_patch(uint8_t *bios, size_t sz, uint32_t offset,
                       const uint8_t *pat, size_t patsz) {
    if (offset + patsz > sz) return;
    memcpy(bios + offset, pat, patsz);
}

// NOP instruction (4E71) and STOP #$2000 + NOP (halt CPU until IRQ, supervisor mode)
static const uint8_t NOP2[] = { 0x4E, 0x71 };
static const uint8_t STOP_NOP[] = { 0x4E, 0x72, 0x20, 0x00, 0x4E, 0x71 };

int geo_cd_detect_bios(uint8_t *bios, size_t sz) {
    // Validity check: first 4 bytes must be 00 10 F3 00
    static const uint8_t valid[] = { 0x00, 0x10, 0xF3, 0x00 };
    if (!bios_pattern(bios, sz, 0x0000, valid, 4))
        return CD_BIOS_UNKNOWN;

    // Family detection from reset vector area at 0x006C
    static const uint8_t pat_front[] = { 0x00, 0xC0, 0xC8, 0x5E };
    static const uint8_t pat_top[]   = { 0x00, 0xC0, 0xC2, 0x22 };
    static const uint8_t pat_cdz[]   = { 0x00, 0xC0, 0xA3, 0xE8 };

    if (bios_pattern(bios, sz, 0x006C, pat_cdz, 4))
        return CD_BIOS_CDZ;
    if (bios_pattern(bios, sz, 0x006C, pat_top, 4))
        return CD_BIOS_TOP;
    if (bios_pattern(bios, sz, 0x006C, pat_front, 4))
        return CD_BIOS_FRONT;

    return CD_BIOS_UNKNOWN;
}

// Apply CD recognition bypass patches (protection check skip)
static void bios_patch_recognition(uint8_t *bios, size_t sz, int family) {
    int applied = 0;
    switch (family) {
        case CD_BIOS_CDZ:
            if (bios_pattern(bios, sz, 0xEB82, (uint8_t[]){0x66,0x10}, 2)) {
                bios_patch(bios, sz, 0xEB82, NOP2, 2); applied++;
            }
            if (bios_pattern(bios, sz, 0xD280, (uint8_t[]){0x66,0x74}, 2)) {
                bios_patch(bios, sz, 0xD280, NOP2, 2); applied++;
            }
            break;
        case CD_BIOS_FRONT:
            if (bios_pattern(bios, sz, 0x10B64, (uint8_t[]){0x66,0x04}, 2)) {
                bios_patch(bios, sz, 0x10B64, NOP2, 2); applied++;
            }
            break;
        case CD_BIOS_TOP:
            if (bios_pattern(bios, sz, 0x10436, (uint8_t[]){0x66,0x04}, 2)) {
                bios_patch(bios, sz, 0x10436, NOP2, 2); applied++;
            }
            break;
    }
    geo_log(GEO_LOG_INF, "BIOS recognition patches applied: %d\n", applied);
}

// Apply speed hack patches (replace busy-wait loops with STOP)
static void bios_patch_speed_hack(uint8_t *bios, size_t sz, int family) {
    // Each patch replaces SUBQ.L #1,D1; BEQ.W xxxx (53 81 67 00 xx xx)
    // with STOP #0; NOP; NOP (73 00 4E 71 4E 71)
    static const uint8_t subq_beq[] = { 0x53, 0x81, 0x67, 0x00 };

    switch (family) {
        case CD_BIOS_CDZ: {
            static const uint32_t addrs[] = {0xE6E0, 0xE724, 0xE764, 0xE836, 0xE860};
            for (int i = 0; i < 5; ++i)
                if (bios_pattern(bios, sz, addrs[i], subq_beq, 4))
                    bios_patch(bios, sz, addrs[i], STOP_NOP, 6);
            break;
        }
        case CD_BIOS_FRONT: {
            static const uint32_t addrs[] = {0x10716, 0x10758, 0x10798, 0x10864};
            for (int i = 0; i < 4; ++i)
                if (bios_pattern(bios, sz, addrs[i], subq_beq, 4))
                    bios_patch(bios, sz, addrs[i], STOP_NOP, 6);
            break;
        }
        case CD_BIOS_TOP: {
            static const uint32_t addrs[] = {0x0FFCA, 0x1000E, 0x1004E, 0x10120};
            for (int i = 0; i < 4; ++i)
                if (bios_pattern(bios, sz, addrs[i], subq_beq, 4))
                    bios_patch(bios, sz, addrs[i], STOP_NOP, 6);
            break;
        }
    }
}

void geo_cd_set_speed_hack(int enabled) {
    speed_hack_enabled = enabled;
}

int geo_cd_sector_decoded_this_frame(void) {
    return sector_decoded_this_frame;
}

void geo_cd_clear_sector_decoded(void) {
    sector_decoded_this_frame = 0;
}

void geo_cd_init(void) {
    romdata = geo_romdata_ptr();

    // Detect BIOS family and apply patches
    if (romdata->b && romdata->bsz >= SIZE_512K) {
        bios_family = geo_cd_detect_bios(romdata->b, romdata->bsz);
        geo_log(GEO_LOG_INF, "CD BIOS family: %s (SP=%02x%02x%02x%02x vec6C=%02x%02x%02x%02x)\n",
            bios_family == CD_BIOS_CDZ ? "CDZ" :
            bios_family == CD_BIOS_TOP ? "Top Loader" :
            bios_family == CD_BIOS_FRONT ? "Front Loader" : "Unknown",
            romdata->b[0], romdata->b[1], romdata->b[2], romdata->b[3],
            romdata->b[0x6C], romdata->b[0x6D], romdata->b[0x6E], romdata->b[0x6F]);

        // Always apply recognition bypass (copy protection skip)
        bios_patch_recognition(romdata->b, romdata->bsz, bios_family);

        // Apply speed hack if enabled
        if (speed_hack_enabled)
            bios_patch_speed_hack(romdata->b, romdata->bsz, bios_family);
    }

    memset(pram, 0, SIZE_2M);
    memset(spr_dram, 0, SIZE_4M);
    memset(pcm_dram, 0, SIZE_1M);
    memset(z80_ram_cd, 0, SIZE_64K);
    memset(fix_ram, 0, SIZE_128K);
    memset(backup_ram, 0, SIZE_8K);

    lc8951_reset();
    cd_comm_reset();
    memset(&dma, 0, sizeof(dma));

    // Redirect ROM data pointers to CD RAM for LSPC and YM2610
    geo_lspc_set_cd_mode(1);
    romdata->c = spr_dram;
    romdata->csz = SIZE_4M;
    romdata->s = fix_ram;
    romdata->ssz = SIZE_128K;
    romdata->v1 = pcm_dram;
    romdata->v1sz = SIZE_1M;
    romdata->v2 = pcm_dram;
    romdata->v2sz = SIZE_1M;

    // Point M1/SM to Z80 CD RAM
    romdata->m = z80_ram_cd;
    romdata->msz = SIZE_64K;

    // Recalculate LSPC masks for the new ROM sizes
    geo_lspc_postload();
}

void geo_cd_deinit(void) {
    // Nothing dynamically allocated
}

void geo_cd_reset(void) {
    vectable = 0;
    transfer_area = 0;
    spr_bank = 0;
    pcm_bank = 0;
    spr_disable = 0;
    fix_disable = 0;
    video_disable = 0;
    busreq_spr = 0;
    busreq_pcm = 0;
    busreq_z80 = 0;
    busreq_fix = 0;
    z80_enabled = 0;
    reg_sramlock = 0;
    cd_irq_mask = 0;
    cd_pending_irq = 0;
    cd_irq_enabled = 0;
    irq_mask1 = 0;
    irq_mask2 = 0;
    vbl_pending = 0;
    cd_sector_counter = 0;
    cd_comm_counter = 0;
    cdda_playing = 0;
    cdda_samples = 0;

    lc8951_reset();
    cd_comm_reset();
    memset(&dma, 0, sizeof(dma));

    // CDZ BIOS polls Status (0x00) expecting STOPPED before proceeding.
    // Real hardware: drive spins up and transitions to STOPPED autonomously.
    // Since we have a disc loaded at boot, start directly in STOPPED state.
    cd.drive_status = CD_STATUS_STOP;
    cd.status[0] = cd.drive_status;
    cd_comm_build_response();
}

// =========================================================================
// Backup RAM Access
// =========================================================================
const void* geo_cd_backup_ram_ptr(void) {
    return backup_ram;
}

// =========================================================================
// State Serialization (placeholder - Phase 8)
// =========================================================================
size_t geo_cd_state_size(void) {
    return SIZE_2M + SIZE_4M + SIZE_1M + SIZE_64K + SIZE_128K + SIZE_8K +
           sizeof(lc) + sizeof(cd) + sizeof(dma) +
           sizeof(cdda_buf) + 64;
}

void geo_cd_state_save(uint8_t *st) {
    geo_serial_pushblk(st, pram, SIZE_2M);
    geo_serial_pushblk(st, spr_dram, SIZE_4M);
    geo_serial_pushblk(st, pcm_dram, SIZE_1M);
    geo_serial_pushblk(st, z80_ram_cd, SIZE_64K);
    geo_serial_pushblk(st, fix_ram, SIZE_128K);
    geo_serial_pushblk(st, backup_ram, SIZE_8K);

    // CD controller state
    geo_serial_pushblk(st, (uint8_t*)&lc, sizeof(lc));
    geo_serial_pushblk(st, (uint8_t*)&cd, sizeof(cd));
    geo_serial_pushblk(st, (uint8_t*)&dma, sizeof(dma));

    // Registers
    geo_serial_push8(st, vectable);
    geo_serial_push8(st, transfer_area);
    geo_serial_push8(st, spr_bank);
    geo_serial_push8(st, pcm_bank);
    geo_serial_push8(st, spr_disable);
    geo_serial_push8(st, fix_disable);
    geo_serial_push8(st, video_disable);
    geo_serial_push8(st, z80_enabled);
    geo_serial_push8(st, reg_sramlock);
    geo_serial_push8(st, cd_irq_mask);
    geo_serial_push8(st, cd_irq_enabled);
    geo_serial_push32(st, cd_sector_counter);

    // Bus request and IRQ mask state
    geo_serial_push8(st, busreq_spr);
    geo_serial_push8(st, busreq_pcm);
    geo_serial_push8(st, busreq_z80);
    geo_serial_push8(st, busreq_fix);
    geo_serial_push16(st, irq_mask1);
    geo_serial_push16(st, irq_mask2);
    geo_serial_push32(st, cd_comm_counter);
    geo_serial_push32(st, cd_sector_rate);

    // CDDA state
    geo_serial_pushblk(st, (uint8_t*)cdda_buf, sizeof(cdda_buf));
    geo_serial_push32(st, (uint32_t)cdda_samples);
    geo_serial_push8(st, cdda_playing);
}

void geo_cd_state_load(uint8_t *st) {
    geo_serial_popblk(pram, st, SIZE_2M);
    geo_serial_popblk(spr_dram, st, SIZE_4M);
    geo_serial_popblk(pcm_dram, st, SIZE_1M);
    geo_serial_popblk(z80_ram_cd, st, SIZE_64K);
    geo_serial_popblk(fix_ram, st, SIZE_128K);
    geo_serial_popblk(backup_ram, st, SIZE_8K);

    geo_serial_popblk((uint8_t*)&lc, st, sizeof(lc));
    geo_serial_popblk((uint8_t*)&cd, st, sizeof(cd));
    geo_serial_popblk((uint8_t*)&dma, st, sizeof(dma));

    vectable = geo_serial_pop8(st);
    transfer_area = geo_serial_pop8(st);
    spr_bank = geo_serial_pop8(st);
    pcm_bank = geo_serial_pop8(st);
    spr_disable = geo_serial_pop8(st);
    fix_disable = geo_serial_pop8(st);
    video_disable = geo_serial_pop8(st);
    z80_enabled = geo_serial_pop8(st);
    reg_sramlock = geo_serial_pop8(st);
    cd_irq_mask = geo_serial_pop8(st);
    cd_irq_enabled = geo_serial_pop8(st);
    cd_sector_counter = geo_serial_pop32(st);

    busreq_spr = geo_serial_pop8(st);
    busreq_pcm = geo_serial_pop8(st);
    busreq_z80 = geo_serial_pop8(st);
    busreq_fix = geo_serial_pop8(st);
    irq_mask1 = geo_serial_pop16(st);
    irq_mask2 = geo_serial_pop16(st);
    cd_comm_counter = geo_serial_pop32(st);
    cd_sector_rate = geo_serial_pop32(st);

    geo_serial_popblk((uint8_t*)cdda_buf, st, sizeof(cdda_buf));
    cdda_samples = (size_t)geo_serial_pop32(st);
    cdda_playing = geo_serial_pop8(st);
}
