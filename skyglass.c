/*
 * SKYGLASS By R1y3n - MIT License
*/
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <errno.h>
#include <ctype.h>
#include <locale.h>
#include <fcntl.h>
#include <unistd.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/select.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/Xatom.h>
#include <X11/keysym.h>
#include <X11/extensions/XShm.h>
#include <X11/extensions/shape.h>
#define STB_TRUETYPE_IMPLEMENTATION
#define STBTT_STATIC
#include "stb_truetype.h"

typedef uint32_t u32; typedef uint8_t u8;
#define CW 380
#define CH 500
#define MARG 12
#define WW (CW + 2 * MARG)
#define WH (CH + 2 * MARG)
#define PI_F 3.14159265f

static int PW, PH; static float S = 1.0f;
static u32 *fb; static u8 *shadow_a;
static int g_demo = 0;

/* ---------- small helpers ---------- */
static inline float fhyp(float a, float b) { return sqrtf(a * a + b * b); }
static inline float clampf(float v, float a, float b) { return v < a ? a : v > b ? b : v; }
static inline float smoothf(float a, float b, float x) { float t = clampf((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); }
static inline float easef(float c, float t, float dt, float r) { float k = dt * r; if (k > 1) k = 1; return c + (t - c) * k; }
static inline int div255(int v) { return (v + 128 + ((v + 128) >> 8)) >> 8; }
#define RGB(r, g, b) ((u32)(((r) << 16) | ((g) << 8) | (b)))
static inline u32 mixc(u32 a, u32 b, float t) {
    if (t <= 0) return a; if (t >= 1) return b;
    int k = (int)(t * 256), ik = 256 - k;
    return ((((a >> 16) & 255) * ik + ((b >> 16) & 255) * k) >> 8 << 16) | ((((a >> 8) & 255) * ik + ((b >> 8) & 255) * k) >> 8 << 8) | (((a & 255) * ik + (b & 255) * k) >> 8);
}
static inline u32 scalec(u32 c, float r, float g, float b) {
    int R = (int)(((c >> 16) & 255) * r), G = (int)(((c >> 8) & 255) * g), B = (int)((c & 255) * b);
    return ((R > 255 ? 255 : R < 0 ? 0 : R) << 16) | ((G > 255 ? 255 : G < 0 ? 0 : G) << 8) | (B > 255 ? 255 : B < 0 ? 0 : B);
}
static u32 rs = 2463534242u;
static inline float rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return (rs & 0xFFFFFF) / 16777216.f; }
static inline float rndr(float a, float b) { return a + (b - a) * rnd(); }
static u32 hash_str(const char *s) { u32 h = 2166136261u; while (*s) { h ^= (u8)*s++; h *= 16777619u; } return h; }

/* ---------- pixel ops (framebuffer is premultiplied ARGB) ---------- */
static inline void bl(int x, int y, u32 c, int a) {
    if ((unsigned)x >= (unsigned)PW || (unsigned)y >= (unsigned)PH || a <= 0) return;
    u32 *p = fb + (size_t)y * PW + x;
    if (a >= 255) { *p = 0xFF000000u | c; return; }
    u32 d = *p; int ia = 255 - a;
    int r = div255(((c >> 16) & 255) * a) + div255(((d >> 16) & 255) * ia);
    int g = div255(((c >> 8) & 255) * a) + div255(((d >> 8) & 255) * ia);
    int b = div255((c & 255) * a) + div255((d & 255) * ia);
    int al = a + div255((int)(d >> 24) * ia);
    *p = ((u32)al << 24) | (r << 16) | (g << 8) | b;
}
static inline void addp(int x, int y, u32 c, int a) {
    if ((unsigned)x >= (unsigned)PW || (unsigned)y >= (unsigned)PH || a <= 0) return;
    u32 *p = fb + (size_t)y * PW + x; u32 d = *p;
    int r = ((d >> 16) & 255) + (((c >> 16) & 255) * a >> 8), g = ((d >> 8) & 255) + (((c >> 8) & 255) * a >> 8), b = (d & 255) + ((c & 255) * a >> 8);
    *p = (d & 0xFF000000u) | ((r > 255 ? 255 : r) << 16) | ((g > 255 ? 255 : g) << 8) | (b > 255 ? 255 : b);
}
static inline u32 getp(int x, int y) { if ((unsigned)x >= (unsigned)PW || (unsigned)y >= (unsigned)PH) return 0; return fb[(size_t)y * PW + x] & 0xFFFFFF; }
#define PX(v) (((v) + MARG) * S)
#define SC(v) ((v) * S)

/* ---------- anti-aliased primitives (logical card coordinates) ---------- */
static void rrect(float x, float y, float w, float h, float r, u32 col, float alpha) {
    x = PX(x); y = PX(y); w = SC(w); h = SC(h); r = SC(r); if (r > w / 2) r = w / 2; if (r > h / 2) r = h / 2;
    float cx = x + w / 2, cy = y + h / 2, hw = w / 2 - r, hh = h / 2 - r;
    for (int py = (int)floorf(y) - 1; py <= (int)ceilf(y + h) + 1; py++) for (int px = (int)floorf(x) - 1; px <= (int)ceilf(x + w) + 1; px++) {
        float dx = fabsf(px + .5f - cx) - hw, dy = fabsf(py + .5f - cy) - hh;
        float ox = dx > 0 ? dx : 0, oy = dy > 0 ? dy : 0;
        float sd = sqrtf(ox * ox + oy * oy) + fminf(fmaxf(dx, dy), 0) - r;
        float cv = clampf(.5f - sd, 0, 1);
        if (cv > 0) bl(px, py, col, (int)(cv * alpha * 255));
    }
}
static void rrect_grad(float x, float y, float w, float h, float r, u32 c0, float a0, u32 c1, float a1) {
    float X = PX(x), Y = PX(y), Wp = SC(w), Hp = SC(h), R = SC(r); if (R > Wp / 2) R = Wp / 2; if (R > Hp / 2) R = Hp / 2;
    float cx = X + Wp / 2, cy = Y + Hp / 2, hw = Wp / 2 - R, hh = Hp / 2 - R;
    for (int py = (int)floorf(Y) - 1; py <= (int)ceilf(Y + Hp) + 1; py++) {
        float t = clampf((py + .5f - Y) / Hp, 0, 1); u32 c = mixc(c0, c1, t); float a = a0 + (a1 - a0) * t;
        for (int px = (int)floorf(X) - 1; px <= (int)ceilf(X + Wp) + 1; px++) {
            float dx = fabsf(px + .5f - cx) - hw, dy = fabsf(py + .5f - cy) - hh;
            float ox = dx > 0 ? dx : 0, oy = dy > 0 ? dy : 0;
            float sd = sqrtf(ox * ox + oy * oy) + fminf(fmaxf(dx, dy), 0) - R;
            float cv = clampf(.5f - sd, 0, 1);
            if (cv > 0) bl(px, py, c, (int)(cv * a * 255));
        }
    }
}
static void rrect_line(float x, float y, float w, float h, float r, float th, u32 col, float alpha) {
    x = PX(x); y = PX(y); w = SC(w); h = SC(h); r = SC(r); th = SC(th); if (r > w / 2) r = w / 2; if (r > h / 2) r = h / 2;
    float cx = x + w / 2, cy = y + h / 2, hw = w / 2 - r, hh = h / 2 - r;
    for (int py = (int)floorf(y) - 2; py <= (int)ceilf(y + h) + 2; py++) for (int px = (int)floorf(x) - 2; px <= (int)ceilf(x + w) + 2; px++) {
        float dx = fabsf(px + .5f - cx) - hw, dy = fabsf(py + .5f - cy) - hh;
        float ox = dx > 0 ? dx : 0, oy = dy > 0 ? dy : 0;
        float sd = sqrtf(ox * ox + oy * oy) + fminf(fmaxf(dx, dy), 0) - r;
        float cv = clampf(th / 2 + .5f - fabsf(sd + th / 2), 0, 1);
        if (cv > 0) bl(px, py, col, (int)(cv * alpha * 255));
    }
}
static void ellipse(float cx, float cy, float rx, float ry, float rot, u32 col, float alpha) {
    cx = PX(cx); cy = PX(cy); rx = SC(rx); ry = SC(ry);
    float R = fmaxf(rx, ry) + 2, mr = fminf(rx, ry), cr = cosf(rot), sr = sinf(rot);
    for (int py = (int)(cy - R); py <= (int)(cy + R) + 1; py++) for (int px = (int)(cx - R); px <= (int)(cx + R) + 1; px++) {
        float dx = px + .5f - cx, dy = py + .5f - cy;
        if (rot != 0) { float tx = dx * cr + dy * sr; dy = -dx * sr + dy * cr; dx = tx; }
        float u = dx / rx, v = dy / ry, d = sqrtf(u * u + v * v);
        float cv = clampf((1 - d) * mr + .5f, 0, 1);
        if (cv > 0) bl(px, py, col, (int)(cv * alpha * 255));
    }
}
static void circle(float cx, float cy, float r, u32 col, float alpha) { ellipse(cx, cy, r, r, 0, col, alpha); }
static void ring(float cx, float cy, float r, float th, u32 col, float alpha) {
    cx = PX(cx); cy = PX(cy); r = SC(r); th = SC(th);
    float R = r + th + 2;
    for (int py = (int)(cy - R); py <= (int)(cy + R) + 1; py++) for (int px = (int)(cx - R); px <= (int)(cx + R) + 1; px++) {
        float d = fhyp(px + .5f - cx, py + .5f - cy);
        float cv = clampf(th / 2 + .5f - fabsf(d - r), 0, 1);
        if (cv > 0) bl(px, py, col, (int)(cv * alpha * 255));
    }
}
/* arc: angles in radians, clockwise from 3 o'clock (screen coords), round caps */
static void arc(float cx, float cy, float r, float th, float a0, float a1, u32 col, float alpha) {
    float sw = a1 - a0; if (sw <= 0) return;
    float X = PX(cx), Y = PX(cy), Rp = SC(r), T = SC(th);
    float R = Rp + T + 2;
    for (int py = (int)(Y - R); py <= (int)(Y + R) + 1; py++) for (int px = (int)(X - R); px <= (int)(X + R) + 1; px++) {
        float dx = px + .5f - X, dy = py + .5f - Y, d = fhyp(dx, dy);
        float cv = clampf(T / 2 + .5f - fabsf(d - Rp), 0, 1);
        if (cv <= 0) continue;
        float an = atan2f(dy, dx) - a0; while (an < 0) an += 2 * PI_F; while (an >= 2 * PI_F) an -= 2 * PI_F;
        if (an > sw) {
            float e0 = fhyp(dx - cosf(a0) * Rp, dy - sinf(a0) * Rp), e1 = fhyp(dx - cosf(a1) * Rp, dy - sinf(a1) * Rp);
            float ec = clampf(T / 2 + .5f - fminf(e0, e1), 0, 1); cv = fminf(cv, ec);
            if (cv <= 0) continue;
        }
        bl(px, py, col, (int)(cv * alpha * 255));
    }
}
static void capsule(float x0, float y0, float x1, float y1, float r0, float r1, u32 col, float alpha) {
    x0 = PX(x0); y0 = PX(y0); x1 = PX(x1); y1 = PX(y1); r0 = SC(r0); r1 = SC(r1);
    float dx = x1 - x0, dy = y1 - y0, L2 = dx * dx + dy * dy; if (L2 < 1e-6f) L2 = 1e-6f;
    float R = fmaxf(r0, r1) + 2;
    for (int py = (int)(fminf(y0, y1) - R); py <= (int)(fmaxf(y0, y1) + R) + 1; py++) for (int px = (int)(fminf(x0, x1) - R); px <= (int)(fmaxf(x0, x1) + R) + 1; px++) {
        float t = ((px + .5f - x0) * dx + (py + .5f - y0) * dy) / L2; t = clampf(t, 0, 1);
        float qx = x0 + t * dx, qy = y0 + t * dy, r = r0 + (r1 - r0) * t;
        float cv = clampf(.5f - (fhyp(px + .5f - qx, py + .5f - qy) - r), 0, 1);
        if (cv > 0) bl(px, py, col, (int)(cv * alpha * 255));
    }
}
static void poly(const float *p, int n, u32 col, float alpha) { /* convex, logical coords */
    float xs[16], ys[16]; float minx = 1e9, maxx = -1e9, miny = 1e9, maxy = -1e9; float area = 0;
    for (int i = 0; i < n; i++) { xs[i] = PX(p[2 * i]); ys[i] = PX(p[2 * i + 1]); minx = fminf(minx, xs[i]); maxx = fmaxf(maxx, xs[i]); miny = fminf(miny, ys[i]); maxy = fmaxf(maxy, ys[i]); }
    for (int i = 0; i < n; i++) { int j = (i + 1) % n; area += xs[i] * ys[j] - xs[j] * ys[i]; }
    float sg = area > 0 ? 1 : -1;
    for (int py = (int)miny - 1; py <= (int)maxy + 1; py++) for (int px = (int)minx - 1; px <= (int)maxx + 1; px++) {
        float dm = 1e9;
        for (int i = 0; i < n; i++) {
            int j = (i + 1) % n; float ex = xs[j] - xs[i], ey = ys[j] - ys[i], L = fhyp(ex, ey); if (L < 1e-6f) continue;
            float d = sg * (ex * (py + .5f - ys[i]) - ey * (px + .5f - xs[i])) / L; if (d < dm) dm = d;
            if (dm < -1) break;
        }
        float cv = clampf(dm + .5f, 0, 1);
        if (cv > 0) bl(px, py, col, (int)(cv * alpha * 255));
    }
}
/* soft radial blob: alpha falls (1-d)^pw ; edge fully soft */
static void soft(float cx, float cy, float R, u32 col, float alpha, float pw) {
    cx = PX(cx); cy = PX(cy); R = SC(R);
    for (int py = (int)(cy - R); py <= (int)(cy + R) + 1; py++) for (int px = (int)(cx - R); px <= (int)(cx + R) + 1; px++) {
        float d = fhyp(px + .5f - cx, py + .5f - cy) / R; if (d >= 1) continue;
        float f = 1 - d; if (pw == 2) f *= f; else f = powf(f, pw);
        int a = (int)(f * alpha * 255); if (a > 0) bl(px, py, col, a);
    }
}
static void puff(float cx, float cy, float R, u32 col, float alpha) {
    cx = PX(cx); cy = PX(cy); R = SC(R);
    for (int py = (int)(cy - R); py <= (int)(cy + R) + 1; py++) for (int px = (int)(cx - R); px <= (int)(cx + R) + 1; px++) {
        float d = fhyp(px + .5f - cx, py + .5f - cy) / R; if (d >= 1) continue;
        float t = clampf((1 - d) / .55f, 0, 1); t = t * t * (3 - 2 * t); int a = (int)(t * alpha * 255); if (a > 0) bl(px, py, col, a);
    }
}
static void glow_add(float cx, float cy, float R, u32 col, float alpha) {
    cx = PX(cx); cy = PX(cy); R = SC(R);
    for (int py = (int)(cy - R); py <= (int)(cy + R) + 1; py++) for (int px = (int)(cx - R); px <= (int)(cx + R) + 1; px++) {
        float d = fhyp(px + .5f - cx, py + .5f - cy) / R; if (d >= 1) continue;
        float f = (1 - d); f *= f; int a = (int)(f * alpha * 256); if (a > 0) addp(px, py, col, a);
    }
}
static void blur_rect(int x0, int y0, int x1, int y1, int rad, int passes) {
    if (x0 < 0) x0 = 0; if (y0 < 0) y0 = 0; if (x1 > PW) x1 = PW; if (y1 > PH) y1 = PH;
    int w = x1 - x0, h = y1 - y0; if (w < 4 || h < 4 || rad < 1) return;
    u32 *tmp = (u32 *)malloc((size_t)w * h * 4); if (!tmp) return;
    for (int ps = 0; ps < passes; ps++) {
        int win = 2 * rad + 1;
        for (int y = 0; y < h; y++) {
            u32 *row = fb + (size_t)(y0 + y) * PW + x0; u32 *out = tmp + (size_t)y * w;
            int sr = 0, sg = 0, sb = 0;
            for (int k = -rad; k <= rad; k++) { u32 c = row[k < 0 ? 0 : k >= w ? w - 1 : k]; sr += (c >> 16) & 255; sg += (c >> 8) & 255; sb += c & 255; }
            for (int x = 0; x < w; x++) {
                out[x] = 0xFF000000u | ((sr / win) << 16) | ((sg / win) << 8) | (sb / win);
                int a = x + rad + 1, b = x - rad; u32 ca = row[a >= w ? w - 1 : a], cb = row[b < 0 ? 0 : b];
                sr += ((ca >> 16) & 255) - ((cb >> 16) & 255); sg += ((ca >> 8) & 255) - ((cb >> 8) & 255); sb += (ca & 255) - (cb & 255);
            }
        }
        for (int x = 0; x < w; x++) {
            int sr = 0, sg = 0, sb = 0;
            for (int k = -rad; k <= rad; k++) { u32 c = tmp[(size_t)(k < 0 ? 0 : k >= h ? h - 1 : k) * w + x]; sr += (c >> 16) & 255; sg += (c >> 8) & 255; sb += c & 255; }
            for (int y = 0; y < h; y++) {
                fb[(size_t)(y0 + y) * PW + x0 + x] = 0xFF000000u | ((sr / win) << 16) | ((sg / win) << 8) | (sb / win);
                int a = y + rad + 1, b = y - rad; u32 ca = tmp[(size_t)(a >= h ? h - 1 : a) * w + x], cb = tmp[(size_t)(b < 0 ? 0 : b) * w + x];
                sr += ((ca >> 16) & 255) - ((cb >> 16) & 255); sg += ((ca >> 8) & 255) - ((cb >> 8) & 255); sb += (ca & 255) - (cb & 255);
            }
        }
    }
    free(tmp);
}

/* ---------- text (stb_truetype, glyph cache) ---------- */
typedef struct { stbtt_fontinfo fi; unsigned char *data; int ok; } GFont;
static GFont fonts[2]; /* 0 = light, 1 = regular */
typedef struct { int key; int w, h, xo, yo; float adv; u8 *bmp; } Glyph;
#define GCN 1536
static Glyph gc[GCN]; static int gc_used = 0;
static unsigned char *slurp(const char *path, long maxsz, long *len) {
    FILE *f = fopen(path, "rb"); if (!f) return NULL;
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    if (n <= 0 || n > maxsz) { fclose(f); return NULL; }
    unsigned char *b = (unsigned char *)malloc(n); if (!b) { fclose(f); return NULL; }
    if ((long)fread(b, 1, n, f) != n) { free(b); fclose(f); return NULL; }
    fclose(f); if (len) *len = n; return b;
}
static int load_font(GFont *f, const char *path) {
    if (!path || !*path) return 0;
    unsigned char *d = slurp(path, 2500000, NULL); if (!d) return 0;
    if (!stbtt_InitFont(&f->fi, d, stbtt_GetFontOffsetForIndex(d, 0))) { free(d); return 0; }
    f->data = d; f->ok = 1; return 1;
}
static int fc_match(const char *pat, char *out, int n) {
    char cmd[200]; snprintf(cmd, sizeof cmd, "fc-match -f '%%{file}' '%s' 2>/dev/null", pat);
    FILE *p = popen(cmd, "r"); if (!p) return 0;
    int k = (int)fread(out, 1, n - 1, p); pclose(p); out[k > 0 ? k : 0] = 0; return k > 0;
}
static void init_fonts(const char *want_light, const char *want_reg) {
    char path[512];
    const char *c0[] = { want_light, getenv("SKYGLASS_FONT_LIGHT") };
    for (int i = 0; i < 2; i++) if (!fonts[0].ok && c0[i]) load_font(&fonts[0], c0[i]);
    if (!fonts[0].ok && fc_match("sans-serif:light", path, sizeof path)) load_font(&fonts[0], path);
    const char *c1[] = { want_reg, getenv("SKYGLASS_FONT") };
    for (int i = 0; i < 2; i++) if (!fonts[1].ok && c1[i]) load_font(&fonts[1], c1[i]);
    if (!fonts[1].ok && fc_match("sans-serif", path, sizeof path)) load_font(&fonts[1], path);
    const char *fb_[] = { "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "/usr/share/fonts/TTF/DejaVuSans.ttf", "/usr/share/fonts/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf", "/usr/share/fonts/noto/NotoSans-Regular.ttf", NULL };
    for (int i = 0; fb_[i] && !fonts[1].ok; i++) load_font(&fonts[1], fb_[i]);
    if (!fonts[0].ok) fonts[0] = fonts[1];
}
static int u8next(const char **s) {
    const unsigned char *p = (const unsigned char *)*s; int c = *p;
    if (c < 0x80) { (*s)++; return c; }
    if ((c >> 5) == 6 && p[1]) { *s += 2; return ((c & 31) << 6) | (p[1] & 63); }
    if ((c >> 4) == 14 && p[1] && p[2]) { *s += 3; return ((c & 15) << 12) | ((p[1] & 63) << 6) | (p[2] & 63); }
    (*s)++; return '?';
}
static Glyph *getglyph(int fid, float px, int cp) {
    int key = (fid << 30) ^ ((int)(px * 4) << 17) ^ cp;
    unsigned h = ((unsigned)key * 2654435761u) % GCN;
    for (int i = 0; i < GCN; i++) {
        Glyph *g = &gc[(h + i) % GCN];
        if (g->key == key && g->bmp != (u8 *)1) return g;
        if (g->bmp == NULL && g->key == 0) {
            GFont *f = &fonts[fid]; float sc = stbtt_ScaleForPixelHeight(&f->fi, px);
            int adv, lsb; stbtt_GetCodepointHMetrics(&f->fi, cp, &adv, &lsb);
            g->key = key; g->adv = adv * sc; g->bmp = stbtt_GetCodepointBitmap(&f->fi, sc, sc, cp, &g->w, &g->h, &g->xo, &g->yo);
            if (!g->bmp) g->bmp = (u8 *)2;
            gc_used++; return g;
        }
    }
    return &gc[0];
}
static float text_w(int fid, float size, const char *s, float spacing) {
    float px = size * S, x = 0; GFont *f = &fonts[fid]; if (!f->ok) return 0; int prev = 0;
    float sc = stbtt_ScaleForPixelHeight(&f->fi, px);
    while (*s) { int cp = u8next(&s); Glyph *g = getglyph(fid, px, cp); if (prev) x += stbtt_GetCodepointKernAdvance(&f->fi, prev, cp) * sc; x += g->adv + spacing * S; prev = cp; }
    return x / S;
}
/* anchor 0 left, 1 center, 2 right ; y is the baseline */
static void text(int fid, float size, float x, float y, const char *s, u32 col, float alpha, float spacing, int anchor) {
    GFont *f = &fonts[fid]; if (!f->ok) return;
    float w = text_w(fid, size, s, spacing);
    if (anchor == 1) x -= w / 2; else if (anchor == 2) x -= w;
    float px = size * S, cx = PX(x), cy = PX(y); int prev = 0; float sc = stbtt_ScaleForPixelHeight(&f->fi, px);
    while (*s) {
        int cp = u8next(&s); Glyph *g = getglyph(fid, px, cp);
        if (prev) cx += stbtt_GetCodepointKernAdvance(&f->fi, prev, cp) * sc;
        if (g->bmp && g->bmp != (u8 *)2) {
            int gx = (int)floorf(cx + .5f) + g->xo, gy = (int)floorf(cy + .5f) + g->yo;
            for (int j = 0; j < g->h; j++) for (int i = 0; i < g->w; i++) { int a = g->bmp[j * g->w + i]; if (a) bl(gx + i, gy + j, col, (int)(a * alpha)); }
        }
        cx += g->adv + spacing * S; prev = cp;
    }
}
static void text_shadow(int fid, float size, float x, float y, const char *s, u32 col, float alpha, float spacing, int anchor) {
    text(fid, size, x, y + 1.5f, s, 0x000000, .28f * alpha, spacing, anchor);
    text(fid, size, x, y, s, col, alpha, spacing, anchor);
}

/* ======================================================================
 *  weather model, config, network (curl subprocess, no libcurl)
 * ====================================================================== */
/* idk why this keep failing on missing connection interfaces*/
enum { C_CLEAR, C_PARTLY, C_CLOUDY, C_FOG, C_DRIZZLE, C_RAIN, C_STORM, C_SNOW, C_BLIZZARD, C_SLEET, C_HAIL, C_DUST, C_HEAT, NCOND };
static const char *cond_label[NCOND] = { "Clear sky", "Partly cloudy", "Overcast", "Foggy", "Drizzle", "Rain", "Thunderstorm", "Snow", "Blizzard", "Sleet", "Hail", "Dust storm", "Scorching heat" };
static const char *cond_name[NCOND] = { "clear", "partly", "cloudy", "fog", "drizzle", "rain", "storm", "snow", "blizzard", "sleet", "hail", "dust", "heat" };
/* cover dark rain snow hail fog dust storm wind */
static const float CP[NCOND][9] = {
    { .04f, 0, 0, 0, 0, 0, 0, 0, 8 }, { .42f, .08f, 0, 0, 0, 0, 0, 0, 14 }, { .88f, .35f, 0, 0, 0, .05f, 0, 0, 16 }, { .55f, .2f, 0, 0, 0, 1, 0, 0, 4 },
    { .85f, .42f, .22f, 0, 0, .15f, 0, 0, 12 }, { .95f, .62f, .7f, 0, 0, .12f, 0, 0, 20 }, { 1, .95f, 1, 0, 0, .1f, 0, 1, 38 }, { .85f, .3f, 0, .55f, 0, .18f, 0, 0, 10 },
    { 1, .45f, 0, 1, 0, .45f, 0, 0, 55 }, { .95f, .55f, .45f, .35f, 0, .2f, 0, 0, 22 }, { 1, .85f, .45f, 0, 1, .1f, 0, .6f, 34 }, { .25f, .25f, 0, 0, 0, 0, 1, 0, 45 }, { 0, 0, 0, 0, 0, 0, 0, 0, 6 } };
static const unsigned char TWC_ICON[48] = { 6, 6, 6, 6, 6, 9, 9, 9, 4, 4, 5, 5, 5, 7, 7, 8, 7, 10, 9, 11, 3, 3, 3, 2, 2, 7, 2, 2, 2, 1, 1, 0, 0, 0, 0, 10, 12, 6, 6, 5, 5, 7, 7, 8, 0, 5, 7, 6 };
static int wmo_cond(int c) {
    if (c <= 1) return C_CLEAR; if (c == 2) return C_PARTLY; if (c == 3) return C_CLOUDY; if (c == 45 || c == 48) return C_FOG;
    if (c >= 51 && c <= 55) return C_DRIZZLE; if (c == 56 || c == 57 || c == 66 || c == 67) return C_SLEET;
    if ((c >= 61 && c <= 65) || (c >= 80 && c <= 82)) return C_RAIN; if ((c >= 71 && c <= 77) || c == 85 || c == 86) return C_SNOW;
    if (c == 95) return C_STORM; if (c == 96 || c == 99) return C_HAIL; return C_CLOUDY;
}
typedef struct { char day[8]; float hi, lo; int cond, pop; } Fc;
typedef struct {
    float temp, feels, wind, wdir, hum, uv, press, aqi; int cond; char phrase[48]; float rise, set; int nf; Fc f[5];
    char src[40]; int valid; float tz_off; char tz[48]; int has_off;
} Weather;
typedef struct { char city[64], country[8], tz[48], key[96], font_l[300], font_r[300]; float lat, lon; int units, px, py, have_pos, have_city; float scale; int fps, below, ontop; } Config;
static Config cfg; static Weather W0;
static char cfg_path[400];

static void cfg_load(void) {
    memset(&cfg, 0, sizeof cfg); cfg.scale = 1; cfg.fps = 24; cfg.below = 0;
    const char *h = getenv("XDG_CONFIG_HOME"); char dir[360];
    if (h && *h) snprintf(dir, sizeof dir, "%s/skyglass", h); else snprintf(dir, sizeof dir, "%s/.config/skyglass", getenv("HOME") ? getenv("HOME") : ".");
    snprintf(cfg_path, sizeof cfg_path, "%s/config", dir);
    FILE *f = fopen(cfg_path, "r"); if (!f) return;
    char line[400];
    while (fgets(line, sizeof line, f)) {
        char *e = strchr(line, '='); if (!e) continue; *e++ = 0; char *nl = strchr(e, '\n'); if (nl) *nl = 0;
        if (!strcmp(line, "city")) { snprintf(cfg.city, sizeof cfg.city, "%s", e); cfg.have_city = 1; }
        else if (!strcmp(line, "country")) snprintf(cfg.country, sizeof cfg.country, "%s", e);
        else if (!strcmp(line, "tz")) snprintf(cfg.tz, sizeof cfg.tz, "%s", e);
        else if (!strcmp(line, "lat")) cfg.lat = atof(e); else if (!strcmp(line, "lon")) cfg.lon = atof(e);
        else if (!strcmp(line, "units")) cfg.units = atoi(e); else if (!strcmp(line, "api_key")) snprintf(cfg.key, sizeof cfg.key, "%s", e);
        else if (!strcmp(line, "x")) { cfg.px = atoi(e); cfg.have_pos = 1; } else if (!strcmp(line, "y")) cfg.py = atoi(e);
        else if (!strcmp(line, "scale")) cfg.scale = atof(e); else if (!strcmp(line, "fps")) cfg.fps = atoi(e);
        else if (!strcmp(line, "below")) cfg.below = atoi(e); else if (!strcmp(line, "ontop")) cfg.ontop = atoi(e);
        else if (!strcmp(line, "font_light")) snprintf(cfg.font_l, sizeof cfg.font_l, "%s", e); else if (!strcmp(line, "font")) snprintf(cfg.font_r, sizeof cfg.font_r, "%s", e);
    }
    fclose(f);
    if (cfg.scale < .6f || cfg.scale > 4) cfg.scale = 1; if (cfg.fps < 5 || cfg.fps > 120) cfg.fps = 24;
}
static void cfg_save(void) {
    char dir[400]; snprintf(dir, sizeof dir, "%s", cfg_path); char *sl = strrchr(dir, '/'); if (!sl) return; *sl = 0;
    char up[400]; snprintf(up, sizeof up, "%s", dir); char *s2 = strrchr(up, '/'); if (s2) { *s2 = 0; mkdir(up, 0755); }
    mkdir(dir, 0755);
    FILE *f = fopen(cfg_path, "w"); if (!f) return;
    fprintf(f, "city=%s\ncountry=%s\ntz=%s\nlat=%.4f\nlon=%.4f\nunits=%d\nscale=%.2f\nfps=%d\nbelow=%d\nontop=%d\n", cfg.city, cfg.country, cfg.tz, cfg.lat, cfg.lon, cfg.units, cfg.scale, cfg.fps, cfg.below, cfg.ontop);
    if (cfg.key[0]) fprintf(f, "api_key=%s\n", cfg.key);
    if (cfg.have_pos) fprintf(f, "x=%d\ny=%d\n", cfg.px, cfg.py);
    if (cfg.font_l[0]) fprintf(f, "font_light=%s\n", cfg.font_l);
    if (cfg.font_r[0]) fprintf(f, "font=%s\n", cfg.font_r);
    fclose(f);
}

/* ---------- time at the chosen city ---------- */
static void city_time(double off_hours, struct tm *out) {
    time_t t = time(NULL) + (time_t)(off_hours * 3600);
    if (cfg.tz[0]) { setenv("TZ", cfg.tz, 1); tzset(); localtime_r(&t, out); }
    else { t += (time_t)(roundf(cfg.lon / 15) * 3600); gmtime_r(&t, out); }
}
static float utc_off_hours(void) {
    time_t t = time(NULL); struct tm a, b;
    if (cfg.tz[0]) { setenv("TZ", cfg.tz, 1); tzset(); localtime_r(&t, &a); gmtime_r(&t, &b); return (float)((mktime(&a) - mktime(&b)) / 3600.0) * 1.0f + 0; }
    return roundf(cfg.lon / 15);
}
static void sun_times(float lat, float lon, int yday, float off, float *rise, float *set) {
    float decl = 23.44f * PI_F / 180 * sinf(2 * PI_F * (284 + yday) / 365);
    float la = clampf(lat, -66, 66) * PI_F / 180;
    float c = (cosf(90.833f * PI_F / 180) - sinf(la) * sinf(decl)) / (cosf(la) * cosf(decl)); c = clampf(c, -1, 1);
    float H = acosf(c) * 180 / PI_F / 15;
    float B = 2 * PI_F * (yday - 81) / 364, eot = (9.87f * sinf(2 * B) - 7.53f * cosf(B) - 1.5f * sinf(B)) / 60;
    float noon = 12 - lon / 15 + off - eot; *rise = noon - H; *set = noon + H;
}
static float moon_phase(time_t t) { double d = difftime(t, 947182440) / 86400.0; double p = fmod(d / 29.530588853, 1.0); if (p < 0) p += 1; return (float)p; }
static const char *moon_name(float p) { static const char *n[] = { "New moon", "Waxing crescent", "First quarter", "Waxing gibbous", "Full moon", "Waning gibbous", "Last quarter", "Waning crescent" }; return n[(int)(p * 8 + .5f) % 8]; }
static const char *DAYS3[] = { "SUN", "MON", "TUE", "WED", "THU", "FRI", "SAT" };

/* ---------- JSON scraping (tiny, tolerant) ---------- */
static const char *jkey(const char *s, const char *key) {
    if (!s) return NULL; char pat[80]; snprintf(pat, sizeof pat, "\"%s\"", key); const char *p = strstr(s, pat); if (!p) return NULL;
    p += strlen(pat); while (*p == ' ' || *p == ':') p++; return p;
}
static double jnum(const char *p, double def) { if (!p) return def; char *e; double v = strtod(p, &e); return e == p ? def : v; }
static int jstr(const char *p, char *out, int n) {
    if (!p || *p != '"') { if (n) out[0] = 0; return 0; } p++; int i = 0;
    while (*p && *p != '"' && i < n - 1) { if (*p == '\\' && p[1]) p++; out[i++] = *p++; } out[i] = 0; return 1;
}
static const char *jarr(const char *p, int idx) {
    if (!p || *p != '[') return NULL; p++; int depth = 0, i = 0;
    while (*p) {
        while (*p == ' ' || *p == '\n') p++;
        if (*p == ']') return NULL;
        if (i == idx) return p;
        int in = 0;
        while (*p) {
            if (*p == '"') in = !in;
            else if (!in) { if (*p == '[' || *p == '{') depth++; else if (*p == ']' || *p == '}') { if (depth == 0) return NULL; depth--; } else if (*p == ',' && depth == 0) break; }
            p++;
        }
        if (*p == ',') p++; i++;
    }
    return NULL;
}
static float hm_of(const char *p) { /* "2026-10-10T07:12..." -> 7.2 */
    char b[48]; if (!jstr(p, b, sizeof b) || strlen(b) < 16) return -1; return atoi(b + 11) + atoi(b + 14) / 60.f;
}
static int weekday_of(const char *ymd) { struct tm t; memset(&t, 0, sizeof t); t.tm_year = atoi(ymd) - 1900; t.tm_mon = atoi(ymd + 5) - 1; t.tm_mday = atoi(ymd + 8); t.tm_hour = 12; mktime(&t); return t.tm_wday; }
/*parsing fails with an error if no connection instead of no connection msg*/
static int parse_openmeteo(const char *b, Weather *w) {
    const char *cur = strstr(b, "\"current\":{"); const char *dl = strstr(b, "\"daily\":{"); if (!cur || !dl) return 0;
    cur += 10; dl += 8;
    w->temp = (float)jnum(jkey(cur, "temperature_2m"), 0); w->feels = (float)jnum(jkey(cur, "apparent_temperature"), w->temp);
    w->hum = (float)jnum(jkey(cur, "relative_humidity_2m"), 50); w->wind = (float)jnum(jkey(cur, "wind_speed_10m"), 0); w->wdir = (float)jnum(jkey(cur, "wind_direction_10m"), 0);
    w->press = (float)jnum(jkey(cur, "surface_pressure"), 1013); w->cond = wmo_cond((int)jnum(jkey(cur, "weather_code"), 3));
    w->uv = (float)jnum(jarr(jkey(dl, "uv_index_max"), 0), 0);
    float r = hm_of(jarr(jkey(dl, "sunrise"), 0)), s = hm_of(jarr(jkey(dl, "sunset"), 0)); if (r >= 0 && s >= 0) { w->rise = r; w->set = s; }
    const char *off = jkey(b, "utc_offset_seconds"); if (off) { w->tz_off = (float)jnum(off, 0) / 3600; w->has_off = 1; }
    jstr(jkey(b, "timezone"), w->tz, sizeof w->tz);
    w->nf = 0;
    for (int i = 0; i < 5; i++) {
        const char *d = jarr(jkey(dl, "time"), i); char ds[16]; if (!d || !jstr(d, ds, sizeof ds)) break;
        strcpy(w->f[i].day, DAYS3[weekday_of(ds)]);
        w->f[i].hi = (float)jnum(jarr(jkey(dl, "temperature_2m_max"), i), 0); w->f[i].lo = (float)jnum(jarr(jkey(dl, "temperature_2m_min"), i), 0);
        w->f[i].cond = wmo_cond((int)jnum(jarr(jkey(dl, "weather_code"), i), 3)); w->f[i].pop = (int)jnum(jarr(jkey(dl, "precipitation_probability_max"), i), 0);
        w->nf++;
    }
    snprintf(w->src, sizeof w->src, "By-R1y3n"); return 1;
}
static int parse_twc(const char *cb, const char *fb_, Weather *w) {
    if (!jkey(cb, "temperature")) return 0;
    w->temp = (float)jnum(jkey(cb, "temperature"), 0); w->feels = (float)jnum(jkey(cb, "temperatureFeelsLike"), w->temp);
    int ic = (int)jnum(jkey(cb, "iconCode"), 26); w->cond = (ic >= 0 && ic < 48) ? TWC_ICON[ic] : C_CLOUDY;
    w->wind = (float)jnum(jkey(cb, "windSpeed"), 0); w->wdir = (float)jnum(jkey(cb, "windDirection"), 0); w->hum = (float)jnum(jkey(cb, "relativeHumidity"), 50);
    w->uv = (float)jnum(jkey(cb, "uvIndex"), 0); w->press = (float)jnum(jkey(cb, "pressureAltimeter"), 1013);
    jstr(jkey(cb, "wxPhraseLong"), w->phrase, sizeof w->phrase);
    float r = hm_of(jkey(cb, "sunriseTimeLocal")), s = hm_of(jkey(cb, "sunsetTimeLocal")); if (r >= 0 && s >= 0) { w->rise = r; w->set = s; }
    w->nf = 0;
    if (fb_) {
        const char *dow = jkey(fb_, "dayOfWeek"), *hi = jkey(fb_, "temperatureMax"), *lo = jkey(fb_, "temperatureMin"); const char *dp = strstr(fb_, "\"daypart\""); 
        const char *ico = dp ? jkey(dp, "iconCode") : NULL, *pc = dp ? jkey(dp, "precipChance") : NULL;
        for (int i = 0; i < 5 && dow; i++) {
            char dn[16]; if (!jstr(jarr(dow, i), dn, sizeof dn)) break;
            snprintf(w->f[i].day, sizeof w->f[i].day, "%.3s", dn); for (char *c = w->f[i].day; *c; c++) if (*c >= 'a' && *c <= 'z') *c -= 32;
            w->f[i].hi = (float)jnum(jarr(hi, i), w->temp); w->f[i].lo = (float)jnum(jarr(lo, i), w->temp);
            int k = (int)jnum(jarr(ico, 2 * i), -1); if (k < 0) k = (int)jnum(jarr(ico, 2 * i + 1), 26);
            w->f[i].cond = (k >= 0 && k < 48) ? TWC_ICON[k] : C_CLOUDY; w->f[i].pop = (int)jnum(jarr(pc, 2 * i), 0); w->nf++;
        }
    }
    snprintf(w->src, sizeof w->src, "The Weather Channel"); return 1;
}
static void demo_weather(Weather *w) {
    struct tm tm; city_time(0, &tm); u32 sv = rs; rs = hash_str(cfg.city) ^ (tm.tm_yday * 977 + tm.tm_hour / 4 + 17); if (!rs) rs = 1;
    float base = 30 - fabsf(cfg.lat) * .45f + 8 * cosf((tm.tm_yday - 200) / 365.f * 6.283f) * (cfg.lat >= 0 ? 1 : -1);
    int pool[] = { C_CLEAR, C_CLEAR, C_PARTLY, C_CLOUDY, C_RAIN, C_STORM, base < 6 ? C_SNOW : C_PARTLY, C_FOG };
    w->cond = pool[(int)(rnd() * 8) % 8]; w->temp = base + rndr(-3, 3); w->feels = w->temp - 1.5f; w->wind = rndr(4, 30); w->wdir = rndr(0, 359); w->hum = rndr(35, 90);
    w->uv = floorf(rndr(1, 9)); w->press = rndr(1002, 1025); w->aqi = floorf(rndr(15, 90)); w->nf = 5;
    for (int i = 0; i < 5; i++) {
        w->f[i].cond = (int)(rnd() * 11) % 11; float hi = base + rndr(-1, 5); w->f[i].hi = hi; w->f[i].lo = hi - rndr(5, 11);
        w->f[i].pop = (w->f[i].cond >= C_DRIZZLE && w->f[i].cond <= C_HAIL) ? (int)rndr(30, 90) : (int)rndr(0, 20); strcpy(w->f[i].day, DAYS3[(tm.tm_wday + i) % 7]);
    }
    snprintf(w->src, sizeof w->src, "Demo data"); w->phrase[0] = 0; rs = sv;
}
/* this once has a race condition issue*/
/* ---------- async downloads through curl (non-blocking pipe) ---------- */
typedef struct { FILE *fp; char *buf; size_t len, cap; int active, kind; time_t t0; } Job;
static Job job; static char *job_keep; 
static void urlenc(const char *s, char *o, int n) {
    int k = 0; for (; *s && k < n - 4; s++) { unsigned char c = *s; if (isalnum(c) || c == '-' || c == '_' || c == '.' || c == '~') o[k++] = c; else k += sprintf(o + k, "%%%02X", c); } o[k] = 0;
}
static int job_start(const char *url, int kind) {
    if (job.active) return 0;
    char cmd[1500]; snprintf(cmd, sizeof cmd, "curl -sfL -m 12 -A skyglass/1.0 '%s' 2>/dev/null", url);
    job.fp = popen(cmd, "r"); if (!job.fp) return 0;
    fcntl(fileno(job.fp), F_SETFL, fcntl(fileno(job.fp), F_GETFL) | O_NONBLOCK);
    job.len = 0; if (!job.buf) { job.cap = 65536; job.buf = (char *)malloc(job.cap); } job.buf[0] = 0; job.active = 1; job.kind = kind; job.t0 = time(NULL); return 1;
}
/* returns 0 pending, 1 finished (job.buf valid), -1 failed */
static int job_poll(void) {
    if (!job.active) return 0;
    char tmp[4096];
    for (;;) {
        ssize_t n = read(fileno(job.fp), tmp, sizeof tmp);
        if (n > 0) { if (job.len + n + 1 > job.cap) { if (job.cap > 4000000) n = 0; else { job.cap *= 2; job.buf = (char *)realloc(job.buf, job.cap); } } if (n > 0) { memcpy(job.buf + job.len, tmp, n); job.len += n; job.buf[job.len] = 0; continue; } }
        if (n == 0) { pclose(job.fp); job.fp = NULL; job.active = 0; return job.len > 20 ? 1 : -1; }
        if (errno == EAGAIN || errno == EWOULDBLOCK) { if (time(NULL) - job.t0 > 20) { pclose(job.fp); job.fp = NULL; job.active = 0; return -1; } return 0; }
        pclose(job.fp); job.fp = NULL; job.active = 0; return -1;
    }
}

typedef struct { char name[64], country[8], tz[48], admin[48]; float lat, lon; } CityHit;
static CityHit hits[6]; static int nhits = 0;
static void parse_hits_openmeteo(const char *b) {
    nhits = 0; const char *p = strstr(b, "\"results\""); if (!p) return;
    while (nhits < 6) {
        const char *o = strstr(p, "{\"id\""); if (!o) break; const char *nx = strstr(o + 5, "{\"id\""); char seg[1200]; size_t n = nx ? (size_t)(nx - o) : strlen(o); if (n > 1190) n = 1190; memcpy(seg, o, n); seg[n] = 0;
        CityHit *h = &hits[nhits]; memset(h, 0, sizeof *h);
        if (!jstr(jkey(seg, "name"), h->name, sizeof h->name)) { p = o + 5; continue; }
        jstr(jkey(seg, "country_code"), h->country, sizeof h->country); jstr(jkey(seg, "timezone"), h->tz, sizeof h->tz); jstr(jkey(seg, "admin1"), h->admin, sizeof h->admin);
        h->lat = (float)jnum(jkey(seg, "latitude"), 0); h->lon = (float)jnum(jkey(seg, "longitude"), 0); nhits++; p = o + 5;
    }
}
static void parse_hits_twc(const char *b) {
    nhits = 0; const char *c = jkey(b, "city"), *la = jkey(b, "latitude"), *lo = jkey(b, "longitude"), *cc = jkey(b, "countryCode"), *tz = jkey(b, "ianaTimeZone"), *ad = jkey(b, "adminDistrict");
    for (int i = 0; i < 6 && c; i++) {
        CityHit *h = &hits[nhits]; memset(h, 0, sizeof *h); if (!jstr(jarr(c, i), h->name, sizeof h->name)) break;
        jstr(jarr(cc, i), h->country, sizeof h->country); jstr(jarr(tz, i), h->tz, sizeof h->tz); jstr(jarr(ad, i), h->admin, sizeof h->admin);
        h->lat = (float)jnum(jarr(la, i), 0); h->lon = (float)jnum(jarr(lo, i), 0); nhits++;
    }
}

/* ======================================================================
 *  the living scene - thanks to RAD GAME Tools for the render stuff
 * ====================================================================== */
#define Y_H 312.f
#define Y_RAIL 316.f
#define Y_L0 321.f
#define Y_L1 346.f
#define PANEL_Y 354.f

typedef struct { float cover, dark, rain, snow, hail, fog, dust, storm, heat, wind, snowc, wet, aur; } Env;
static Env E, T; static int g_cond = C_CLEAR;
static float g_alt = .5f, g_night = 0, g_f = .5f, g_hour = 12, g_rise = 6.5f, g_set = 19.5f, g_moon = .3f, g_temp = 20, g_uv = 5, g_wsign = 1;
static int g_isday = 1, g_season = 0; /* 0 autumn 1 green 2 winter */
static float Lr = 1, Lg = 1, Lb = 1, g_t = 0, g_lamp = 0;
static u32 skyTop, skyBot, g_srcc = 0xFFF4D6; static float g_srcx = 190, g_srcs = 0;
static float g_flash = 0, g_flash_t = 9, next_strike = 3, g_force_aur = 0; static int thunder_pending = 0;
static float bolt_x[48], bolt_y[48]; static int bolt_n = 0;
static char g_msg[64]; static float g_msg_t = 0;
static void say(const char *m, float t) { snprintf(g_msg, sizeof g_msg, "%s", m); g_msg_t = t; }

static const float SKYK[7][7] = { { -.35f, 3, 5, 18, 9, 13, 34 }, { -.12f, 10, 13, 42, 34, 32, 84 }, { -.03f, 46, 36, 108, 214, 84, 104 }, { .04f, 84, 86, 176, 255, 128, 74 },
    { .16f, 66, 118, 204, 255, 206, 150 }, { .40f, 48, 118, 214, 150, 205, 248 }, { 1, 26, 96, 204, 132, 196, 246 } };
static const float LIGK[7][4] = { { -.35f, .17f, .21f, .40f }, { -.12f, .27f, .30f, .52f }, { -.03f, .70f, .52f, .62f }, { .05f, 1, .72f, .58f }, { .20f, 1, .90f, .80f }, { .50f, 1, 1, 1 }, { 1, 1, 1, 1 } };
static void kinterp(const float *keys, int stride, int n, float a, float *out) {
    int dim = stride - 1;
    if (a <= keys[0]) { for (int i = 0; i < dim; i++) out[i] = keys[1 + i]; return; }
    const float *last = keys + (n - 1) * stride; if (a >= last[0]) { for (int i = 0; i < dim; i++) out[i] = last[1 + i]; return; }
    for (int k = 0; k < n - 1; k++) { const float *k0 = keys + k * stride, *k1 = k0 + stride; if (a >= k0[0] && a <= k1[0]) { float t = (a - k0[0]) / (k1[0] - k0[0]); for (int i = 0; i < dim; i++) out[i] = k0[1 + i] + (k1[1 + i] - k0[1 + i]) * t; return; } }
}
static void grade(float *r, float *g, float *b) {
    float lum = .3f * *r + .59f * *g + .11f * *b, k = clampf(E.cover * .8f, 0, 1);
    *r += (lum - *r) * k; *g += (lum - *g) * k; *b += (lum - *b) * k;
    if (E.fog > .02f) { float f = E.fog * .7f, t = lum * .92f + 22; *r += (t - *r) * f; *g += (t - *g) * f; *b += (t * 1.03f - *b) * f; }
    if (E.dust > .02f) { float d = E.dust * .95f, s = clampf(lum / 130, .12f, 1.4f); *r += (214 * s - *r) * d; *g += (138 * s - *g) * d; *b += (70 * s - *b) * d; }
    if (E.heat > .02f) { float h = E.heat; *r += (255 - *r) * .28f * h; *g += (222 - *g) * .22f * h; *b += (170 - *b) * .12f * h; }
    float dk = 1 - .62f * E.dark; *r *= dk; *g *= dk; *b *= dk;
}
static u32 gradec(float r, float g, float b) { grade(&r, &g, &b); return RGB((int)clampf(r, 0, 255), (int)clampf(g, 0, 255), (int)clampf(b, 0, 255)); }
static inline u32 LT(u32 c) { return scalec(c, Lr, Lg, Lb); }

/* tables built once */
static u8 ntex[128 * 128]; static float lat1[512];
static float vn1(float x) { int i = (int)floorf(x); float f = x - i; f = f * f * (3 - 2 * f); return lat1[i & 511] * (1 - f) + lat1[(i + 1) & 511] * f; }
static float fbm1(float x, int o) { float s = 0, a = 1, t = 0, fq = 1; for (int k = 0; k < o; k++) { s += a * vn1(x * fq + k * 17.3f); t += a; a *= .5f; fq *= 2; } return s / t; }
static void init_tables(u32 seed) {
    u32 sv = rs; rs = seed ? seed : 1;
    for (int i = 0; i < 512; i++) lat1[i] = rnd();
    float g[34 * 34]; for (int i = 0; i < 34 * 34; i++) g[i] = rnd();
    for (int y = 0; y < 128; y++) for (int x = 0; x < 128; x++) {
        float v = 0, a = 1, tt = 0;
        for (int o = 0; o < 3; o++) { int f = 4 << o; float fx = x * f / 128.f, fy = y * f / 128.f; int ix = (int)fx, iy = (int)fy; float tx = fx - ix, ty = fy - iy; tx = tx * tx * (3 - 2 * tx); ty = ty * ty * (3 - 2 * ty);
            int xa = ix % 32, xb = (ix + 1) % 32, ya = iy % 32, yb = (iy + 1) % 32; float n = (g[ya * 34 + xa] * (1 - tx) + g[ya * 34 + xb] * tx) * (1 - ty) + (g[yb * 34 + xa] * (1 - tx) + g[yb * 34 + xb] * tx) * ty; v += n * a; tt += a; a *= .5f; }
        ntex[y * 128 + x] = (u8)(v / tt * 255);
    }
    rs = sv;
}

/* ---------- scene data ---------- */
typedef struct { float x, w, h, rh; u32 col, roof; int nwin, on[3], ci[3]; float wx[3], wy[3]; float chx, chy; int kind; } House;
typedef struct { float x, y, h; int kind; float rv; } Tree;
typedef struct { float x, y, w; int n; float dx[7], dy[7], r[7]; float sp, th; int layer; } Cloud;
static House houses[44]; static int nhouses; static Tree trees[130]; static int ntrees; static Cloud clouds[14];
static float *mt0, *mt1, *hl; static int ridge_w;
static float stars[110][6]; static float dr[260][5], fl[170][6], dp[70][4], lv[16][6], sm[28][6], rg[40][3], ff[16][4], bats[3][5], bshr[5][3];
static int cat_house = 0; static float oak_x = 34, oak_y = 280;
typedef struct { int on; float hx; int dir, kind, ncar; float speed; u32 body, acc, carcol[14]; int horn; } Train;
static Train train; static float next_train = 6;
typedef struct { int on; float x, y, dir, v; float off[8][3]; int n; } Flock;
static Flock flock; static float next_flock = 8;
typedef struct { int on, state; float x, y, tx, t, lift, vx, vy; int said; float side; } Ufo;
static Ufo ufo; static float next_ufo = 90;
static float boat_x = 240, boat_dir = -1, duck_x[3] = { 120, 170, 290 }, duck_d[3] = { 1, -1, 1 }, sheep_x = 200, sheep_gone = 0, sheep_dir = 1;
static float udk_x = -20, udk_dir = 1; static int udk_on = 0; static float fish_t = -1, fish_x = 0, fish_y = 0, next_fish = 8;
static float tumble_x = -10, tumble_a = 0; static int tumble_on = 0;
static float owl_look = 0, owl_next = 2, owl_blink = 0, cat_blink = 0, cat_next = 4, shoot[5], next_shoot = 6; static int shoot_on = 0;
static float plane_x, plane_y, plane_d; static int plane_on = 0; static float next_plane = 25;
static float steam_dummy;

static void scene_init(u32 seed) {
    u32 sv = rs; rs = seed ? seed : 1; init_tables(seed ^ 0x9e3779b9u);
    for (int i = 0; i < 110; i++) { stars[i][0] = rndr(0, CW); stars[i][1] = rndr(8, Y_H - 40); stars[i][2] = powf(rnd(), 2.2f) * .9f + .1f; stars[i][3] = rnd() * 6; stars[i][4] = rndr(1, 4); stars[i][5] = (float)(rnd() < .3f ? 0xFFE8C8 : rnd() < .5f ? 0xC8DCFF : 0xFFFFFF); }
    free(mt0); free(mt1); free(hl); ridge_w = PW; mt0 = (float *)calloc(PW, 4); mt1 = (float *)calloc(PW, 4); hl = (float *)calloc(PW, 4);
    for (int x = 0; x < PW; x++) {
        float lx = x / S - MARG;
        float n = fbm1(lx * .0075f + 3.1f, 5), rid = 1 - fabsf(2 * n - 1); mt0[x] = Y_H - (14 + (.55f * rid + .45f * n) * 82);
        float n2 = fbm1(lx * .012f + 40.f, 5); mt1[x] = Y_H - (6 + n2 * 30 + vn1(lx * .35f) * 2);
        float n3 = fbm1(lx * .02f + 90.f, 4); hl[x] = Y_RAIL - 4 - (2 + n3 * 14);
    }
    nhouses = 0; float xs[2] = { .30f * CW, .70f * CW };
    for (int cl = 0; cl < 2; cl++) {
        float x = xs[cl] - CW * .11f, xe = xs[cl] + CW * .11f;
        while (x < xe && nhouses < 40) {
            House *h = &houses[nhouses++]; memset(h, 0, sizeof *h);
            h->x = x; h->w = rndr(8, 13); h->h = rndr(6, 11); h->rh = h->w * .42f;
            u32 bc[] = { RGB(228, 206, 170), RGB(198, 130, 98), RGB(190, 196, 204), RGB(214, 178, 108), RGB(236, 226, 206) }; u32 rc[] = { RGB(150, 66, 50), RGB(96, 74, 70), RGB(132, 84, 60), RGB(70, 76, 92) };
            h->col = bc[(int)(rnd() * 5) % 5]; h->roof = rc[(int)(rnd() * 4) % 4]; h->nwin = h->w > 10 ? 2 : 1;
            for (int k = 0; k < h->nwin; k++) { h->wx[k] = h->nwin == 2 ? h->w * (.2f + .45f * k) : h->w * .38f; h->wy[k] = h->h * .3f; h->on[k] = rnd() < .65f; h->ci[k] = (int)(rnd() * 4) % 4; }
            h->chx = h->w * (rnd() < .5f ? .62f : .28f); h->chy = rnd() < .75f ? 1 : 0; h->kind = 0;
            x += h->w + rndr(2, 6);
        }
    }
    int best = 0; float bd = 1e9; for (int i = 0; i < nhouses; i++) { float d = fabsf(houses[i].x - 225); if (houses[i].w > 9 && d < bd) { bd = d; best = i; } } cat_house = best;
    ntrees = 0; for (int i = 0; i < 120; i++) { Tree *t = &trees[ntrees++]; t->x = rndr(0, CW); t->h = rndr(7, 15); t->y = rndr(Y_RAIL - 12, Y_RAIL - 2); t->kind = rnd() < .55f; t->rv = rnd(); }
    for (int i = 0; i < 14; i++) {
        Cloud *c = &clouds[i]; c->layer = (int)(rnd() * 3) % 3; c->w = rndr(130, 250) * (.62f + .25f * c->layer); c->x = rndr(-c->w, CW); c->y = rndr(30, 190); c->n = 7 + (int)(rnd() * 3);
        for (int k = 0; k < c->n; k++) { float f = (float)k / (c->n - 1); c->dx[k] = c->w * (.1f + .8f * f); c->r[k] = c->w * rndr(.1f, .15f) * (1 - .25f * fabsf(f - .5f)); c->dy[k] = -c->r[k] * .55f * sinf(PI_F * f) + rndr(-3, 3); }
        c->sp = (.5f + c->layer * .5f) * rndr(.8f, 1.2f); c->th = (float)i / 14 * .95f;
    }
    for (int i = 0; i < 260; i++) { dr[i][0] = rndr(-CW * .3f, CW); dr[i][1] = rndr(0, CH); dr[i][2] = rndr(380, 620); dr[i][3] = rnd(); dr[i][4] = rndr(Y_L0, CH - 20); }
    for (int i = 0; i < 170; i++) { fl[i][0] = rndr(-60, CW + 60); fl[i][1] = rndr(0, CH); fl[i][2] = rndr(18, 46); fl[i][3] = rnd() * 6; fl[i][4] = rnd(); fl[i][5] = rndr(Y_L0, CH - 10); }
    for (int i = 0; i < 70; i++) { dp[i][0] = rndr(0, CW); dp[i][1] = rndr(120, CH - 10); dp[i][2] = rndr(.6f, 1.4f); dp[i][3] = rnd(); }
    for (int i = 0; i < 16; i++) lv[i][5] = -1;
    for (int i = 0; i < 28; i++) sm[i][4] = 99;
    for (int i = 0; i < 40; i++) rg[i][2] = 9;
    for (int i = 0; i < 16; i++) { ff[i][0] = rndr(0, CW); ff[i][1] = rndr(Y_L0 + 4, CH - 30); ff[i][2] = rnd() * 6; ff[i][3] = rndr(.5f, 1.4f); }
    for (int i = 0; i < 3; i++) { bats[i][0] = rndr(0, CW); bats[i][1] = rndr(40, 150); bats[i][2] = rndr(-40, 40); bats[i][3] = 0; bats[i][4] = rnd() * 6; }
    float bx[5] = { 98, 146, 210, 262, 332 }; for (int i = 0; i < 5; i++) { bshr[i][0] = bx[i] + rndr(-10, 10); bshr[i][1] = Y_L1 + rndr(2, 6); bshr[i][2] = rndr(7, 12); }
    memset(&train, 0, sizeof train); memset(&ufo, 0, sizeof ufo); memset(&flock, 0, sizeof flock); plane_on = 0; shoot_on = 0; tumble_on = 0; udk_on = 0; sheep_gone = 0; fish_t = -1;
    rs = sv;
}

static void train_spawn(int kind, int dir) {
    memset(&train, 0, sizeof train); train.on = 1; train.kind = kind >= 0 ? kind : (rnd() < .7f ? 0 : 1); train.dir = dir ? dir : (rnd() < .5f ? -1 : 1);
    if (train.kind == 0) { train.speed = rndr(230, 320); train.ncar = 5 + (int)(rnd() * 3); u32 bc[] = { RGB(232, 236, 244), RGB(225, 232, 240), RGB(240, 240, 235) }, ac[] = { RGB(214, 40, 52), RGB(30, 120, 220), RGB(20, 170, 140), RGB(240, 150, 20) };
        train.body = bc[(int)(rnd() * 3) % 3]; train.acc = ac[(int)(rnd() * 4) % 4]; }
    else { train.speed = rndr(70, 95); train.ncar = 9 + (int)(rnd() * 4); train.body = RGB(70, 78, 92); train.acc = RGB(240, 140, 30);
        u32 cc[] = { RGB(180, 60, 50), RGB(50, 110, 170), RGB(190, 150, 40), RGB(60, 140, 90), RGB(150, 150, 160), RGB(210, 100, 40) }; for (int i = 0; i < 14; i++) train.carcol[i] = cc[(int)(rnd() * 6) % 6]; }
    float len = train.kind == 0 ? 44 + train.ncar * 33 : 28 + train.ncar * 25; train.hx = train.dir == 1 ? -4 : CW + 4; (void)len;
}
static float train_len(void) { return train.kind == 0 ? 44 + train.ncar * 33.f : 28 + train.ncar * 25.f; }

static void strike(void) {
    next_strike = rndr(2, 7); float x = rndr(CW * .15f, CW * .85f), y = 22; bolt_n = 0; bolt_x[bolt_n] = x; bolt_y[bolt_n++] = y; float yg = Y_H - rndr(0, 6);
    while (y < yg && bolt_n < 46) { y += rndr(6, 11); x += rndr(-8, 8); bolt_x[bolt_n] = x; bolt_y[bolt_n++] = y; }
    g_flash_t = 0; thunder_pending = 1;
}

static void compute_env(void) {
    float v[6]; kinterp(&SKYK[0][0], 7, 7, g_alt, v);
    float tr = v[0], tg = v[1], tb = v[2], br = v[3], bg = v[4], bb = v[5];
    grade(&tr, &tg, &tb); grade(&br, &bg, &bb);
    float f = g_flash; if (f > 0) { tr += (200 - tr) * f * .5f; tg += (200 - tg) * f * .5f; tb += (220 - tb) * f * .5f; br += (210 - br) * f * .55f; bg += (214 - bg) * f * .55f; bb += (235 - bb) * f * .55f; }
    skyTop = RGB((int)clampf(tr, 0, 255), (int)clampf(tg, 0, 255), (int)clampf(tb, 0, 255)); skyBot = RGB((int)clampf(br, 0, 255), (int)clampf(bg, 0, 255), (int)clampf(bb, 0, 255));
    float l[3]; kinterp(&LIGK[0][0], 4, 7, g_alt, l); float dk = 1 - .42f * E.dark; Lr = l[0] * dk; Lg = l[1] * dk; Lb = l[2] * dk;
    g_srcx = CW * (.14f + .72f * g_f);
    if (g_isday) { g_srcc = mixc(RGB(255, 150, 90), RGB(255, 244, 214), smoothf(0, .45f, g_alt)); g_srcs = smoothf(-.02f, .25f, g_alt) * (1 - E.cover * .75f); }
    else { g_srcc = RGB(150, 172, 235); float il = (1 - cosf(2 * PI_F * g_moon)) / 2; g_srcs = .3f * g_night * (.3f + .7f * il) * (1 - E.cover * .7f); }
    g_lamp = clampf(.1f + g_night * .95f + E.dark * .55f + (1 - smoothf(0, .3f, g_alt)) * .3f, 0, 1);
}

/* ---------- drawing the world ---------- */
static void fill_sky(void) {
    int x0 = (int)(MARG * S), x1 = (int)((MARG + CW) * S), y0 = (int)(MARG * S), y1 = (int)((MARG + CH) * S), sh = (int)(SC(Y_H + 20));
    for (int y = y0; y < y1; y++) {
        float t = clampf((float)(y - y0) / sh, 0, 1); t = powf(t, 1.5f); u32 c = 0xFF000000u | mixc(skyTop, skyBot, t);
        u32 *row = fb + (size_t)y * PW; for (int x = x0; x < x1; x++) row[x] = c;
    }
}
static void draw_stars(void) {
    float sv = g_night * (1 - E.cover * .92f); if (sv < .03f) return;
    for (int i = 0; i < 110; i++) {
        float a = sv * stars[i][2] * (.65f + .35f * sinf(g_t * stars[i][4] + stars[i][3]));
        int ia = (int)(a * 255); if (ia < 6) continue; float x = PX(stars[i][0]), y = PX(stars[i][1]); u32 c = (u32)stars[i][5];
        bl((int)x, (int)y, c, ia); if (stars[i][2] > .7f) { bl((int)x + 1, (int)y, c, ia / 3); bl((int)x - 1, (int)y, c, ia / 3); bl((int)x, (int)y + 1, c, ia / 3); bl((int)x, (int)y - 1, c, ia / 3); }
    }
    if (shoot_on) { for (int i = 0; i < 12; i++) { float a = (1 - i / 12.f) * (1 - shoot[4] / .8f); soft(shoot[0] - shoot[2] * .02f * i, shoot[1] - shoot[3] * .02f * i, 1.8f, 0xFFFFFF, a, 1.5f); } }
}
static void draw_aurora(void) {
    if (E.aur < .03f || g_night < .3f) return; float av = E.aur * g_night * (1 - E.cover * .92f);
    for (int px = (int)(MARG * S); px < (int)((MARG + CW) * S); px += 2) {
        float lx = px / S - MARG;
        float yb = 150 + 22 * sinf(lx * .018f + g_t * .4f) + 14 * sinf(lx * .05f - g_t * .7f), hh = 85 + 30 * sinf(lx * .012f + g_t * .3f);
        float ray = .5f + .5f * sinf(lx * .1f + g_t * 1.3f + sinf(lx * .03f) * 3);
        for (float y = yb - hh; y < yb; y += 1.f / S) { float u = (y - (yb - hh)) / hh; int a = (int)(av * ray * u * u * 130); if (a < 3) continue; u32 c = mixc(RGB(170, 80, 255), RGB(70, 255, 150), u); bl(px, (int)PX(y), c, a); bl(px + 1, (int)PX(y), c, a); }
    }
}
static void draw_celestial(void) {
    float sx = g_srcx, sy = Y_H - 8 - (Y_H - 8 - 62) * sinf(PI_F * g_f);
    if (g_isday) {
        float R = (E.heat > .3f ? 19 : 15), vis = 1 - E.cover * .85f - E.dust * .3f; if (vis < 0) vis = 0;
        u32 sc = mixc(RGB(255, 110, 45), RGB(255, 246, 205), smoothf(0, .4f, g_alt)); if (E.heat > .2f) sc = mixc(sc, RGB(255, 150, 70), .4f * E.heat);
        soft(sx, sy, R * 6, sc, .55f * vis, 2.2f); soft(sx, sy, R * 2.6f, sc, .5f * vis, 1.6f);
        if (vis > .12f) { float da = clampf((vis - .12f) * 3, 0, 1); circle(sx, sy, R, sc, fminf(1, vis + .3f) * da); circle(sx, sy, R * .7f, RGB(255, 255, 240), .5f * vis * da); }
    } else {
        float vis = g_night * (1 - E.cover * .75f); if (vis < .05f) return; float R = 13;
        soft(sx, sy, R * 5, RGB(150, 180, 255), .35f * vis, 2.2f);
        float p = g_moon, cp = cosf(2 * PI_F * p); float X = PX(sx), Y = PX(sy), Rp = SC(R);
        for (int py = (int)(Y - Rp - 2); py <= (int)(Y + Rp + 2); py++) for (int px = (int)(X - Rp - 2); px <= (int)(X + Rp + 2); px++) {
            float dx = px + .5f - X, dy = py + .5f - Y, d = fhyp(dx, dy); float edge = clampf(Rp + .5f - d, 0, 1); if (edge <= 0) continue;
            float xn = dx / Rp, yn = dy / Rp, xr = sqrtf(fmaxf(0, 1 - yn * yn)); int lit = p < .5f ? (xn > cp * xr) : (xn < -cp * xr); if (p < .03f || p > .97f) lit = 0;
            if (lit) { float m = ntex[((py & 127) << 7) | (px * 3 & 127)] / 255.f; u32 c = mixc(RGB(240, 240, 220), RGB(176, 180, 176), clampf((m - .5f) * 3, 0, 1) * .6f); bl(px, py, c, (int)(255 * vis * edge)); }
            else bl(px, py, RGB(66, 78, 108), (int)(70 * vis * edge));
        }
    }
}
static void draw_rays(void) {
    if (!g_isday || g_alt > .4f || g_alt < 0 || E.cover < .12f || E.cover > .93f) return;
    float amt = (1 - smoothf(.05f, .4f, g_alt)) * clampf(E.cover * 2, 0, 1) * (1 - clampf((E.cover - .6f) * 2.5f, 0, 1));
    float sx = g_srcx, sy = Y_H - 8 - (Y_H - 8 - 62) * sinf(PI_F * g_f); u32 sc = mixc(RGB(255, 170, 90), RGB(255, 236, 190), smoothf(0, .3f, g_alt));
    for (int k = 0; k < 9; k++) { float an = PI_F * .1f + k * (PI_F * .8f / 8) + sinf(g_t * .2f + k) * .02f; float L = 260;
        for (float r = 20; r < L; r += 3) { int a = (int)(amt * 40 * (1 - r / L) * (.6f + .4f * sinf(k * 3.1f + g_t * .3f))); if (a < 2) continue; float x = sx + cosf(an) * r, y = sy + sinf(an) * r; bl((int)PX(x), (int)PX(y), sc, a); bl((int)PX(x) + 1, (int)PX(y), sc, a / 2); } }
}
static void draw_clouds(void) {
    u32 lit = LT(gradec(250, 250, 252)), shade = LT(gradec(140, 150, 178));
    float g = clampf(1 - fabsf(g_alt - .03f) / .22f, 0, 1) * (1 - E.cover * .6f); if (g_alt < -.14f) g = 0;
    if (g > 0) { lit = mixc(lit, RGB(255, 160, 110), g * .55f); shade = mixc(shade, RGB(220, 90, 90), g * .55f); }
    if (g_flash > 0) { lit = mixc(lit, 0xFFFFFF, g_flash * .7f); shade = mixc(shade, RGB(200, 210, 255), g_flash * .5f); }
    float spd = (3 + E.wind * .35f) * g_wsign;
    for (int i = 0; i < 14; i++) {
        Cloud *c = &clouds[i]; c->x += spd * c->sp * (1.f / 30); if (c->x > CW + 10) c->x = -c->w - 10; if (c->x < -c->w - 14) c->x = CW + 10;
        float va = clampf((E.cover - c->th) * 3.2f, 0, 1); if (va < .03f) continue; float la = va * (c->layer == 0 ? .6f : c->layer == 1 ? .8f : .95f);
        for (int k = 0; k < c->n; k++) { float cx = c->x + c->dx[k], cy = c->y + c->dy[k] + c->w * .1f, r = c->r[k];
            puff(cx, cy + r * .2f, r * 1.1f, mixc(shade, lit, .2f), la * .9f); }
        for (int k = 0; k < c->n; k++) { float cx = c->x + c->dx[k], cy = c->y + c->dy[k] + c->w * .1f, r = c->r[k];
            puff(cx - r * .12f, cy - r * .3f, r * .82f, lit, la * .85f); }
    }
}
static void draw_ridge(const float *top, float base, u32 ctop, u32 cbot, int toff, float texamt, int snow) {
    int x0 = (int)(MARG * S), x1 = (int)((MARG + CW) * S); float yb = PX(base);
    for (int x = x0; x < x1; x++) {
        float yt = PX(top[x]); int ys = (int)floorf(yt); if (ys < 0) ys = 0;
        float dh = (top[x + 5 < PW ? x + 5 : PW - 1] - top[x > 5 ? x - 5 : 0]) * .5f; float lx = x / S - MARG; float side = (g_srcx - lx) > 0 ? 1.f : -1.f;
        float sf0 = .22f * clampf(-dh * side * .5f, -1, 1) * (.35f + g_srcs * 1.4f);
        float snowy = PX(base - 38 - vn1(lx * .05f) * 16);
        for (int y = ys; y <= (int)yb && y < PH; y++) {
            float t = (y - yt) / (yb - yt); if (t < 0) t = 0; float sf = 1 + sf0 * expf(-t * 7);
            u32 c = mixc(ctop, cbot, t); float n = ntex[((y & 127) << 7) | ((x + toff) & 127)] / 255.f; c = scalec(c, sf * (1 - texamt + 2 * texamt * n), sf * (1 - texamt + 2 * texamt * n), sf * (1 - texamt + 2 * texamt * n));
            if (snow && y < snowy) c = mixc(c, LT(RGB(240, 244, 252)), clampf((snowy - y) / SC(3) + .2f, 0, 1) * .9f);
            if (y == ys) { int a = (int)((1 - (yt - ys)) * 255); bl(x, y, c, a); } else fb[(size_t)y * PW + x] = 0xFF000000u | c;
        }
    }
}
static void draw_far_land(void) {
    float haze0 = clampf(.42f + E.fog * .45f + E.dust * .4f, 0, .95f), haze1 = clampf(.24f + E.fog * .45f + E.dust * .4f, 0, .95f);
    float sn = E.snowc;
    u32 c0t = mixc(mixc(LT(RGB(96, 112, 152)), skyBot, haze0), LT(RGB(230, 236, 250)), sn * .35f), c0b = mixc(LT(RGB(140, 156, 190)), skyBot, clampf(haze0 + .25f, 0, 1));
    draw_ridge(mt0, Y_H, c0t, c0b, 0, .08f, 1);
    u32 c1t = mixc(mixc(LT(RGB(58, 82, 94)), skyBot, haze1), LT(RGB(226, 234, 246)), sn * .6f), c1b = mixc(LT(RGB(84, 110, 114)), skyBot, clampf(haze1 + .22f, 0, 1));
    draw_ridge(mt1, Y_H + 4, c1t, c1b, 40, .1f, 0);
    /* forested hill band */
    float h2 = clampf(.12f + E.fog * .4f, 0, .9f);
    u32 hca = g_season == 0 ? RGB(150, 100, 48) : g_season == 1 ? RGB(66, 112, 62) : RGB(120, 126, 116);
    u32 ht = mixc(mixc(LT(mixc(RGB(48, 80, 54), hca, .45f)), skyBot, h2), LT(RGB(232, 238, 250)), sn * .75f), hb = mixc(mixc(LT(RGB(36, 62, 46)), skyBot, h2), LT(RGB(220, 228, 244)), sn * .75f);
    draw_ridge(hl, Y_RAIL + 1, ht, hb, 77, .12f, 0);
    for (int i = 0; i < ntrees; i++) {
        Tree *t = &trees[i]; u32 c; float x = t->x, y = t->y;
        if (t->kind) { c = mixc(LT(RGB(30, 66, 46)), skyBot, h2 * .6f); c = mixc(c, LT(RGB(230, 238, 250)), sn * .7f);
            float p[6] = { x, y - t->h, x - t->h * .2f, y, x + t->h * .2f, y }; poly(p, 3, c, 1); }
        else { u32 pal[4] = { RGB(204, 96, 36), RGB(224, 150, 44), RGB(176, 64, 36), RGB(206, 176, 62) };
            c = g_season == 0 ? LT(pal[(int)(t->rv * 4) % 4]) : g_season == 1 ? LT(RGB(64, 118, 60)) : LT(RGB(110, 104, 98)); c = mixc(c, skyBot, h2 * .6f); c = mixc(c, LT(RGB(230, 238, 250)), sn * .7f);
            ellipse(x, y - t->h * .5f, t->h * .3f, t->h * .5f, 0, c, 1); }
    }
}
static void draw_village(void) {
    float night = g_night; u32 body_haze = skyBot; float hz = clampf(.1f + E.fog * .45f, 0, .9f);
    for (int i = 0; i < nhouses; i++) {
        House *h = &houses[i]; float yb = Y_RAIL - 6 + (i % 3) - 1; float x = h->x, w = h->w, hh = h->h;
        u32 body = mixc(LT(h->col), body_haze, hz), roof = mixc(LT(h->roof), body_haze, hz);
        rrect(x, yb - hh, w, hh, .8f, body, 1); rrect(x + w * .62f, yb - hh, w * .38f, hh, .8f, scalec(body, .84f, .84f, .88f), .55f);
        float p[6] = { x - 1, yb - hh + .5f, x + w + 1, yb - hh + .5f, x + w / 2, yb - hh - h->rh }; poly(p, 3, roof, 1);
        if (h->chy > .5f) { rrect(x + h->chx, yb - hh - h->rh * .8f, 2.2f, h->rh * .8f, .3f, scalec(roof, .8f, .8f, .8f), 1); }
        for (int k = 0; k < h->nwin; k++) {
            float wx = x + h->wx[k], wy = yb - hh + h->wy[k];
            u32 glass = mixc(LT(RGB(36, 48, 66)), skyBot, .25f); rrect(wx, wy, 2.4f, 3.2f, .5f, glass, 1);
            if (night > .12f && h->on[k]) { float fl_ = (int)(g_t * 1.5f + i) % 11 ? 1.f : .78f; u32 wc = mixc(RGB(255, 190, 90), RGB(255, 226, 150), (float)h->ci[k] / 3); float a = clampf(night * 1.5f, 0, 1) * fl_;
                rrect(wx, wy, 2.4f, 3.2f, .5f, wc, a); glow_add(wx + 1.2f, wy + 1.6f, 9, wc, .22f * a); }
        }
        if (i == cat_house) { /* a cat on the roof ridge */
            float cx = x + w * .5f, cy = yb - hh - h->rh * .72f - 1; u32 cc = mixc(LT(RGB(36, 32, 40)), skyBot, .2f);
            ellipse(cx, cy - 2.4f, 3.4f, 2.8f, 0, cc, 1); circle(cx + 3.2f, cy - 5, 2.2f, cc, 1);
            float e1[6] = { cx + 1.7f, cy - 6.4f, cx + 2.1f, cy - 8.6f, cx + 3.3f, cy - 6.9f }, e2[6] = { cx + 3.3f, cy - 6.9f, cx + 4.5f, cy - 8.6f, cx + 4.9f, cy - 6.4f }; poly(e1, 3, cc, 1); poly(e2, 3, cc, 1);
            capsule(cx - 3, cy - 1.5f, cx - 6 - sinf(g_t * 1.6f) * 1.6f, cy - 4.5f, .9f, .6f, cc, 1);
            if (night > .3f && cat_blink <= 0) { glow_add(cx + 2.5f, cy - 5.2f, 3.2f, RGB(170, 255, 110), .8f * night); glow_add(cx + 4.1f, cy - 5.2f, 3.2f, RGB(170, 255, 110), .8f * night); circle(cx + 2.5f, cy - 5.2f, .6f, RGB(220, 255, 170), night); circle(cx + 4.1f, cy - 5.2f, .6f, RGB(220, 255, 170), night); }
        }
    }
    /* church */
    float cx = CW * .5f, cb = Y_RAIL - 5; u32 cb_ = mixc(LT(RGB(226, 214, 190)), body_haze, hz); rrect(cx - 4.6f, cb - 22, 9.2f, 22, .8f, cb_, 1);
    float sp[6] = { cx - 5.4f, cb - 22, cx + 5.4f, cb - 22, cx, cb - 38 }; poly(sp, 3, mixc(LT(RGB(96, 70, 66)), body_haze, hz), 1);
    rrect(cx - 1.4f, cb - 18, 2.8f, 5, 1.2f, LT(RGB(40, 44, 56)), 1); capsule(cx, cb - 38, cx, cb - 43, .5f, .5f, RGB(210, 180, 80), 1);
    if (night > .15f) glow_add(cx, cb - 15.5f, 8, RGB(255, 200, 120), .3f * night);
    /* smoke */
    for (int i = 0; i < 28; i++) { if (sm[i][4] > 90) continue; float k = sm[i][4] / sm[i][5]; soft(sm[i][0], sm[i][1], 3 + k * 6, g_night > .5f ? RGB(70, 76, 94) : RGB(210, 212, 218), .22f * (1 - k), 1.5f); }
    /* embankment, rails, catenary */
    u32 em = mixc(LT(RGB(122, 116, 108)), body_haze, hz * .6f); rrect_grad(-4, Y_RAIL - 1, CW + 8, 7, 0, scalec(em, 1.1f, 1.1f, 1.1f), 1, scalec(em, .75f, .75f, .8f), 1);
    rrect(-4, Y_RAIL - 1, CW + 8, 1.1f, 0, LT(RGB(196, 196, 204)), 1);
    for (float px = 20; px < CW + 40; px += 52) { rrect(px, Y_RAIL - 23, 1.3f, 23, .3f, LT(RGB(70, 74, 84)), .9f); rrect(px - 5, Y_RAIL - 23, 11, 1, .3f, LT(RGB(70, 74, 84)), .9f); }
    for (float px = 20; px < CW + 40; px += 52) capsule(px, Y_RAIL - 22, px + 52, Y_RAIL - 22, .3f, .3f, LT(RGB(50, 54, 62)), .75f);
}
static void draw_train(void) {
    if (!train.on) return; float ty = Y_RAIL - 1.4f, hc = 11.5f; int d = train.dir; float off = 0; float night = g_night;
    u32 glass = LT(RGB(34, 46, 70)); u32 body = LT(train.body), dark = scalec(body, .62f, .62f, .66f), acc = scalec(train.acc, fmaxf(Lr, .5f), fmaxf(Lg, .5f), fmaxf(Lb, .5f));
    int nseg = 1 + train.ncar;
    for (int s = 0; s < nseg; s++) {
        float len = (train.kind == 0) ? (s == 0 ? 44.f : 32.f) : (s == 0 ? 28.f : 24.f);
        float fx = train.hx - d * off, x0 = d == 1 ? fx - len : fx, w = len;
        if (train.kind == 0) {
            if (s == 0) { /* loco with streamlined nose */
                float nx = d == 1 ? fx : fx; float tip = 12; float b[10];
                float bx0 = d == 1 ? fx - len : fx + len; /* back */
                b[0] = bx0; b[1] = ty - hc; b[2] = fx - d * tip; b[3] = ty - hc; b[4] = fx; b[5] = ty - hc * .45f; b[6] = fx; b[7] = ty - 1.5f; b[8] = bx0; b[9] = ty - 1.5f; (void)nx;
                /* split into two convex polys */
                float p1[8] = { b[0], b[1], b[2], b[3], b[4], b[5], b[0], b[9] }; (void)p1;
                rrect(x0, ty - hc, w - tip * .2f, hc - 1.5f, 2, body, 1); float nose[8] = { fx - d * tip, ty - hc, fx, ty - hc * .45f, fx, ty - 1.5f, fx - d * tip, ty - 1.5f }; poly(nose, 4, body, 1);
                rrect(x0, ty - 5, w, 1.3f, 0, acc, 1); rrect(x0, ty - 3.4f, w, 2, 0, dark, 1);
                float ws[8] = { fx - d * 10, ty - hc + 1.4f, fx - d * 1, ty - hc * .45f - .5f, fx - d * 1, ty - hc * .45f + 3.2f, fx - d * 10, ty - hc + 4.6f }; poly(ws, 4, mixc(glass, skyBot, .3f), 1);
                for (int k = 0; k < 3; k++) { float wx = fx - d * (17 + k * 6.5f) - (d == 1 ? 4.5f : 0); u32 wc = mixc(glass, skyBot, .45f); if (night > .25f) wc = mixc(wc, RGB(255, 222, 140), night); rrect(wx, ty - hc + 2, 4.5f, 3.2f, .8f, wc, 1); }
                capsule(fx - d * 22, ty - hc, fx - d * 24, ty - hc - 6, .5f, .5f, RGB(30, 32, 40), 1); capsule(fx - d * 22 - 4, ty - hc - 7, fx - d * 22 + 4, ty - hc - 7, .6f, .6f, RGB(30, 32, 40), 1);
                if (night > .2f && rnd() < .08f) glow_add(fx - d * 22, ty - hc - 7, 9, RGB(210, 235, 255), 1);
                glow_add(fx, ty - 4, 6, RGB(255, 250, 215), .9f);
                if (night > .05f) { for (int i = 1; i < 90; i += 3) { float hh = 1.5f + i * .09f; float a = (1 - i / 90.f) * .5f * clampf(night * 1.5f, 0, 1); rrect(fx + d * i, ty - 3.5f - hh, 3.2f, hh * 2, 0, RGB(255, 244, 200), a * .5f); } }
            } else {
                rrect(x0, ty - hc, w, hc - 1.5f, 1.6f, body, 1); rrect(x0, ty - 5, w, 1.3f, 0, acc, 1); rrect(x0, ty - 3.4f, w, 2, 0, dark, 1);
                for (int k = 0; k < 5; k++) { float wx = x0 + 3 + k * 5.4f; u32 wc = mixc(glass, skyBot, .45f); if (night > .25f) wc = mixc(wc, RGB(255, 222, 140), night * (.7f + .3f * ((s + k) % 3) / 2.f)); rrect(wx, ty - hc + 2, 4, 3.2f, .8f, wc, 1); }
            }
        } else {
            if (s == 0) { rrect(x0, ty - hc + 1.5f, w, hc - 3, 1.5f, mixc(LT(train.acc), 0, 0), 1); rrect(x0, ty - 5, w, 3.5f, 0, LT(RGB(40, 42, 50)), 1); rrect(fx - d * 8 - (d == 1 ? 5 : 0), ty - hc + 3, 5, 3.6f, .8f, glass, 1); glow_add(fx, ty - 4, 5, RGB(255, 250, 215), .8f);
                if (night > .05f) for (int i = 1; i < 60; i += 3) { float hh = 1.5f + i * .08f; rrect(fx + d * i, ty - 3.5f - hh, 3.2f, hh * 2, 0, RGB(255, 244, 200), (1 - i / 60.f) * .4f * clampf(night * 1.5f, 0, 1)); } }
            else { u32 cc = LT(train.carcol[s % 14]); float h2 = (s % 3 == 0) ? 7 : 9.5f; rrect(x0 + .8f, ty - h2 - 1.5f, w - 1.6f, h2, .8f, cc, 1); for (float rb = x0 + 3; rb < x0 + w - 2; rb += 3.4f) rrect(rb, ty - h2 - 1.5f, .8f, h2, 0, scalec(cc, .82f, .82f, .85f), .6f); }
        }
        for (int k = 0; k < 2; k++) { float wx = x0 + (k ? w - 7 : 4); rrect(wx, ty - 1.5f, 3.5f, 2.6f, 1, RGB(40, 42, 50), 1); }
        off += len + 1.2f;
    }
    if (train.kind == 0) { float rx = train.hx - d * train_len(); for (int k = 1; k < 28; k++) { float a = (1 - k / 28.f) * .35f; rrect(rx - d * k * 1.5f, ty - hc + 3, 1.6f, 1, 0, 0xFFFFFF, a); rrect(rx - d * k * 1.5f, ty - 5, 1.6f, 1, 0, 0xFFFFFF, a); } }
}
static void draw_lake(void) {
    int x0 = (int)(MARG * S), x1 = (int)((MARG + CW) * S), ya = (int)PX(Y_L0), yb = (int)PX(Y_L1); int depth = yb - ya; if (depth < 2) return;
    u32 wc = mixc(LT(RGB(34, 72, 84)), skyBot, .3f); float wamp = (.5f + E.wind * .03f + E.rain * .9f) * S; float dim = 1 - .25f * E.rain;
    for (int y = ya; y < yb; y++) {
        int dy = y - ya; int src = ya - 1 - dy; if (src < 0) src = 0; float rw = (.9f - .52f * dy / depth) * dim; float ph = g_t * 1.3f + dy * .09f / S * 10;
        u32 base = scalec(wc, 1 + .06f * sinf(ph * 1.7f), 1 + .06f * sinf(ph * 1.7f), 1 + .06f * sinf(ph * 1.7f));
        for (int bx = x0; bx < x1; bx += 4) { int o = (int)lroundf(sinf(bx * .11f / S + ph) * wamp * (1 + dy / S * .12f));
            for (int x = bx; x < bx + 4 && x < x1; x++) { int sx = x + o; if (sx < x0) sx = x0; if (sx >= x1) sx = x1 - 1; u32 c = fb[(size_t)src * PW + sx] & 0xFFFFFF; fb[(size_t)y * PW + x] = 0xFF000000u | mixc(base, c, rw); } }
    }
    /* sun/moon glitter */
    float vis = g_isday ? (1 - E.cover * .8f) : g_night * (1 - E.cover * .8f) * .6f;
    if (vis > .1f) { u32 gc_ = g_isday ? RGB(255, 244, 214) : RGB(200, 215, 255); for (int y = ya; y < yb; y++) for (int k = 0; k < 2; k++) { float gx = g_srcx + (rnd() - .5f) * 2 * (10 + (y - ya) / S * 1.2f); if (rnd() < vis * .8f) bl((int)PX(gx), y, gc_, 190); } }
    for (int i = 0; i < 40; i++) { if (rg[i][2] > 1.2f) continue; float age = rg[i][2], r = age * 12, a = 160 * (1 - age / 1.2f) / 255.f; if (rg[i][1] < Y_L0 || rg[i][1] > Y_L1) continue; for (int k = 0; k < 20; k++) { float an = k * .314f; bl((int)PX(rg[i][0] + cosf(an) * r), (int)PX(rg[i][1] + sinf(an) * r * .35f), RGB(210, 225, 240), (int)(a * 255)); } }
    /* boat */
    float bx = boat_x, by = Y_L0 + 9 + sinf(g_t * 1.1f) * .6f; u32 hull = LT(RGB(104, 64, 40)); float hp[8] = { bx - 10, by - 4, bx + 10, by - 4, bx + 7, by + 1, bx - 7, by + 1 }; poly(hp, 4, hull, 1);
    capsule(bx - 10, by - 4, bx + 10, by - 4, .5f, .5f, LT(RGB(150, 100, 64)), 1);
    ellipse(bx - boat_dir * 2, by - 8, 1.7f, 3, 0, LT(RGB(66, 54, 66)), 1); circle(bx - boat_dir * 2, by - 12, 1.3f, LT(RGB(206, 164, 132)), 1); ellipse(bx - boat_dir * 2, by - 13.2f, 2.6f, .6f, 0, LT(RGB(214, 184, 96)), 1);
    float lx = bx + boat_dir * 8.5f; capsule(lx, by - 4, lx, by - 11, .4f, .4f, LT(RGB(60, 44, 34)), 1); capsule(bx - boat_dir * 2 + boat_dir * 2, by - 9, lx + boat_dir * 3, by - 14, .2f, .15f, LT(RGB(90, 70, 50)), 1);
    float lam = clampf(g_night * 1.4f + E.dark * .6f, 0, 1); rrect(lx - 1.3f, by - 13, 2.6f, 2.6f, .6f, RGB(255, 224, 140), .6f + .4f * lam);
    if (lam > .1f) { glow_add(lx, by - 11.7f, 22, RGB(255, 200, 110), .55f * lam); for (int k = 0; k < 20; k++) bl((int)PX(lx + sinf(g_t * 2 + k) * 1.2f), (int)PX(by + 2 + k), RGB(255, 200, 110), (int)(110 * lam * (1 - k / 20.f))); }
    for (int i = 0; i < 3; i++) { float dx = duck_x[i], dy = Y_L0 + 10 + i * 5.5f + sinf(g_t * 2 + dx) * .4f, d = duck_d[i]; u32 gcol = LT(RGB(152, 142, 130));
        ellipse(dx, dy - 2, 4.6f, 2.5f, 0, gcol, 1); ellipse(dx + d * 2.4f, dy - 2.4f, 2.4f, 2.1f, 0, LT(RGB(126, 84, 60)), 1); circle(dx + d * 4.6f, dy - 5, 1.7f, LT(RGB(30, 112, 72)), 1);
        float bk[6] = { dx + d * 5.8f, dy - 5.4f, dx + d * 8.2f, dy - 4.6f, dx + d * 5.8f, dy - 3.8f }; poly(bk, 3, RGB(242, 202, 44), 1); circle(dx + d * 5.1f, dy - 5.4f, .35f, 0x101010, 1);
        for (int k = 1; k < 7; k++) { float a = (1 - k / 7.f) * .35f; bl((int)PX(dx - d * (4 + k * 1.2f)), (int)PX(dy + k * .35f), 0xE6F0FA, (int)(a * 255)); bl((int)PX(dx - d * (4 + k * 1.2f)), (int)PX(dy - k * .35f), 0xE6F0FA, (int)(a * 255)); } }
    if (fish_t >= 0) { float tt = fish_t / .8f, fx = fish_x + tt * 14, fy = fish_y - sinf(PI_F * tt) * 12; capsule(fx - 3, fy + 1 * (1 - 2 * tt), fx + 3, fy, 1.1f, .6f, RGB(210, 224, 236), 1); circle(fx + 3, fy, .5f, 0xFFFFFF, 1); }
}

static void draw_meadow(void) {
    int x0 = (int)(MARG * S), x1 = (int)((MARG + CW) * S); float yb = PX(CH);
    u32 ct = g_season == 1 ? RGB(118, 150, 66) : g_season == 2 ? RGB(150, 150, 120) : RGB(142, 140, 66), cb = g_season == 1 ? RGB(66, 118, 52) : g_season == 2 ? RGB(110, 124, 96) : RGB(84, 112, 48);
    float sand = clampf(E.dust + E.heat * .6f, 0, 1); ct = mixc(ct, RGB(170, 140, 84), sand); cb = mixc(cb, RGB(140, 112, 64), sand);
    ct = mixc(LT(ct), LT(RGB(238, 244, 255)), E.snowc * .85f); cb = mixc(LT(cb), LT(RGB(214, 224, 242)), E.snowc * .85f);
    float wet = 1 - .18f * E.wet; ct = scalec(ct, wet, wet, wet); cb = scalec(cb, wet, wet, wet);
    for (int x = x0; x < x1; x++) {
        float lx = x / S - MARG; float top = Y_L1 + 1.3f * sinf(lx * .045f) + (vn1(lx * .02f + 9) - .5f) * 3; float yt = PX(top); int ys = (int)floorf(yt);
        for (int y = ys; y < (int)yb && y < PH; y++) {
            float t = clampf((y - yt) / (yb - yt) * 3, 0, 1); u32 c = mixc(ct, cb, t); float n = ntex[((y & 127) << 7) | ((x + 31) & 127)] / 255.f; float f = .9f + .2f * n; c = scalec(c, f, f, f);
            if (y == ys) { bl(x, y, mixc(RGB(70, 66, 52), c, .3f), (int)((1 - (yt - ys)) * 255)); } else fb[(size_t)y * PW + x] = 0xFF000000u | c;
        }
    }
    /* shore bushes + glowing eyes in the dark */
    for (int i = 0; i < 5; i++) {
        float bx = bshr[i][0], by = bshr[i][1], br = bshr[i][2]; u32 bc = mixc(LT(g_season == 0 ? RGB(80, 78, 40) : RGB(36, 78, 46)), LT(RGB(238, 244, 255)), E.snowc * .8f);
        ellipse(bx, by, br, br * .55f, 0, bc, 1); ellipse(bx - br * .4f, by - br * .15f, br * .6f, br * .45f, 0, scalec(bc, 1.15f, 1.15f, 1.1f), 1);
        if (g_night > .4f) { float ph = bshr[i][0] * .13f; float vis = sinf(g_t * .27f + ph * 5) > -.35f ? 1.f : 0.f; float bk = fmodf(g_t * .7f + ph, 5.f) < .12f ? 0.f : 1.f;
            if (vis && bk) { u32 ec[5] = { RGB(255, 220, 60), RGB(120, 255, 120), RGB(255, 70, 60), RGB(110, 190, 255), RGB(255, 160, 40) }; u32 c = ec[i];
                float ex = bx + sinf(g_t * .5f + ph) * 1.2f; glow_add(ex - 2, by - 1.5f, 4.4f, c, .9f * g_night); glow_add(ex + 2, by - 1.5f, 4.4f, c, .9f * g_night); circle(ex - 2, by - 1.5f, .75f, c, g_night); circle(ex + 2, by - 1.5f, .75f, c, g_night); } }
    }
    /* reeds */
    for (int i = 0; i < 16; i++) { float x = fmodf(i * 61.f + 11, CW); if (x > 120 && x < 330 && i % 3) continue; float h = 8 + (i % 4) * 2.5f, sw = sinf(g_t * (1 + E.wind * .03f) + i) * 1.4f; u32 rc = LT(RGB(104, 112, 56));
        capsule(x, Y_L1 + 1, x + sw, Y_L1 - h, .55f, .4f, mixc(rc, LT(RGB(238, 244, 255)), E.snowc * .5f), 1); if (i % 2) ellipse(x + sw, Y_L1 - h, 1.1f, 3, 0, LT(RGB(104, 64, 38)), 1); }
}
static void draw_oak(void) {
    float ox = oak_x, w = 1 + E.wind * .04f; u32 bark = LT(RGB(84, 62, 44)); u32 snowc = LT(RGB(240, 246, 255)); float sc = E.snowc;
    capsule(ox, 350, ox + 2, 296, 6, 3.6f, bark, 1); capsule(ox + 2, 296, ox + 44, 282, 2.5f, 1.3f, bark, 1); capsule(ox + 1, 304, ox - 18, 288, 2, 1, bark, 1);
    if (g_season == 2) { capsule(ox + 2, 296, ox + 8, 250, 2.6f, 1.2f, bark, 1); capsule(ox + 8, 262, ox + 30, 240, 1.6f, .8f, bark, 1); capsule(ox + 6, 272, ox - 14, 246, 1.5f, .8f, bark, 1); capsule(ox + 20, 252, ox + 38, 258, 1, .6f, bark, 1); }
    else {
        u32 pal[5] = { RGB(200, 84, 32), RGB(226, 146, 40), RGB(178, 56, 36), RGB(224, 182, 60), RGB(120, 110, 40) }, gp[4] = { RGB(62, 122, 56), RGB(84, 148, 64), RGB(48, 100, 54), RGB(110, 160, 70) };
        for (int i = 0; i < 26; i++) { float a = i * 2.39996f, d = sqrtf(i / 26.f) * 36; float cx = ox + 8 + cosf(a) * d * 1.15f + sinf(g_t * .8f + i) * .5f * w, cy = oak_y - 22 + sinf(a) * d * .8f; float r = 9 + (i % 3) * 2.5f;
            u32 c = g_season == 0 ? pal[i % 5] : gp[i % 4]; float sh = .62f + .5f * clampf(1 - (cy - (oak_y - 55)) / 70, 0, 1); c = LT(scalec(c, sh, sh, sh)); c = mixc(c, snowc, sc * .7f); circle(cx, cy, r, c, 1);
            circle(cx - r * .25f, cy - r * .3f, r * .55f, scalec(c, 1.18f, 1.15f, 1.05f), .55f); }
        for (int i = 0; i < 6; i++) { float cx = ox + 30 + i * 3, cy = 280 - i * 1.2f; circle(cx, cy, 5, LT(g_season == 0 ? pal[(i + 1) % 5] : gp[i % 4]), 1); }
    }
    /* owl on the branch */
    float bx = ox + 33, by = 279.5f; u32 br = LT(RGB(124, 94, 68)), ch = LT(RGB(208, 186, 152)), wg = LT(RGB(96, 72, 52));
    ellipse(bx, by - 6.2f, 4.8f, 6, 0, br, 1); ellipse(bx, by - 5.4f, 3.2f, 4.6f, 0, ch, 1); ellipse(bx - 4.2f, by - 6, 1.8f, 4.6f, .1f, wg, 1); ellipse(bx + 4.2f, by - 6, 1.8f, 4.6f, -.1f, wg, 1);
    ellipse(bx, by - 13, 5.2f, 4.2f, 0, LT(RGB(134, 103, 74)), 1);
    float t1[6] = { bx - 4.8f, by - 15, bx - 5.4f, by - 18.6f, bx - 2.2f, by - 16.4f }, t2[6] = { bx + 4.8f, by - 15, bx + 5.4f, by - 18.6f, bx + 2.2f, by - 16.4f }; poly(t1, 3, br, 1); poly(t2, 3, br, 1);
    ellipse(bx - 2.5f, by - 12.6f, 2.5f, 2.6f, 0, LT(RGB(228, 210, 178)), 1); ellipse(bx + 2.5f, by - 12.6f, 2.5f, 2.6f, 0, LT(RGB(228, 210, 178)), 1);
    float bk[6] = { bx - .9f, by - 11.4f, bx + .9f, by - 11.4f, bx, by - 9.4f }; poly(bk, 3, RGB(204, 164, 74), 1);
    int awake = g_night > .25f && owl_blink <= 0;
    for (int e = -1; e <= 1; e += 2) { float ex = bx + e * 2.5f, ey = by - 12.8f;
        if (awake) { circle(ex, ey, 1.9f, RGB(252, 204, 44), 1); circle(ex + owl_look * .6f, ey, .9f, RGB(12, 8, 4), 1); circle(ex + owl_look * .6f - .3f, ey - .4f, .3f, 0xFFFFFF, 1); glow_add(ex, ey, 7, RGB(255, 214, 60), .6f * g_night); }
        else capsule(ex - 1.5f, ey + .4f, ex + 1.5f, ey + .4f, .35f, .35f, LT(RGB(52, 36, 24)), 1); }
    capsule(bx - 2, by, bx - 2, by - 1.5f, .5f, .5f, RGB(190, 150, 60), 1); capsule(bx + 2, by, bx + 2, by - 1.5f, .5f, .5f, RGB(190, 150, 60), 1);
}
static void draw_critters(void) {
    float ground = Y_L1 + 5.5f;
    if (sheep_gone <= 0) { float sx = sheep_x; u32 wl = LT(RGB(240, 235, 222)), dk = LT(RGB(60, 52, 50)); if (ufo.on && ufo.state == 1 && ufo.lift > 0) ground -= ufo.lift * (ground - ufo.y - 12);
        for (int k = 0; k < 4; k++) capsule(sx - 4.5f + k * 3, ground - 4, sx - 4.5f + k * 3, ground, .7f, .6f, dk, 1);
        float cc[7][3] = { { -3.6f, -7.6f, 3.4f }, { 0, -8.4f, 3.8f }, { 3.6f, -7.6f, 3.4f }, { -1.5f, -5.8f, 3.2f }, { 2, -5.6f, 3 }, { -4.8f, -5.8f, 2.6f }, { 4.8f, -5.8f, 2.4f } };
        for (int k = 0; k < 7; k++) circle(sx + cc[k][0], ground + cc[k][1] + 1.5f, cc[k][2], k % 2 ? scalec(wl, .94f, .94f, .96f) : wl, 1);
        ellipse(sx + sheep_dir * 6.2f, ground - 6 + (int)(g_t * .6f) % 2 * 2.2f, 2, 2.7f, .4f * sheep_dir, dk, 1); }
    if (udk_on) { float x = udk_x, y = Y_L1 + 8.5f, d = udk_dir; u32 yc = RGB(255, 218, 62); capsule(x - 1.5f, y - 1, x - 1.5f, y + 1, .5f, .5f, RGB(250, 140, 30), 1); capsule(x + 1.5f, y - 1, x + 1.5f, y + 1, .5f, .5f, RGB(250, 140, 30), 1);
        ellipse(x, y - 3, 4, 2.8f, 0, yc, 1); circle(x + d * 3.2f, y - 6, 2.2f, yc, 1); float bk[6] = { x + d * 5, y - 6.4f, x + d * 7.4f, y - 5.8f, x + d * 5, y - 5 }; poly(bk, 3, RGB(250, 140, 30), 1);
        capsule(x, y - 6.5f, x, y - 2.6f, .3f, .3f, RGB(60, 56, 60), 1); for (int k = 0; k < 6; k++) { float a0 = PI_F + k * PI_F / 6, a1 = a0 + PI_F / 6; float p[6] = { x, y - 13.4f, x + cosf(a0) * 8, y - 8.5f + sinf(a0) * 5, x + cosf(a1) * 8, y - 8.5f + sinf(a1) * 5 }; poly(p, 3, k % 2 ? RGB(250, 232, 220) : RGB(212, 44, 56), 1); } }
    if (E.snowc > .3f) { float x = 300, y = Y_L1 + 8; float a = clampf(E.snowc * 1.4f, 0, 1); u32 sn = LT(RGB(244, 248, 255)); circle(x, y - 4, 5, sn, a); circle(x, y - 11, 3.7f, sn, a); circle(x, y - 16.4f, 2.8f, sn, a);
        circle(x - 1, y - 17, .4f, 0x1c1c22, a); circle(x + 1, y - 17, .4f, 0x1c1c22, a); float nz[6] = { x, y - 16.2f, x + 3.4f, y - 15.6f, x, y - 15.2f }; poly(nz, 3, RGB(250, 130, 30), a);
        capsule(x - 3.4f, y - 12, x + 3.4f, y - 12, .9f, .9f, RGB(206, 40, 52), a); ellipse(x, y - 19.4f, 3.4f, .8f, 0, 0x22222a, a); rrect(x - 2, y - 24, 4, 5, .4f, 0x22222a, a); }
    if (tumble_on) { float x = tumble_x, y = Y_L1 + 8; ring(x, y - 3.5f, 3.5f, 1, LT(RGB(140, 102, 58)), .9f); for (int k = 0; k < 7; k++) { float an = tumble_a * 3 + k * .9f; capsule(x, y - 3.5f, x + cosf(an) * 3.4f, y - 3.5f + sinf(an) * 3.4f, .4f, .3f, LT(RGB(158, 118, 68)), .9f); } }
}
static void draw_sky_actors(void) {
    if (flock.on) for (int i = 0; i < flock.n; i++) { float bx = flock.x + flock.off[i][0], by = flock.y + flock.off[i][1] + sinf(g_t * 2 + flock.off[i][2]) * 1.5f, w = sinf(g_t * 9 + flock.off[i][2]) * 3.2f; u32 c = mixc(RGB(30, 34, 44), skyBot, .25f);
        capsule(bx, by, bx - 4, by - 1 - w, .7f, .3f, c, .9f); capsule(bx, by, bx + 4, by - 1 - w, .7f, .3f, c, .9f); circle(bx, by, 1, c, 1); }
    if (g_night > .35f) for (int i = 0; i < 3; i++) { float bx = bats[i][0], by = bats[i][1], w = sinf(g_t * 13 + bats[i][4]) * 3; u32 c = RGB(60, 50, 86);
        capsule(bx, by, bx - 5, by - w, .8f, .3f, c, .95f); capsule(bx, by, bx + 5, by - w, .8f, .3f, c, .95f); ellipse(bx, by + .5f, 1.3f, 2, 0, c, 1); }
    if (plane_on) { float x = plane_x, y = plane_y;
        if (g_night < .3f) { for (int i = 0; i < 40; i++) { float a = (1 - i / 40.f) * .5f; bl((int)PX(x - plane_d * i * 2.2f), (int)PX(y), 0xFFFFFF, (int)(a * 255)); } capsule(x - 3 * plane_d, y, x + 3 * plane_d, y, .8f, .5f, RGB(240, 242, 248), 1); }
        else { glow_add(x, y + 1, 7, RGB(255, 60, 60), .9f); circle(x + 3 * plane_d, y, .8f, RGB(80, 255, 120), 1); if ((int)(g_t * 2) % 2 == 0) glow_add(x - plane_d, y, 7, 0xFFFFFF, 1); } }
}
static void draw_mist(void) {
    float dawn = (fabsf(g_hour - g_rise - .6f) < 2.2f && E.cover < .9f) ? clampf(1 - fabsf(g_hour - g_rise - .6f) / 2.2f, 0, 1) * (1 - E.cover * .5f) * .5f : 0; float amt = fmaxf(E.fog, dawn); if (amt < .06f) return;
    u32 fc = scalec(RGB(215, 220, 228), fmaxf(Lr, .3f), fmaxf(Lg, .3f), fmaxf(Lb, .38f)); int x0 = (int)(MARG * S), x1 = (int)((MARG + CW) * S), ya = (int)PX(Y_H - 50), yb = (int)PX(Y_L1 + 10); int n = yb - ya;
    for (int y = ya; y < yb; y++) { float k = (float)(y - ya) / n; float prof = powf(sinf(k * PI_F), 1.2f);
        for (int x = x0; x < x1; x++) { int a = (int)(amt * 190 * prof * (.78f + .22f * sinf(x * .05f / S + g_t * .3f + k * 9))); if (a > 2) bl(x, y, fc, a); } }
}
static void draw_precip(void) {
    float wx = E.wind * 1.1f * g_wsign; u32 rc = scalec(RGB(176, 196, 232), fmaxf(Lr, .55f), fmaxf(Lg, .6f), fmaxf(Lb, .75f));
    int nr = (int)(fminf(1, E.rain + E.hail * .4f) * 260 * .55f);
    for (int i = 0; i < nr; i++) {
        float *d = dr[i]; if (E.hail > .5f && i % 2 == 0) { circle(d[0], d[1], 1.5f, RGB(235, 242, 255), 1); continue; }
        float len = 6 + 10 * d[3]; float sl = wx * (.5f + d[3]) / d[2]; capsule(d[0], d[1], d[0] - sl * len, d[1] - len, .55f, .35f, rc, .35f + .5f * d[3]);
    }
    int ns = (int)(fminf(1, E.snow) * 170); u32 fc = scalec(RGB(246, 249, 255), fmaxf(Lr, .62f), fmaxf(Lg, .66f), fmaxf(Lb, .82f));
    for (int i = 0; i < ns; i++) { float *f = fl[i]; float r = .8f + f[4] * 1.5f; if (f[4] > .6f) soft(f[0], f[1], r * 2, fc, .5f, 1.3f); circle(f[0], f[1], r, fc, .6f + .4f * f[4]); }
    if (E.dust > .05f) { u32 dc = scalec(RGB(215, 165, 95), fmaxf(Lr, .5f), fmaxf(Lg, .5f), fmaxf(Lb, .6f)); float sg = g_wsign >= 0 ? 1.f : -1.f;
        for (int i = 0; i < 70; i++) capsule(dp[i][0], dp[i][1], dp[i][0] - sg * 12, dp[i][1], .5f, .2f, dc, E.dust * .45f); }
    for (int i = 0; i < 16; i++) { if (lv[i][5] < 0) continue; u32 lc[4] = { RGB(200, 84, 32), RGB(226, 146, 40), RGB(178, 56, 36), RGB(224, 182, 60) }; ellipse(lv[i][0], lv[i][1], 2.6f, 1.3f, lv[i][4], LT(lc[(int)lv[i][5] & 3]), 1); }
    if (g_night > .4f && g_temp > 10 && E.rain < .2f && E.snow < .1f) for (int i = 0; i < 16; i++) { float x = ff[i][0] + sinf(g_t * ff[i][3] + ff[i][2]) * 8, y = ff[i][1] + cosf(g_t * ff[i][3] * .7f + ff[i][2]) * 4; float a = powf(fmaxf(0, sinf(g_t * 1.4f + ff[i][2])), 3) * g_night; if (a > .12f) { glow_add(x, y, 6, RGB(210, 255, 90), a); circle(x, y, .8f, RGB(240, 255, 170), a); } }
}
static void draw_ufo(void) {
    if (!ufo.on) return; float ux = ufo.x, uy = ufo.y, gy = Y_L1 + 6;
    if (ufo.state == 1) { float prog = clampf(ufo.t / .8f, 0, 1); for (float y = uy + 4; y < gy; y += 1.f / S * 1.5f) { float f = (y - uy) / (gy - uy), hw = (3 + f * 9 * prog); for (float x = ux - hw; x <= ux + hw; x += 1.f / S * 1.5f) { int a = (int)(((fabsf(x - ux) < hw - 1 ? 40 : 80) * prog) + (rnd() < .04f ? 70 : 0)); bl((int)PX(x), (int)PX(y), RGB(170, 255, 190), a); } } }
    ellipse(ux, uy - 3, 6, 4, 0, RGB(150, 232, 240), .9f); ellipse(ux, uy + 1, 14, 3.8f, 0, RGB(176, 182, 198), 1); ellipse(ux, uy + 3, 9, 2.3f, 0, RGB(104, 110, 128), 1);
    for (int i = 0; i < 5; i++) { u32 cs[3] = { RGB(255, 70, 70), RGB(255, 230, 80), RGB(90, 255, 120) }; circle(ux + (i - 2) * 4.2f, uy + 2.2f, 1, cs[(int)(g_t * 6 + i) % 3], 1); }
    glow_add(ux, uy + 3, 16, RGB(120, 255, 170), .45f);
}
static void draw_flash(void) {
    if (g_flash <= 0) return; int a = (int)(g_flash * 46); int x0 = (int)(MARG * S), x1 = (int)((MARG + CW) * S), y0 = (int)(MARG * S), y1 = (int)PX(Y_H);
    for (int y = y0; y < y1; y++) for (int x = x0; x < x1; x++) addp(x, y, RGB(190, 205, 255), a);
    if (g_flash > .2f && bolt_n > 1) for (int i = 0; i + 1 < bolt_n; i++) { capsule(bolt_x[i] - 1, bolt_y[i], bolt_x[i + 1] - 1, bolt_y[i + 1], 2.2f, 2.2f, RGB(150, 170, 255), .35f); capsule(bolt_x[i], bolt_y[i], bolt_x[i + 1], bolt_y[i + 1], .8f, .8f, 0xFFFFFF, 1); }
}
static void draw_world(void) {
    compute_env(); fill_sky(); draw_stars(); draw_aurora(); draw_celestial(); draw_rays(); draw_clouds();
    draw_far_land(); draw_sky_actors(); draw_village(); draw_train(); draw_lake(); draw_meadow(); draw_oak(); draw_critters(); draw_mist(); draw_precip(); draw_ufo(); draw_flash();
}

/* ---------- simulation step ---------- */
static void ring_add(float x, float y) { for (int i = 0; i < 40; i++) if (rg[i][2] > 1.2f) { rg[i][0] = x; rg[i][1] = y; rg[i][2] = 0; return; } }
static void scene_update(float dt) {
    g_t += dt; float *e = &E.cover; const float *t = &T.cover; for (int i = 0; i < 9; i++) e[i] = easef(e[i], t[i], dt, .7f);
    E.snowc = easef(E.snowc, T.snow > .2f ? 1.f : 0.f, dt, T.snow > .2f ? .05f : (g_temp > 3 ? .04f : .012f)); E.wet = easef(E.wet, E.rain > .2f ? 1.f : 0.f, dt, E.rain > .2f ? .15f : .05f); E.aur = easef(E.aur, T.aur, dt, .5f);
    if (g_msg_t > 0) g_msg_t -= dt;
    if (E.storm > .3f) { next_strike -= dt * E.storm; if (next_strike <= 0) strike(); }
    g_flash_t += dt; g_flash = 0; if (g_flash_t < .55f) g_flash = (g_flash_t < .1f || g_flash_t > .16f) ? fmaxf(0, 1 - g_flash_t * 2.2f) : .25f;
    if (g_flash_t > .7f && thunder_pending) { thunder_pending = 0; const char *m[] = { "KRA-KA-BOOOOM!", "*RUMBLE*", "CRAAACK!" }; /*say(m[(int)(rnd() * 3) % 3], 2);*/ }
    if (!train.on) { next_train -= dt; if (next_train <= 0) { train_spawn(-1, 0); next_train = rndr(26, 55); } }
    else { train.hx += train.dir * train.speed * dt; /*if (!train.horn && train.hx > 0 && train.hx < CW) { train.horn = 1; say(train.kind == 0 ? "TRAIN!  TUUUUUUU!" : "freight train... chug chug", 3); }*/
        float rear = train.hx - train.dir * train_len(); if ((train.dir == 1 && rear > CW + 4) || (train.dir == -1 && rear < -4)) train.on = 0; }
    if (!ufo.on) { if (g_night > .7f && E.rain < .1f) { next_ufo -= dt; if (next_ufo <= 0) { memset(&ufo, 0, sizeof ufo); ufo.on = 1; ufo.side = rnd() < .5f ? -1.f : 1.f; ufo.x = ufo.side == 1 ? -20.f : CW + 20.f; ufo.y = 80; ufo.tx = sheep_x; next_ufo = rndr(90, 200); say("something is in the sky...", 4); } } }
    else { ufo.t += dt; if (ufo.state == 0) { float d = ufo.tx - ufo.x; ufo.x += clampf(d * 1.4f, -90, 90) * dt; if (fabsf(d) < 1) { ufo.state = 1; ufo.t = 0; } }
        else if (ufo.state == 1) { if (ufo.t > 1 && ufo.t < 5.5f) ufo.lift = clampf((ufo.t - 1) / 4.5f, 0, 1); if (ufo.t > 1.3f && !ufo.said) { ufo.said = 1; /*say("BAAA?!", 3.5f);*/ } if (ufo.t > 5.8f) { ufo.state = 2; ufo.t = 0; ufo.vx = ufo.side * 5; ufo.vy = -3; sheep_gone = 45; } }
        else { ufo.vx *= 1 + dt * 3; ufo.vy *= 1 + dt * 3; ufo.x += ufo.vx * dt * 12; ufo.y += ufo.vy * dt * 12; if (ufo.x < -40 || ufo.x > CW + 40 || ufo.y < -30) ufo.on = 0; } }
    if (sheep_gone > 0) sheep_gone -= dt;
    sheep_x += sheep_dir * 1.6f * dt * ((int)(g_t * .35f) % 3 != 0); if (sheep_x < 110 || sheep_x > 280) sheep_dir = -sheep_dir;
    if (flock.on) { flock.x += flock.v * dt; if (flock.x < -50 || flock.x > CW + 50) flock.on = 0; }
    else if (g_night < .2f && E.rain < .2f && E.storm < .2f && E.snow < .5f) { next_flock -= dt; if (next_flock <= 0) { flock.on = 1; flock.dir = rnd() < .5f ? -1.f : 1.f; flock.x = flock.dir > 0 ? -20.f : CW + 20.f; flock.y = rndr(70, 150); flock.v = rndr(24, 40) * flock.dir; flock.n = 6;
        for (int i = 0; i < 6; i++) { int s = (i + 1) / 2 * (i % 2 ? 1 : -1); flock.off[i][0] = -flock.dir * abs(s) * 9; flock.off[i][1] = s * 5.f; flock.off[i][2] = rnd() * 6; } next_flock = rndr(20, 48); } }
    for (int i = 0; i < 3; i++) { bats[i][2] += rndr(-160, 160) * dt; bats[i][3] += rndr(-160, 160) * dt; bats[i][2] = clampf(bats[i][2], -50, 50); bats[i][3] = clampf(bats[i][3], -28, 28); bats[i][0] += bats[i][2] * dt; bats[i][1] += bats[i][3] * dt;
        if (bats[i][1] < 30 || bats[i][1] > 220) bats[i][3] = -bats[i][3]; if (bats[i][0] < -8) bats[i][0] = CW + 6; if (bats[i][0] > CW + 8) bats[i][0] = -6; }
    boat_x += boat_dir * 3 * dt; if (boat_x < 110 || boat_x > 300) boat_dir = -boat_dir;
    for (int i = 0; i < 3; i++) { duck_x[i] += duck_d[i] * 4.4f * dt; if (duck_x[i] < 50 || duck_x[i] > 330) duck_d[i] = -duck_d[i]; }
    if (fish_t < 0) { next_fish -= dt; if (next_fish <= 0) { next_fish = rndr(7, 16); if (g_night < .5f && E.snowc < .5f) { fish_t = 0; fish_x = rndr(CW * .25f, CW * .7f); fish_y = rndr(Y_L0 + 8, Y_L1 - 3); } } }
    else { fish_t += dt; if (fish_t > .8f) { ring_add(fish_x + 14, fish_y); fish_t = -1; } }
    if (E.rain > .15f && !udk_on) { udk_on = 1; udk_x = rnd() < .5f ? -14.f : CW + 14.f; udk_dir = udk_x < 0 ? 1.f : -1.f; }
    if (udk_on) { udk_x += udk_dir * 10 * dt; if (udk_x > CW + 16) udk_dir = -1; if (udk_x < -16) udk_dir = 1; if (E.rain < .04f && (udk_x < -10 || udk_x > CW + 10)) udk_on = 0; }
    if (E.dust > .3f && !tumble_on) { tumble_on = 1; tumble_x = -6; } if (tumble_on) { tumble_x += (40 + E.wind * 1.5f) * dt * g_wsign; tumble_a += dt * 8; if (tumble_x > CW + 8 || tumble_x < -10) { tumble_on = E.dust > .3f; tumble_x = g_wsign > 0 ? -6.f : CW + 6.f; } }
    owl_next -= dt; if (owl_next <= 0) { owl_look = (float)((int)(rnd() * 3) - 1); owl_next = rndr(1.5f, 4.5f); owl_blink = rnd() < .4f ? .18f : 0; } if (owl_blink > 0) owl_blink -= dt;
    cat_next -= dt; if (cat_next <= 0) { cat_next = rndr(3, 9); cat_blink = .2f; } if (cat_blink > 0) cat_blink -= dt;
    if (!shoot_on) { next_shoot -= dt; if (next_shoot <= 0) { next_shoot = rndr(5, 14); if (g_night > .7f && E.cover < .5f) { shoot_on = 1; shoot[0] = rndr(0, CW * .8f); shoot[1] = rndr(10, 100); shoot[2] = rndr(90, 160); shoot[3] = rndr(30, 70); shoot[4] = 0; } } }
    else { shoot[0] += shoot[2] * dt; shoot[1] += shoot[3] * dt; shoot[4] += dt; if (shoot[4] > .8f) shoot_on = 0; }
    if (!plane_on) { next_plane -= dt; if (next_plane <= 0 && E.cover < .8f && E.storm < .2f) { plane_on = 1; plane_d = rnd() < .5f ? -1.f : 1.f; plane_x = plane_d > 0 ? -4.f : CW + 4.f; plane_y = rndr(26, 80); next_plane = rndr(30, 70); } }
    else { plane_x += plane_d * 22 * dt; if (plane_x < -8 || plane_x > CW + 8) plane_on = 0; }
    if (g_season == 0 && E.wind > 3) { for (int i = 0; i < 16; i++) if (lv[i][5] < 0 && rnd() < dt * (.6f + E.wind * .05f)) { lv[i][0] = oak_x + rndr(-6, 36); lv[i][1] = oak_y - 40 + rndr(0, 30); lv[i][2] = 0; lv[i][3] = rndr(8, 16); lv[i][4] = rnd() * 6; lv[i][5] = (float)((int)(rnd() * 4)); break; } }
    for (int i = 0; i < 16; i++) { if (lv[i][5] < 0) continue; lv[i][4] += dt * 3; lv[i][0] += (E.wind * .9f * g_wsign + sinf(lv[i][4]) * 8) * dt * .5f; lv[i][1] += lv[i][3] * dt; if (lv[i][1] > Y_L1 + 2 || lv[i][0] < -10 || lv[i][0] > CW + 10) lv[i][5] = -1; }
    for (int i = 0; i < nhouses; i++) if (houses[i].chy > .5f && (g_temp < 22 || g_night > .3f) && rnd() < dt * .35f) for (int k = 0; k < 28; k++) if (sm[k][4] > 90) { float yb = Y_RAIL - 6 + (i % 3) - 1; sm[k][0] = houses[i].x + houses[i].chx + 1; sm[k][1] = yb - houses[i].h - houses[i].rh * .8f; sm[k][2] = 0; sm[k][3] = rndr(6, 11); sm[k][4] = 0; sm[k][5] = rndr(4, 6); break; }
    for (int k = 0; k < 28; k++) { if (sm[k][4] > 90) continue; sm[k][4] += dt; sm[k][0] += (E.wind * .4f * g_wsign + rndr(-1.5f, 1.5f)) * dt; sm[k][1] -= sm[k][3] * dt; if (sm[k][4] >= sm[k][5]) sm[k][4] = 99; }
    for (int i = 0; i < 40; i++) if (rg[i][2] <= 1.2f) rg[i][2] += dt;
    float wx = E.wind * 1.1f * g_wsign; int nr = (int)(fminf(1, E.rain + E.hail * .4f) * 260 * .55f);
    for (int i = 0; i < nr; i++) { dr[i][1] += dr[i][2] * dt * (E.hail > .5f ? 1.3f : 1); dr[i][0] += wx * dt * (.5f + dr[i][3]); if (dr[i][1] >= dr[i][4]) { if (dr[i][4] < Y_L1 && rnd() < .5f) ring_add(dr[i][0], dr[i][4]); dr[i][1] = rndr(-30, -1); dr[i][0] = rndr(-CW * .3f, CW * 1.1f); } }
    int ns = (int)(fminf(1, E.snow) * 170); for (int i = 0; i < ns; i++) { fl[i][1] += fl[i][2] * dt * (.5f + fl[i][4]) * (1 + E.snow * .5f); fl[i][0] += (wx * .7f + sinf(g_t * 1.3f + fl[i][3]) * 10) * dt; if (fl[i][1] >= fl[i][5]) { fl[i][1] = rndr(-10, 0); fl[i][0] = rndr(-60, CW + 60); } if (fl[i][0] > CW + 5) fl[i][0] = -3; if (fl[i][0] < -5) fl[i][0] = CW + 3; }
    for (int i = 0; i < 70; i++) { dp[i][0] += (60 + E.wind * 2.5f) * dp[i][2] * dt * (g_wsign >= 0 ? 1 : -1); if (dp[i][0] > CW + 3) dp[i][0] = -3; if (dp[i][0] < -3) dp[i][0] = CW + 3; }
}

/* ======================================================================
 *  UI: header, glass panel, gauges, forecast, menu, city search
 * ====================================================================== */
static Weather W; static int has_w = 0, ui_mode = 0 /*0 normal 1 search 2 menu*/, ov_cond = -1, lapse = 0, reel = 0, reel_i = 0, quit_flag = 0;
static float t_off = 0, reel_t = 0, reel_target = -1, last_fetch_t = -999; static char qbuf[64]; static int qlen = 0, qsel = 0, q_dirty = 0, q_searched = 0; static float q_t = 0, caret_t = 0;
static char status[80] = ""; static float status_t = 0;
static const struct { int c; float h; } REEL[] = { { C_CLEAR, 7 }, { C_PARTLY, 12 }, { C_STORM, 19.4f }, { C_RAIN, 22 }, { C_SNOW, 2 }, { C_FOG, 6.2f }, { C_CLEAR, 21 }, { C_DUST, 15.5f }, { C_HEAT, 13 }, { C_HAIL, 18 }, { C_BLIZZARD, 23 }, { C_CLEAR, 5.4f } };
static const char *MENU_ITEMS[] = { "Change city", "Units", "Refresh", "Weather", "Time-lapse", "Showreel", "Summon train", "Quit" };
#define NMENU 8
static void toast(const char *s) { snprintf(status, sizeof status, "%s", s); status_t = 3; }
static int tfv(float c) { return (int)lroundf(cfg.units ? c * 9 / 5 + 32 : c); }
static int in_rect(float x, float y, float rx, float ry, float rw, float rh) { return x >= rx && x < rx + rw && y >= ry && y < ry + rh; }

static u32 accent_of(int c) { static const u32 a[NCOND] = { 0xFFD65A, 0xFFDC82, 0xBEC8DC, 0xC8D2DC, 0x82BEFF, 0x6EAAFF, 0xFFEB5A, 0xD2EBFF, 0xC8E6FF, 0xAAD2F5, 0xBEE1FF, 0xEBAA5A, 0xFF7846 }; return a[c]; }
static void sun_i(float cx, float cy, float r, float t) {
    for (int k = 0; k < 8; k++) { float a = k * PI_F / 4 + t * .3f; capsule(cx + cosf(a) * r * 1.4f, cy + sinf(a) * r * 1.4f, cx + cosf(a) * r * (1.85f + .12f * sinf(t * 3 + k)), cy + sinf(a) * r * (1.85f + .12f * sinf(t * 3 + k)), r * .13f, r * .1f, RGB(255, 196, 60), .95f); }
    circle(cx, cy, r, RGB(255, 214, 70), 1); circle(cx - r * .25f, cy - r * .25f, r * .6f, RGB(255, 236, 140), .55f);
}
static void cloud_i(float cx, float cy, float s, u32 col) {
    circle(cx - 6 * s, cy + 1 * s, 4.6f * s, col, 1); circle(cx + 6.5f * s, cy + 1.5f * s, 4.2f * s, col, 1); circle(cx - .5f * s, cy - 2 * s, 6.4f * s, col, 1); rrect(cx - 10.6f * s, cy + 1 * s, 21.2f * s, 4.8f * s, 2.4f * s, col, 1);
    circle(cx - 1.5f * s, cy - 3.6f * s, 4.2f * s, mixc(col, 0xFFFFFF, .35f), .6f);
}
static void icon(int c, float cx, float cy, float s, float t) {
    u32 cl = RGB(236, 242, 252), cd = RGB(142, 152, 176); int f = (int)(t * 3);
    if (c == C_CLEAR || c == C_HEAT) { sun_i(cx, cy, 5.2f * s, t); return; }
    if (c == C_PARTLY) { sun_i(cx - 4 * s, cy - 3 * s, 4.3f * s, t); cloud_i(cx + 1.5f * s, cy + 2.5f * s, s * .95f, cl); return; }
    if (c == C_CLOUDY) { cloud_i(cx, cy, s, cl); return; }
    if (c == C_FOG) { for (int i = 0; i < 4; i++) capsule(cx - 8 * s + (i % 2) * 2 * s, cy - 6 * s + i * 4.2f * s, cx + 8 * s - (i % 2) * 2 * s, cy - 6 * s + i * 4.2f * s, .9f * s, .9f * s, RGB(196, 206, 220), .9f); return; }
    if (c == C_DUST) { for (int i = 0; i < 4; i++) capsule(cx - 8 * s + (i * 3) % 4 * s, cy - 6 * s + i * 4.2f * s, cx + 8 * s + (i % 2) * 2 * s, cy - 6 * s + i * 4.2f * s, .9f * s, .9f * s, RGB(224, 170, 96), .95f); return; }
    int dark = c == C_STORM || c == C_HAIL; cloud_i(cx, cy - 4 * s, s * .95f, dark ? cd : cl);
    for (int i = 0; i < 3; i++) { float x = cx - 6 * s + i * 6 * s, y = cy + 4 * s + ((f + i) % 3) * 1.2f * s;
        if (c == C_RAIN || c == C_DRIZZLE || c == C_SLEET || c == C_STORM) capsule(x, y, x - 1.2f * s, y + 3.6f * s, .7f * s, .55f * s, RGB(110, 176, 255), 1);
        if (c == C_SNOW || c == C_BLIZZARD || (c == C_SLEET && i == 1)) circle(x, y + 1.5f * s, 1.2f * s, 0xFFFFFF, 1);
        if (c == C_HAIL) circle(x, y + 1.5f * s, 1.3f * s, RGB(236, 244, 255), 1); }
    if (c == C_STORM) { float p[8] = { cx + 1.5f * s, cy + 1 * s, cx - 2.5f * s, cy + 6.5f * s, cx + .5f * s, cy + 6.5f * s, cx - 1.5f * s, cy + 10.5f * s }; float a[6] = { p[0], p[1], p[2], p[3], p[4], p[5] }, b[6] = { p[4], p[5], p[6], p[7], p[2], p[3] }; (void)b; poly(a, 3, RGB(255, 232, 80), 1); float bb[6] = { p[2] + .5f * s, p[3] - .5f * s, p[6], p[7], p[4] + .5f * s, p[5] - .5f * s }; poly(bb, 3, RGB(255, 232, 80), 1); }
}
static void gauge_ring(float cx, float cy, float R, float frac, u32 col, const char *val, const char *label, float tt) {
    float a0 = PI_F * .75f, sw = PI_F * 1.5f; arc(cx, cy, R, 3.4f, a0, a0 + sw, 0xFFFFFF, .16f);
    if (frac > .005f) { arc(cx, cy, R, 3.4f, a0, a0 + sw * clampf(frac, 0, 1), col, 1); float ea = a0 + sw * clampf(frac, 0, 1); glow_add(cx + cosf(ea) * R, cy + sinf(ea) * R, 7, col, .5f); circle(cx + cosf(ea) * R, cy + sinf(ea) * R, 2.2f, 0xFFFFFF, .95f); }
    text(1, 13, cx, cy + 4.5f, val, 0xFFFFFF, .96f, 0, 1); text(1, 8.4f, cx, cy + R + 14, label, 0xFFFFFF, .62f, 1.4f, 1); (void)tt;
}
static void gauge_wind(float cx, float cy, float R, float dir, const char *val, float tt) {
    ring(cx, cy, R, 1.2f, 0xFFFFFF, .22f);
    for (int k = 0; k < 16; k++) { float a = k * PI_F / 8; float r0 = R - (k % 4 == 0 ? 5.5f : 3), r1 = R + .5f; capsule(cx + cosf(a) * r0, cy + sinf(a) * r0, cx + cosf(a) * r1, cy + sinf(a) * r1, .5f, .5f, 0xFFFFFF, k % 4 == 0 ? .55f : .28f); }
    text(1, 7.5f, cx, cy - R + 11, "N", 0xFFFFFF, .75f, 0, 1);
    float a = (dir + 90) * PI_F / 180; /* arrow points where the wind blows to */
    float wob = sinf(tt * 2) * .04f; a += wob; float tx = cx + cosf(a) * (R - 4), ty = cy + sinf(a) * (R - 4), bx = cx - cosf(a) * (R - 8), by = cy - sinf(a) * (R - 8);
    capsule(bx, by, tx, ty, .9f, .9f, RGB(120, 210, 255), .95f); float hp[6] = { tx + cosf(a) * 3.5f, ty + sinf(a) * 3.5f, tx - cosf(a) * 4 + cosf(a + 1.57f) * 3.4f, ty - sinf(a) * 4 + sinf(a + 1.57f) * 3.4f, tx - cosf(a) * 4 - cosf(a + 1.57f) * 3.4f, ty - sinf(a) * 4 - sinf(a + 1.57f) * 3.4f };
    hp[1] = ty + sinf(a) * 3.5f; hp[3] = ty + sinf(a) * -4 + sinf(a + 1.57f) * 3.4f; hp[5] = ty + sinf(a) * -4 - sinf(a + 1.57f) * 3.4f; poly(hp, 3, RGB(120, 210, 255), 1);
    text(1, 11.5f, cx, cy + 4, val, 0xFFFFFF, .95f, 0, 1); text(1, 8.4f, cx, cy + R + 14, "WIND", 0xFFFFFF, .62f, 1.4f, 1);
}
static u32 *pc_buf; static int pc_w, pc_h, pc_x, pc_y, pc_age;
static void blur_rrect(float x, float y, float w, float h, float r, int rad, int passes, int cached) {
    int X = (int)PX(x), Y = (int)PX(y), Wp = (int)SC(w), Hp = (int)SC(h); if (X < 0) X = 0; if (Y < 0) Y = 0; if (X + Wp > PW) Wp = PW - X; if (Y + Hp > PH) Hp = PH - Y; if (Wp < 8 || Hp < 8) return;
    if (cached && pc_buf && pc_w == Wp && pc_h == Hp && pc_x == X && pc_y == Y && (pc_age++ % 3)) { for (int j = 0; j < Hp; j++) memcpy(fb + (size_t)(Y + j) * PW + X, pc_buf + (size_t)j * Wp, (size_t)Wp * 4); return; }
    u32 *bak = (u32 *)malloc((size_t)Wp * Hp * 4); if (!bak) return;
    for (int j = 0; j < Hp; j++) memcpy(bak + (size_t)j * Wp, fb + (size_t)(Y + j) * PW + X, (size_t)Wp * 4);
    blur_rect(X, Y, X + Wp, Y + Hp, rad, passes);
    float R = SC(r), cx = Wp / 2.f, cy = Hp / 2.f, hw = Wp / 2.f - R, hh = Hp / 2.f - R;
    for (int j = 0; j < Hp; j++) for (int i = 0; i < Wp; i++) {
        float dx = fabsf(i + .5f - cx) - hw, dy = fabsf(j + .5f - cy) - hh; float ox = dx > 0 ? dx : 0, oy = dy > 0 ? dy : 0; float sd = sqrtf(ox * ox + oy * oy) + fminf(fmaxf(dx, dy), 0) - R; float cv = clampf(.5f - sd, 0, 1);
        if (cv >= 1) continue; u32 *p = fb + (size_t)(Y + j) * PW + X + i; *p = 0xFF000000u | mixc(bak[(size_t)j * Wp + i] & 0xFFFFFF, *p & 0xFFFFFF, cv);
    }
    free(bak);
    if (cached) { if (!pc_buf || pc_w != Wp || pc_h != Hp) { free(pc_buf); pc_buf = (u32 *)malloc((size_t)Wp * Hp * 4); } pc_w = Wp; pc_h = Hp; pc_x = X; pc_y = Y; pc_age = 1;
        if (pc_buf) for (int j = 0; j < Hp; j++) memcpy(pc_buf + (size_t)j * Wp, fb + (size_t)(Y + j) * PW + X, (size_t)Wp * 4); }
}
static void glass(float x, float y, float w, float h, float r, float strength, int cached) {
    blur_rrect(x, y, w, h, r, (int)(9 * S), 2, cached);
    rrect(x, y, w, h, r, mixc(skyTop, 0x05080f, .55f), .22f * strength + .1f);
    rrect_grad(x, y, w, h, r, 0xFFFFFF, .20f * strength, 0xFFFFFF, .05f * strength);
    rrect_line(x, y, w, h, r, 1.1f, 0xFFFFFF, .32f); rrect_line(x + 1, y + 1, w - 2, h - 2, r - 1, .8f, 0xFFFFFF, .07f);
}

static void draw_ui(void) {
    struct tm tm; city_time(t_off, &tm); char buf[96];
    u32 acc = accent_of(g_cond);
    /* header */
    char city[80]; snprintf(city, sizeof city, "%s", cfg.city[0] ? cfg.city : "SKYGLASS"); for (char *c = city; *c; c++) if (*c >= 'a' && *c <= 'z') *c -= 32;
    text_shadow(1, 12.5f, 24, 38, city, 0xFFFFFF, .95f, 2.2f, 0);
    static const char *MON[] = { "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec" };
    snprintf(buf, sizeof buf, "%s %d %s  ·  %02d:%02d", DAYS3[tm.tm_wday], tm.tm_mday, MON[tm.tm_mon], tm.tm_hour, tm.tm_min); text_shadow(1, 11, 24, 56, buf, 0xFFFFFF, .78f, .4f, 0);
    for (int i = 0; i < 3; i++) circle(CW - 28 + i * 6.5f - 6.5f, 34, 1.7f, 0xFFFFFF, .85f);
    /* hero */
    snprintf(buf, sizeof buf, "%d", tfv(W.temp)); float tw = text_w(0, 98, buf, -2); text_shadow(0, 98, 20, 150, buf, 0xFFFFFF, .98f, -2, 0);
    text_shadow(0, 34, 22 + tw + 3, 100, cfg.units ? "°F" : "°C", 0xFFFFFF, .85f, 0, 0);
    const char *lab = (ov_cond < 0 && W.phrase[0]) ? W.phrase : cond_label[g_cond];
    text_shadow(1, 17, 24, 180, lab, acc, 1, .3f, 0);
    float hi = W.nf ? W.f[0].hi : W.temp, lo = W.nf ? W.f[0].lo : W.temp;
    snprintf(buf, sizeof buf, "H %d°   L %d°   ·   Feels %d°", tfv(hi), tfv(lo), tfv(W.feels)); text_shadow(1, 12, 24, 202, buf, 0xFFFFFF, .82f, .2f, 0);
    if (g_msg_t > 0) text_shadow(1, 13, CW / 2.f, 236, g_msg, RGB(255, 244, 200), clampf(g_msg_t, 0, 1), .5f, 1);
    /* glass panel */
    float px = 12, py = PANEL_Y, pw = CW - 24, ph = 134;
    glass(px, py, pw, ph, 24, 1, 1);
    float gx[3] = { px + pw / 6, px + pw / 2, px + pw * 5 / 6 }, gy = py + 33;
    snprintf(buf, sizeof buf, "%d%%", (int)W.hum); gauge_ring(gx[0], gy, 20, W.hum / 100.f, RGB(90, 200, 255), buf, "HUMIDITY", g_t);
    snprintf(buf, sizeof buf, "%d", (int)lroundf(cfg.units ? W.wind * .621f : W.wind)); gauge_wind(gx[1], gy, 20, W.wdir, buf, g_t);
    if (W.aqi > 0) { float f = clampf(W.aqi / 200.f, 0, 1); u32 c = f < .25f ? RGB(120, 230, 120) : f < .5f ? RGB(250, 220, 90) : f < .75f ? RGB(255, 150, 70) : RGB(255, 80, 90); snprintf(buf, sizeof buf, "%d", (int)W.aqi); gauge_ring(gx[2], gy, 20, f, c, buf, "AIR QUALITY", g_t); }
    else { snprintf(buf, sizeof buf, "%d", (int)W.uv); float f = clampf(W.uv / 11.f, 0, 1); u32 c = f < .3f ? RGB(120, 230, 120) : f < .55f ? RGB(250, 220, 90) : f < .8f ? RGB(255, 150, 70) : RGB(255, 80, 90); gauge_ring(gx[2], gy, 20, f, c, buf, "UV INDEX", g_t); }
    capsule(px + 18, py + 70, px + pw - 18, py + 70, .5f, .5f, 0xFFFFFF, .16f);
    int n = W.nf; float cwid = (pw - 12) / (n ? n : 1);
    for (int i = 0; i < n; i++) {
        float cx = px + 6 + cwid * (i + .5f), cy = py + 70; Fc *f = &W.f[i];
        if (i == 0) rrect(cx - cwid / 2 + 3, cy + 4, cwid - 6, ph - 76, 12, 0xFFFFFF, .09f);
        text(1, 8.8f, cx, cy + 15, i == 0 ? "TODAY" : f->day, i == 0 ? acc : 0xFFFFFF, i == 0 ? 1 : .62f, 1.2f, 1);
        icon(f->cond, cx, cy + 30, .85f, g_t + i * .7f);
        snprintf(buf, sizeof buf, "%d°", tfv(f->hi)); text(1, 11.5f, cx - 9, cy + 50, buf, 0xFFFFFF, .95f, 0, 1); snprintf(buf, sizeof buf, "%d°", tfv(f->lo)); text(1, 11.5f, cx + 11, cy + 50, buf, 0xFFFFFF, .5f, 0, 1);
    }
    /* status line */
    /*if (status_t > 0) { text(1, 9.5f, CW / 2.f, 20, status, RGB(255, 236, 190), clampf(status_t, 0, 1), .5f, 1); }
    else if (has_w) { snprintf(buf, sizeof buf, "%s%s", W.src, job.active ? "  ·  updating" : ""); text(1, 8.6f, CW - 24, 214, buf, 0xFFFFFF, .5f, .6f, 2); }
    *//* menu */
    if (ui_mode == 2) {
        float mx = CW - 196, my = 48, mw = 176, mh = NMENU * 30 + 12; glass(mx, my, mw, mh, 16, 1.5f, 0);
        for (int i = 0; i < NMENU; i++) { char it[64]; const char *s = MENU_ITEMS[i];
            if (i == 1) snprintf(it, sizeof it, "Units: %s", cfg.units ? "°F  (tap for °C)" : "°C  (tap for °F)");
            else if (i == 3) snprintf(it, sizeof it, "Weather: %s", ov_cond < 0 ? "live" : cond_name[ov_cond]);
            else if (i == 4) snprintf(it, sizeof it, "Time-lapse: %s", lapse ? "on" : "off");
            else if (i == 5) snprintf(it, sizeof it, "Showreel: %s", reel ? "on" : "off");
            else snprintf(it, sizeof it, "%s", s);
            text(1, 12, mx + 16, my + 28 + i * 30, it, i == NMENU - 1 ? RGB(255, 150, 150) : 0xFFFFFF, .92f, .2f, 0); }
    }
    /* city search */
    if (ui_mode == 1) {
        rrect(0, 0, CW, CH, 30, 0x03060c, .55f);
        float bx = 26, by = 104, bw = CW - 52, bh = 292; glass(bx, by, bw, bh, 22, 1.6f, 0);
        text(1, 17, bx + 22, by + 40, has_w || cfg.have_city ? "Change city" : "Where are you?", 0xFFFFFF, 1, .3f, 0);
        text(1, 10.5f, bx + 22, by + 60, "Type a city, then pick it. It will be remembered.", 0xFFFFFF, .6f, 0, 0);
        rrect(bx + 18, by + 74, bw - 36, 38, 12, 0x000000, .28f); rrect_line(bx + 18, by + 74, bw - 36, 38, 12, 1, 0xFFFFFF, .3f);
        float tw2 = text_w(1, 15, qbuf, 0); text(1, 15, bx + 32, by + 99, qbuf, 0xFFFFFF, 1, 0, 0);
        if (qlen == 0) text(1, 14, bx + 32, by + 99, "Search city…", 0xFFFFFF, .35f, 0, 0);
        if (fmodf(caret_t, 1.f) < .6f) rrect(bx + 33 + tw2, by + 83, 1.5f, 20, .5f, RGB(120, 210, 255), 1);
        for (int i = 0; i < nhits; i++) { float ry = by + 126 + i * 26; if (i == qsel) rrect(bx + 12, ry - 3, bw - 24, 25, 9, 0xFFFFFF, .14f);
            snprintf(buf, sizeof buf, "%s%s%s  ·  %s", hits[i].name, hits[i].admin[0] ? ", " : "", hits[i].admin, hits[i].country); text(1, 12.5f, bx + 24, ry + 14, buf, 0xFFFFFF, i == qsel ? 1 : .8f, 0, 0); }
        if (nhits == 0) text(1, 11, bx + 24, by + 150, job.active ? "searching…" : (q_searched ? "no match — try another spelling" : ""), 0xFFFFFF, .55f, 0, 0);
        text(1, 9.5f, CW / 2.f, by + bh - 14, "Enter to select  ·  Esc to cancel", 0xFFFFFF, .45f, .4f, 1);
    }
}

/* ---------- composition / masking ---------- */
static void init_shadow(void) {
    shadow_a = (u8 *)calloc((size_t)PW * PH, 1);
    float cx = (MARG + CW / 2.f) * S, cy = (MARG + CH / 2.f + 4) * S, hw = CW / 2.f * S - 30 * S, hh = CH / 2.f * S - 30 * S, R = 30 * S;
    for (int y = 0; y < PH; y++) for (int x = 0; x < PW; x++) {
        float dx = fabsf(x + .5f - cx) - hw, dy = fabsf(y + .5f - cy) - hh; float ox = dx > 0 ? dx : 0, oy = dy > 0 ? dy : 0; float sd = (sqrtf(ox * ox + oy * oy) + fminf(fmaxf(dx, dy), 0) - R) / S;
        float a = expf(-powf(fmaxf(sd, 0) / 8.5f, 1.6f)) * .42f; shadow_a[(size_t)y * PW + x] = (u8)(a * 255);
    }
}
static void finish_mask(void) {
    int x0 = (int)(MARG * S), x1 = (int)((MARG + CW) * S), y0 = (int)(MARG * S), y1 = (int)((MARG + CH) * S);
    for (int y = 0; y < PH; y++) { size_t o = (size_t)y * PW; if (y < y0 || y >= y1) { for (int x = 0; x < PW; x++) fb[o + x] = (u32)shadow_a[o + x] << 24; } else { for (int x = 0; x < x0; x++) fb[o + x] = (u32)shadow_a[o + x] << 24; for (int x = x1; x < PW; x++) fb[o + x] = (u32)shadow_a[o + x] << 24; } }
    float R = 30 * S, cx = (x0 + x1) / 2.f, cy = (y0 + y1) / 2.f, hw = (x1 - x0) / 2.f - R, hh = (y1 - y0) / 2.f - R; int rr = (int)ceilf(R) + 2;
    for (int cn = 0; cn < 4; cn++) { int bx = (cn & 1) ? x1 - rr : x0, by = (cn & 2) ? y1 - rr : y0;
        for (int y = by; y < by + rr; y++) for (int x = bx; x < bx + rr; x++) {
            float dx = fabsf(x + .5f - cx) - hw, dy = fabsf(y + .5f - cy) - hh; float ox = dx > 0 ? dx : 0, oy = dy > 0 ? dy : 0; float sd = sqrtf(ox * ox + oy * oy) + fminf(fmaxf(dx, dy), 0) - R; float cv = clampf(.5f - sd, 0, 1);
            if (cv >= 1) continue; size_t i = (size_t)y * PW + x; u32 sc = fb[i]; float sa = shadow_a[i] / 255.f;
            int r = (int)(((sc >> 16) & 255) * cv), g = (int)(((sc >> 8) & 255) * cv), b = (int)((sc & 255) * cv), a = (int)((cv + sa * (1 - cv)) * 255);
            fb[i] = ((u32)a << 24) | (r << 16) | (g << 8) | b; } }
}
static void render_frame(void) { draw_world(); draw_ui(); finish_mask(); }

/* ---------- weather -> scene ---------- */
static void apply_env(void) {
    int c = ov_cond >= 0 ? ov_cond : W.cond; g_cond = c; const float *p = CP[c];
    T.cover = p[0]; T.dark = p[1]; T.rain = p[2]; T.snow = p[3]; T.hail = p[4]; T.fog = p[5]; T.dust = p[6]; T.storm = p[7]; T.heat = (c == C_HEAT || (c == C_CLEAR && W.temp >= 37)) ? 1.f : 0.f; T.wind = fmaxf(W.wind, p[8] * .6f);
    T.aur = (g_force_aur > .5f || ((c == C_CLEAR || c == C_PARTLY) && (W.temp < 3 || fabsf(cfg.lat) > 58))) ? 1.f : 0.f;
    g_wsign = W.wind > 0 ? -sinf(W.wdir * PI_F / 180) : 1; if (fabsf(g_wsign) < .25f) g_wsign = g_wsign >= 0 ? .25f : -.25f; g_temp = W.temp; g_uv = W.uv;
}
static void apply_time(void) {
    static float last = -9; static struct tm tm; if (g_t - last > .25f || last < 0) { last = g_t; city_time(t_off, &tm); }
    float hour = tm.tm_hour + tm.tm_min / 60.f + tm.tm_sec / 3600.f; float rise = W.rise, set = W.set;
    if (rise <= 0 && set <= 0) { sun_times(cfg.lat, cfg.lon, tm.tm_yday, W.has_off ? W.tz_off : utc_off_hours(), &rise, &set); }
    if (set - rise < 1 || set - rise > 23) { rise = 6; set = 18; }
    g_hour = hour; g_rise = rise; g_set = set; g_moon = moon_phase(time(NULL) + (time_t)(t_off * 3600));
    if (hour >= rise && hour <= set) { g_f = (hour - rise) / (set - rise); g_isday = 1; g_alt = sinf(PI_F * g_f); }
    else { float nl = 24 - (set - rise); float h2 = fmodf(hour - set + 24, 24); g_f = h2 / nl; g_isday = 0; g_alt = -sinf(PI_F * g_f) * .35f; }
    g_night = smoothf(.05f, -.12f, g_alt);
    int m = tm.tm_mon + 1; g_season = (m >= 9 && m <= 11) ? 0 : (m == 12 || m <= 2) ? 2 : 1; if (cfg.lat < 0) g_season = g_season == 0 ? 1 : g_season == 2 ? 1 : 0; if (cfg.lat < 0 && (m == 12 || m <= 2)) g_season = 1;
}

/* ---------- network flow ---------- */
static void builtin_hits(void);
static int fstage = 0; static char *twc_cur = NULL;
static void fetch_start(void) {
    if (g_demo || !cfg.have_city || job.active) return;
    char url[1400]; last_fetch_t = g_t;
    if (cfg.key[0]) { snprintf(url, sizeof url, "https://api.weather.com/v3/wx/observations/current?geocode=%.3f,%.3f&units=m&language=en-US&format=json&apiKey=%s", cfg.lat, cfg.lon, cfg.key); fstage = 1; }
    else { snprintf(url, sizeof url, "https://api.open-meteo.com/v1/forecast?latitude=%.3f&longitude=%.3f&timezone=auto&forecast_days=5&current=temperature_2m,apparent_temperature,relative_humidity_2m,weather_code,wind_speed_10m,wind_direction_10m,surface_pressure&daily=weather_code,temperature_2m_max,temperature_2m_min,sunrise,sunset,uv_index_max,precipitation_probability_max", cfg.lat, cfg.lon); fstage = 3; }
    job_start(url, fstage);
}
static void air_start(void) { char url[600]; snprintf(url, sizeof url, "https://air-quality-api.open-meteo.com/v1/air-quality?latitude=%.3f&longitude=%.3f&current=us_aqi", cfg.lat, cfg.lon); fstage = 4; job_start(url, 4); }
static void commit_weather(Weather *n) {
    float aq = W.aqi; *&W = *n; if (W.aqi <= 0) W.aqi = aq; has_w = 1; W.valid = 1;
    if (!cfg.tz[0] && W.tz[0]) { snprintf(cfg.tz, sizeof cfg.tz, "%s", W.tz); cfg_save(); }
}
static void net_tick(void) {
    int r = job_poll(); if (r == 0) return;
    if (r < 0) { if (fstage == 1 || fstage == 2) { fstage = 0; char url[1400]; snprintf(url, sizeof url, "https://api.open-meteo.com/v1/forecast?latitude=%.3f&longitude=%.3f&timezone=auto&forecast_days=5&current=temperature_2m,apparent_temperature,relative_humidity_2m,weather_code,wind_speed_10m,wind_direction_10m,surface_pressure&daily=weather_code,temperature_2m_max,temperature_2m_min,sunrise,sunset,uv_index_max,precipitation_probability_max", cfg.lat, cfg.lon); fstage = 3; job_start(url, 3); return; }
        if (fstage == 3 && !has_w) { demo_weather(&W); has_w = 1; toast("offline - showing demo data"); } if (fstage == 5) { builtin_hits(); q_searched = 1; } fstage = 0; return; }
    Weather n; memset(&n, 0, sizeof n); n.rise = n.set = 0;
    if (job.kind == 1) { free(twc_cur); twc_cur = strdup(job.buf); char url[1400]; snprintf(url, sizeof url, "https://api.weather.com/v3/wx/forecast/daily/5day?geocode=%.3f,%.3f&format=json&units=m&language=en-US&apiKey=%s", cfg.lat, cfg.lon, cfg.key); fstage = 2; job_start(url, 2); return; }
    if (job.kind == 2) { if (parse_twc(twc_cur ? twc_cur : "", job.buf, &n)) { commit_weather(&n); } free(twc_cur); twc_cur = NULL; air_start(); return; }
    if (job.kind == 3) { if (parse_openmeteo(job.buf, &n)) commit_weather(&n); air_start(); return; }
    if (job.kind == 4) { const char *c = strstr(job.buf, "\"current\":{"); if (c) { float a = (float)jnum(jkey(c + 10, "us_aqi"), 0); if (a > 0) W.aqi = a; } fstage = 0; return; }
    if (job.kind == 5) { if (cfg.key[0] && strstr(job.buf, "\"location\"")) parse_hits_twc(job.buf); else parse_hits_openmeteo(job.buf); q_searched = 1; qsel = 0; fstage = 0; return; }
}
static const struct { const char *n, *cc, *tz; float la, lo; } BUILTIN[] = { { "Algiers", "DZ", "Africa/Algiers", 36.75f, 3.06f }, { "Oran", "DZ", "Africa/Algiers", 35.7f, -.63f }, { "Paris", "FR", "Europe/Paris", 48.85f, 2.35f }, { "London", "GB", "Europe/London", 51.51f, -.13f },
    { "New York", "US", "America/New_York", 40.71f, -74.01f }, { "Tokyo", "JP", "Asia/Tokyo", 35.68f, 139.69f }, { "Dubai", "AE", "Asia/Dubai", 25.2f, 55.27f }, { "Berlin", "DE", "Europe/Berlin", 52.52f, 13.4f }, { "Cairo", "EG", "Africa/Cairo", 30.04f, 31.24f },
    { "Reykjavik", "IS", "Atlantic/Reykjavik", 64.15f, -21.94f }, { "Sydney", "AU", "Australia/Sydney", -33.87f, 151.21f }, { "Moscow", "RU", "Europe/Moscow", 55.75f, 37.62f } };
static void builtin_hits(void) {
    nhits = 0; for (unsigned i = 0; i < sizeof BUILTIN / sizeof *BUILTIN && nhits < 6; i++) { if (strncasecmp(BUILTIN[i].n, qbuf, qlen) == 0) { CityHit *h = &hits[nhits++]; memset(h, 0, sizeof *h); snprintf(h->name, sizeof h->name, "%s", BUILTIN[i].n); snprintf(h->country, sizeof h->country, "%s", BUILTIN[i].cc); snprintf(h->tz, sizeof h->tz, "%s", BUILTIN[i].tz); h->lat = BUILTIN[i].la; h->lon = BUILTIN[i].lo; snprintf(h->admin, sizeof h->admin, "offline list"); } }
}
static void search_start(void) {
    if (qlen < 2 || job.active) return; char enc[200], url[700]; urlenc(qbuf, enc, sizeof enc);
    if (cfg.key[0]) snprintf(url, sizeof url, "https://api.weather.com/v3/location/search?query=%s&locationType=city&language=en-US&format=json&apiKey=%s", enc, cfg.key);
    else snprintf(url, sizeof url, "https://geocoding-api.open-meteo.com/v1/search?name=%s&count=6&language=en&format=json", enc);
    fstage = 5; q_dirty = 0; job_start(url, 5);
}
static void choose_city(int i) {
    if (i < 0 || i >= nhits) return; CityHit *h = &hits[i]; snprintf(cfg.city, sizeof cfg.city, "%s", h->name); snprintf(cfg.country, sizeof cfg.country, "%s", h->country); snprintf(cfg.tz, sizeof cfg.tz, "%s", h->tz); cfg.lat = h->lat; cfg.lon = h->lon; cfg.have_city = 1; cfg_save();
    ui_mode = 0; has_w = 0; memset(&W, 0, sizeof W); if (g_demo) { demo_weather(&W); has_w = 1; } scene_init(hash_str(cfg.city)); if (job.active) { pclose(job.fp); job.active = 0; } fstage = 0; fetch_start();
}
static void open_search(void) { ui_mode = 1; qlen = 0; qbuf[0] = 0; nhits = 0; qsel = 0; q_searched = 0; q_dirty = 0; }
static void do_menu(int i) {
    switch (i) {
    case 0: open_search(); break;
    case 1: cfg.units = !cfg.units; cfg_save(); break;
    case 2: if (!job.active) { fetch_start(); toast("refreshing…"); } ui_mode = 0; break;
    case 3: ov_cond = ov_cond < 0 ? 0 : (ov_cond + 1 >= NCOND ? -1 : ov_cond + 1); break;
    case 4: lapse = !lapse; break;
    case 5: reel = !reel; reel_i = 0; reel_target = -1; if (reel) ov_cond = REEL[0].c; break;
    case 6: train_spawn(-1, 0); ui_mode = 0; break;
    case 7: quit_flag = 1; break;
    }
}
static void sim_tick(float dt) {
    if (lapse) t_off += dt * .6f;
    if (reel) { reel_t += dt; if (reel_target < 0) { ov_cond = REEL[reel_i % 12].c; reel_target = REEL[reel_i % 12].h; reel_t = 0; } else { struct tm tm; city_time(t_off, &tm); float cur = tm.tm_hour + tm.tm_min / 60.f; float diff = fmodf(reel_target - cur + 24, 24); if (diff > .15f) t_off += fminf(diff, dt * 4.5f); else if (reel_t > 11) { reel_i++; reel_target = -1; } } }
    if (t_off > 48) t_off = 48; if (t_off < -48) t_off = -48; if (status_t > 0) status_t -= dt; caret_t += dt;
    net_tick(); if (ui_mode == 1 && q_dirty && g_t - q_t > .6f && !job.active) search_start();
    if (!g_demo && cfg.have_city && !job.active && g_t - last_fetch_t > 600) fetch_start();
}

/* ======================================================================
 *  X11 window (ARGB visual + MIT-SHM) and main loop
 * ====================================================================== */
static Display *dpy; static Window win; static GC xgc; static XImage *ximg; static XShmSegmentInfo shminfo; static int use_shm = 0, vis_ok = 1;
static XIC xic; static Atom wm_delete;
static double now_s(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }
static void die(const char *m) { fprintf(stderr, "skyglass: %s\n", m); exit(1); }
static void set_atoms(void) {
    Atom st = XInternAtom(dpy, "_NET_WM_STATE", 0), list[4]; int n = 0;
    list[n++] = XInternAtom(dpy, "_NET_WM_STATE_STICKY", 0); list[n++] = XInternAtom(dpy, "_NET_WM_STATE_SKIP_TASKBAR", 0); list[n++] = XInternAtom(dpy, "_NET_WM_STATE_SKIP_PAGER", 0);
    if (cfg.below) list[n++] = XInternAtom(dpy, "_NET_WM_STATE_BELOW", 0); else if (cfg.ontop) list[n++] = XInternAtom(dpy, "_NET_WM_STATE_ABOVE", 0);
    XChangeProperty(dpy, win, st, XA_ATOM, 32, PropModeReplace, (unsigned char *)list, n);
    Atom wt = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE", 0), ut = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE_UTILITY", 0); XChangeProperty(dpy, win, wt, XA_ATOM, 32, PropModeReplace, (unsigned char *)&ut, 1);
    struct { unsigned long flags, functions, decorations; long input_mode; unsigned long status; } mh = { 2, 0, 0, 0, 0 };
    Atom mo = XInternAtom(dpy, "_MOTIF_WM_HINTS", 0); XChangeProperty(dpy, win, mo, mo, 32, PropModeReplace, (unsigned char *)&mh, 5);
    wm_delete = XInternAtom(dpy, "WM_DELETE_WINDOW", 0); XSetWMProtocols(dpy, win, &wm_delete, 1);
    XClassHint ch = { (char *)"skyglass", (char *)"Skyglass" }; XSetClassHint(dpy, win, &ch); XStoreName(dpy, win, "Skyglass");
}
static void x_shape_fallback(void) {
    Atom cm = XInternAtom(dpy, "_NET_WM_CM_S0", 0); if (XGetSelectionOwner(dpy, cm) != None) return;
    int ev, er; if (!XShapeQueryExtension(dpy, &ev, &er)) return;
    Pixmap pm = XCreatePixmap(dpy, win, PW, PH, 1); GC g = XCreateGC(dpy, pm, 0, NULL); XSetForeground(dpy, g, 0); XFillRectangle(dpy, pm, g, 0, 0, PW, PH); XSetForeground(dpy, g, 1);
    int x = (int)(MARG * S), y = (int)(MARG * S), w = (int)(CW * S), h = (int)(CH * S), r = (int)(30 * S);
    XFillRectangle(dpy, pm, g, x + r, y, w - 2 * r, h); XFillRectangle(dpy, pm, g, x, y + r, w, h - 2 * r);
    XFillArc(dpy, pm, g, x, y, 2 * r, 2 * r, 0, 360 * 64); XFillArc(dpy, pm, g, x + w - 2 * r, y, 2 * r, 2 * r, 0, 360 * 64); XFillArc(dpy, pm, g, x, y + h - 2 * r, 2 * r, 2 * r, 0, 360 * 64); XFillArc(dpy, pm, g, x + w - 2 * r, y + h - 2 * r, 2 * r, 2 * r, 0, 360 * 64);
    XShapeCombineMask(dpy, win, ShapeBounding, 0, 0, pm, ShapeSet); XFreeGC(dpy, g); XFreePixmap(dpy, pm);
}
static void x_create(void) {
    dpy = XOpenDisplay(NULL); if (!dpy) die("cannot open X display (is DISPLAY set? Wayland users: XWayland must be running)");
    int scr = DefaultScreen(dpy); Window root = RootWindow(dpy, scr); XVisualInfo vi; if (!XMatchVisualInfo(dpy, scr, 32, TrueColor, &vi)) die("no 32-bit ARGB visual available");
    int sw = DisplayWidth(dpy, scr), sh = DisplayHeight(dpy, scr); int x = cfg.have_pos ? cfg.px : sw - PW - 30, y = cfg.have_pos ? cfg.py : 50; if (x > sw - 40) x = sw - PW; if (y > sh - 40) y = 40; if (x < -PW + 60) x = 0; if (y < 0) y = 0;
    XSetWindowAttributes a; memset(&a, 0, sizeof a); a.colormap = XCreateColormap(dpy, root, vi.visual, AllocNone); a.border_pixel = 0; a.background_pixel = 0;
    a.event_mask = ExposureMask | KeyPressMask | ButtonPressMask | ButtonReleaseMask | PointerMotionMask | StructureNotifyMask | VisibilityChangeMask | FocusChangeMask;
    win = XCreateWindow(dpy, root, x, y, PW, PH, 0, 32, InputOutput, vi.visual, CWColormap | CWBorderPixel | CWBackPixel | CWEventMask, &a);
    XSizeHints *sz = XAllocSizeHints(); sz->flags = PMinSize | PMaxSize | PPosition; sz->min_width = sz->max_width = PW; sz->min_height = sz->max_height = PH; sz->x = x; sz->y = y; XSetWMNormalHints(dpy, win, sz); XFree(sz);
    set_atoms(); xgc = XCreateGC(dpy, win, 0, NULL);
    int shmok = XShmQueryExtension(dpy);
    if (shmok) {
        ximg = XShmCreateImage(dpy, vi.visual, 32, ZPixmap, NULL, &shminfo, PW, PH);
        if (ximg) { shminfo.shmid = shmget(IPC_PRIVATE, (size_t)ximg->bytes_per_line * ximg->height, IPC_CREAT | 0600);
            if (shminfo.shmid >= 0) { shminfo.shmaddr = ximg->data = (char *)shmat(shminfo.shmid, 0, 0); shminfo.readOnly = False;
                if (shminfo.shmaddr != (char *)-1 && XShmAttach(dpy, &shminfo)) { XSync(dpy, False); shmctl(shminfo.shmid, IPC_RMID, 0); use_shm = 1; } } }
    }
    if (!use_shm) { if (ximg) { ximg->data = NULL; XDestroyImage(ximg); } ximg = XCreateImage(dpy, vi.visual, 32, ZPixmap, 0, (char *)malloc((size_t)PW * PH * 4), PW, PH, 32, 0); }
    fb = (u32 *)ximg->data;
    XIM xim = XOpenIM(dpy, NULL, NULL, NULL); xic = xim ? XCreateIC(xim, XNInputStyle, XIMPreeditNothing | XIMStatusNothing, XNClientWindow, win, XNFocusWindow, win, NULL) : NULL;
    XMapWindow(dpy, win); x_shape_fallback();
}
static void present(void) { if (use_shm) XShmPutImage(dpy, win, xgc, ximg, 0, 0, 0, 0, PW, PH, False); else XPutImage(dpy, win, xgc, ximg, 0, 0, 0, 0, PW, PH); XSync(dpy, False); }

static int drag = 0, dragged = 0, drag_rx, drag_ry, drag_wx, drag_wy; static double pos_dirty = 0; static int wm_moveresize = -1;
static int wm_has_moveresize(void) {
    Atom sup = XInternAtom(dpy, "_NET_SUPPORTED", 0), mr = XInternAtom(dpy, "_NET_WM_MOVERESIZE", 0), type; int fmt; unsigned long n, after; unsigned char *data = NULL; int ok = 0;
    if (XGetWindowProperty(dpy, DefaultRootWindow(dpy), sup, 0, 4096, False, XA_ATOM, &type, &fmt, &n, &after, &data) == Success && data) { Atom *a = (Atom *)data; for (unsigned long i = 0; i < n; i++) if (a[i] == mr) ok = 1; XFree(data); }
    return ok;
}
static void wm_begin_move(XButtonEvent *b) {
    XUngrabPointer(dpy, CurrentTime); XEvent e; memset(&e, 0, sizeof e); e.xclient.type = ClientMessage; e.xclient.window = win; e.xclient.message_type = XInternAtom(dpy, "_NET_WM_MOVERESIZE", 0); e.xclient.format = 32;
    e.xclient.data.l[0] = b->x_root; e.xclient.data.l[1] = b->y_root; e.xclient.data.l[2] = 8; e.xclient.data.l[3] = Button1; e.xclient.data.l[4] = 1;
    XSendEvent(dpy, DefaultRootWindow(dpy), False, SubstructureNotifyMask | SubstructureRedirectMask, &e); XFlush(dpy);
}
static void save_pos(void) { Window ch; int x, y; XTranslateCoordinates(dpy, win, DefaultRootWindow(dpy), 0, 0, &x, &y, &ch); cfg.px = x; cfg.py = y; cfg.have_pos = 1; cfg_save(); }
static void key_normal(KeySym ks, const char *s) {
    char c = s && s[0] ? s[0] : 0;
    if (ks == XK_Escape) { ui_mode = 0; return; }
    switch (c) {
    case 'q': quit_flag = 1; break; case 'c': ov_cond = ov_cond < 0 ? 0 : (ov_cond + 1 >= NCOND ? -1 : ov_cond + 1); break; case 'C': ov_cond = ov_cond < 0 ? NCOND - 1 : ov_cond - 1; break;
    case '0': ov_cond = -1; t_off = 0; lapse = 0; reel = 0; break; case ']': t_off += .5f; break; case '[': t_off -= .5f; break; case 'f': lapse = !lapse; break; case 'w': do_menu(5); break;
    case 't': train_spawn(-1, 0); break; case 'l': strike(); break; case 'a': g_force_aur = g_force_aur > .5f ? 0 : 1; break; case 'u': do_menu(1); break; case 'r': do_menu(2); break; case 'n': open_search(); break;
    case 'o': memset(&ufo, 0, sizeof ufo); ufo.on = 1; ufo.x = -20; ufo.y = 80; ufo.tx = sheep_x; ufo.side = 1; break;
    }
}
static void handle_event(XEvent *ev) {
    switch (ev->type) {
    case ClientMessage: if ((Atom)ev->xclient.data.l[0] == wm_delete) quit_flag = 1; break;
    case VisibilityNotify: vis_ok = ev->xvisibility.state != VisibilityFullyObscured; break;
    case ConfigureNotify: pos_dirty = now_s(); break;
    case UnmapNotify: vis_ok = 0; break; case MapNotify: vis_ok = 1; break;
    case KeyPress: {
        char buf[64]; KeySym ks = 0; int n; Status st;
        if (xic) n = Xutf8LookupString(xic, &ev->xkey, buf, sizeof buf - 1, &ks, &st); else n = XLookupString(&ev->xkey, buf, sizeof buf - 1, &ks, NULL);
        if (n < 0) n = 0; buf[n] = 0;
        if (ui_mode == 1) {
            if (ks == XK_Escape) { if (cfg.have_city) ui_mode = 0; }
            else if (ks == XK_Return || ks == XK_KP_Enter) { if (nhits > 0 && !q_dirty) choose_city(qsel); else search_start(); }
            else if (ks == XK_BackSpace) { while (qlen > 0 && ((unsigned char)qbuf[qlen - 1] & 0xC0) == 0x80) qlen--; if (qlen > 0) qlen--; qbuf[qlen] = 0; q_dirty = 1; q_t = g_t; nhits = 0; q_searched = 0; }
            else if (ks == XK_Down) { if (nhits) qsel = (qsel + 1) % nhits; } else if (ks == XK_Up) { if (nhits) qsel = (qsel + nhits - 1) % nhits; }
            else if (n > 0 && (unsigned char)buf[0] >= 32 && buf[0] != 127 && qlen + n < (int)sizeof qbuf - 1) { memcpy(qbuf + qlen, buf, n); qlen += n; qbuf[qlen] = 0; q_dirty = 1; q_t = g_t; nhits = 0; q_searched = 0; }
        } else if (ui_mode == 2) { if (ks == XK_Escape) ui_mode = 0; else key_normal(ks, buf); } else key_normal(ks, buf);
        break; }
    case ButtonPress: {
        float lx = ev->xbutton.x / S - MARG, ly = ev->xbutton.y / S - MARG; int b = ev->xbutton.button;
        if (b == 4) { t_off += .25f; break; } if (b == 5) { t_off -= .25f; break; }
        if (ui_mode == 2) { float mx = CW - 196, my = 48, mw = 176; int hit = -1; for (int i = 0; i < NMENU; i++) if (in_rect(lx, ly, mx, my + 8 + i * 30, mw, 30)) hit = i; if (hit >= 0 && b == 1) { do_menu(hit); if (hit != 1 && hit != 3 && hit != 4 && hit != 5) { if (ui_mode == 2) ui_mode = 0; } } else ui_mode = 0; break; }
        if (ui_mode == 1) { float bx = 26, by = 104, bw = CW - 52, bh = 292; int hit = -1; for (int i = 0; i < nhits; i++) if (in_rect(lx, ly, bx + 12, by + 123 + i * 26, bw - 24, 25)) hit = i; if (hit >= 0) choose_city(hit); else if (!in_rect(lx, ly, bx, by, bw, bh) && cfg.have_city) ui_mode = 0; break; }
        if (b == 3 || (b == 1 && in_rect(lx, ly, CW - 56, 12, 50, 44))) { ui_mode = 2; break; }
        if (b == 1 && wm_moveresize < 0) wm_moveresize = wm_has_moveresize();
        if (b == 1 && wm_moveresize > 0) { wm_begin_move(&ev->xbutton); break; }
        if (b == 1) { drag = 1; dragged = 0; drag_rx = ev->xbutton.x_root; drag_ry = ev->xbutton.y_root; Window ch; XTranslateCoordinates(dpy, win, DefaultRootWindow(dpy), 0, 0, &drag_wx, &drag_wy, &ch); }
        break; }
    case MotionNotify: if (drag) { int dx = ev->xmotion.x_root - drag_rx, dy = ev->xmotion.y_root - drag_ry; if (abs(dx) + abs(dy) > 3) dragged = 1; if (dragged) XMoveWindow(dpy, win, drag_wx + dx, drag_wy + dy); } break;
    case ButtonRelease: if (drag && ev->xbutton.button == 1) { drag = 0; if (dragged) save_pos(); } break;
    }
}
static void write_ppm(const char *path) {
    FILE *f = fopen(path, "wb"); if (!f) return; fprintf(f, "P6\n%d %d\n255\n", PW, PH);
    for (int y = 0; y < PH; y++) for (int x = 0; x < PW; x++) { u32 p = fb[(size_t)y * PW + x]; int a = p >> 24; int bgc = (((x / 12) + (y / 12)) & 1) ? 70 : 90; unsigned char px[3] = { (unsigned char)(((p >> 16) & 255) + bgc * (255 - a) / 255), (unsigned char)(((p >> 8) & 255) + bgc * (255 - a) / 255), (unsigned char)((p & 255) + bgc * (255 - a) / 255) }; fwrite(px, 1, 3, f); }
    fclose(f);
}
static void usage(void) {
    puts("skyglass - glass weather gadget (X11)\n  --demo            offline demo data\n  --city NAME       search & remember a city from the command line\n  --scale N         UI scale (1.0 default, saved)\n  --fps N           frame rate (default 30)\n  --below | --ontop keep the window under / over other windows\n  --reset           forget the saved city\n  keys: c weather  [ ] time  f lapse  w showreel  t train  l lightning  a aurora  o ufo  u units  r refresh  n city  q quit\n  mouse: drag to move, click the dots (or right-click) for the menu, wheel = time");
}
int main(int argc, char **argv) {
    const char *shot = NULL; int shot_frames = 60, shot_search = 0, shot_menu = 0, shot_train = 0, shot_aur = 0; float shot_hour = -1, shot_temp = -999; int shot_cond = -1; const char *city_arg = NULL; float scale_arg = 0;
    cfg_load();
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) { usage(); return 0; }
        else if (!strcmp(argv[i], "--demo")) g_demo = 1; else if (!strcmp(argv[i], "--reset")) { cfg.have_city = 0; cfg.city[0] = 0; }
        else if (!strcmp(argv[i], "--below")) { cfg.below = 1; cfg.ontop = 0; } else if (!strcmp(argv[i], "--ontop")) { cfg.ontop = 1; cfg.below = 0; }
        else if (!strcmp(argv[i], "--scale") && i + 1 < argc) scale_arg = atof(argv[++i]); else if (!strcmp(argv[i], "--fps") && i + 1 < argc) cfg.fps = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--city") && i + 1 < argc) city_arg = argv[++i]; else if (!strcmp(argv[i], "--key") && i + 1 < argc) snprintf(cfg.key, sizeof cfg.key, "%s", argv[++i]);
        else if (!strcmp(argv[i], "--shot") && i + 1 < argc) shot = argv[++i]; else if (!strcmp(argv[i], "--frames") && i + 1 < argc) shot_frames = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--hour") && i + 1 < argc) shot_hour = atof(argv[++i]); else if (!strcmp(argv[i], "--temp") && i + 1 < argc) shot_temp = atof(argv[++i]);
        else if (!strcmp(argv[i], "--cond") && i + 1 < argc) { i++; for (int k = 0; k < NCOND; k++) if (!strcmp(argv[i], cond_name[k])) shot_cond = k; }
        else if (!strcmp(argv[i], "--search")) shot_search = 1; else if (!strcmp(argv[i], "--menu")) shot_menu = 1; else if (!strcmp(argv[i], "--train")) shot_train = 1; else if (!strcmp(argv[i], "--aur")) shot_aur = 1;
    }
    if (!cfg.key[0] && getenv("TWC_API_KEY")) snprintf(cfg.key, sizeof cfg.key, "%s", getenv("TWC_API_KEY"));
    if (scale_arg > .5f) cfg.scale = scale_arg; S = cfg.scale; PW = (int)(WW * S); PH = (int)(WH * S);
    if (shot) { S = scale_arg > .5f ? scale_arg : 1; PW = (int)(WW * S); PH = (int)(WH * S); if (!cfg.have_city) { snprintf(cfg.city, sizeof cfg.city, "Algiers"); snprintf(cfg.country, sizeof cfg.country, "DZ"); snprintf(cfg.tz, sizeof cfg.tz, "Africa/Algiers"); cfg.lat = 36.75f; cfg.lon = 3.06f; cfg.have_city = 1; } g_demo = 1; }
    if (city_arg && !shot) { snprintf(qbuf, sizeof qbuf, "%s", city_arg); qlen = (int)strlen(qbuf);         char enc[200], url[700], cmd[900]; urlenc(city_arg, enc, sizeof enc); snprintf(url, sizeof url, "https://geocoding-api.open-meteo.com/v1/search?name=%s&count=1&language=en&format=json", enc); snprintf(cmd, sizeof cmd, "curl -sfL -m 10 '%s'", url);
        FILE *p = popen(cmd, "r"); static char big[20000]; size_t n = p ? fread(big, 1, sizeof big - 1, p) : 0; if (p) pclose(p); big[n] = 0; parse_hits_openmeteo(big);
        if (nhits > 0) { CityHit *h = &hits[0]; snprintf(cfg.city, sizeof cfg.city, "%s", h->name); snprintf(cfg.country, sizeof cfg.country, "%s", h->country); snprintf(cfg.tz, sizeof cfg.tz, "%s", h->tz); cfg.lat = h->lat; cfg.lon = h->lon; cfg.have_city = 1; cfg_save(); } else fprintf(stderr, "skyglass: city '%s' not found\n", city_arg); nhits = 0; }
    init_fonts(cfg.font_l, cfg.font_r); if (!fonts[1].ok) die("no usable TrueType font found (set SKYGLASS_FONT=/path/to/font.ttf)");
    signal(SIGPIPE, SIG_IGN);
    if (shot) { fb = (u32 *)calloc((size_t)PW * PH, 4); }
    else { x_create(); }
    init_shadow(); scene_init(hash_str(cfg.city[0] ? cfg.city : "skyglass"));
    if (!cfg.have_city) { open_search(); demo_weather(&W); has_w = 1; } else if (g_demo) { demo_weather(&W); has_w = 1; } else fetch_start();
    if (shot) {
        if (shot_cond >= 0) ov_cond = shot_cond; if (shot_temp > -900) W.temp = shot_temp, W.feels = shot_temp - 1.5f; g_force_aur = shot_aur ? 1.f : 0; if (shot_search) { open_search(); snprintf(qbuf, sizeof qbuf, "Par"); qlen = 3; nhits = 3; strcpy(hits[0].name, "Paris"); strcpy(hits[0].admin, "Île-de-France"); strcpy(hits[0].country, "FR"); strcpy(hits[1].name, "Paris"); strcpy(hits[1].admin, "Texas"); strcpy(hits[1].country, "US"); strcpy(hits[2].name, "Parma"); strcpy(hits[2].admin, "Emilia-Romagna"); strcpy(hits[2].country, "IT"); }
        if (shot_menu) ui_mode = 2;
        if (shot_hour >= 0) { struct tm tm; city_time(0, &tm); t_off = shot_hour - (tm.tm_hour + tm.tm_min / 60.f); }
        apply_env(); apply_time(); memcpy(&E, &T, sizeof(float) * 9); E.snowc = T.snow > .2f ? 1.f : 0; E.wet = E.rain > .2f ? 1.f : 0; E.aur = T.aur; next_train = 999; next_ufo = 999;
        for (int f = 0; f < shot_frames; f++) { g_t += 0; if (shot_train && f == shot_frames - 10) { train_spawn(0, 1); train.hx = CW * .6f; } apply_env(); apply_time(); scene_update(1.f / 30); }
        render_frame(); write_ppm(shot); { double t0 = now_s(); for (int k = 0; k < 20; k++) { scene_update(1.f / 30); render_frame(); } fprintf(stderr, "render: %.1f ms/frame (%dx%d)\n", (now_s() - t0) * 50, PW, PH); } return 0;
    }
    double interval = 1.0 / cfg.fps, next = now_s(), last = next; int xfd = ConnectionNumber(dpy);
    while (!quit_flag) {
        while (XPending(dpy)) { XEvent ev; XNextEvent(dpy, &ev); if (XFilterEvent(&ev, None)) continue; handle_event(&ev); }
        double t = now_s();
        if (pos_dirty > 0 && t - pos_dirty > 1.2 && cfg.have_city) { pos_dirty = 0; save_pos(); }
        if (t >= next) {
            double iv = vis_ok ? interval : .5; float dt = (float)fmin(.1, t - last); last = t; next += iv; if (next < t) next = t + iv;
            sim_tick(dt); apply_env(); apply_time(); scene_update(dt); render_frame(); present();
        }
        t = now_s(); double wait = next - t; if (wait > 0) { fd_set fds; FD_ZERO(&fds); FD_SET(xfd, &fds); struct timeval tv = { (time_t)wait, (suseconds_t)((wait - (time_t)wait) * 1e6) }; select(xfd + 1, &fds, NULL, NULL, &tv); }
    }
    if (cfg.have_city) save_pos();
    if (use_shm) { XShmDetach(dpy, &shminfo); shmdt(shminfo.shmaddr); }
    XDestroyWindow(dpy, win); XCloseDisplay(dpy); return 0;
}
