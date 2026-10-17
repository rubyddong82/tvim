/*
 * tvim - a small terminal text editor with VS Code style keys.
 *
 * Single file, no dependencies besides libc. See README.md for the key list.
 */
#define _GNU_SOURCE
#include <ctype.h>
#include <errno.h>
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
#include <strings.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

#define TVIM_VERSION "0.1.0"
#define TABW 4
#define MAX_UNDO 200

/* ---------- keys ---------- */

#undef CTRL
#define CTRL(k) ((k) & 0x1f)
#define K_SPECIAL (1 << 21)
#define M_SHIFT (1 << 22)
#define M_CTRL (1 << 23)
#define M_ALT (1 << 24)
#define K_BASE(k) ((k) & ~(M_SHIFT | M_CTRL | M_ALT))

enum {
    K_NONE = 0,
    K_UP = K_SPECIAL + 1, K_DOWN, K_LEFT, K_RIGHT, K_HOME, K_END, K_PGUP, K_PGDN,
    K_DEL, K_INS, K_F1, K_F2, K_F3, K_BTAB, K_MOUSE, K_PASTE, K_RESIZE
};

#define KEY_ESC 27
#define KEY_ENTER 13
#define KEY_TAB 9
#define KEY_BS 127

/* ---------- types ---------- */

typedef struct { char *s; int len, cap; } Line;
typedef struct { int r, c; } Pos;
typedef struct { Line *l; int n; Pos cur, anc; int sel; } Snap;
typedef struct { char *b; size_t len, cap; } Abuf;

static struct {
    Line *l; int n, cap;
    Pos cur, anc; int sel;
    int want, want_keep;
    int top, topsub, rows, cols; /* first visible logical line + wrapped row within it */
    char *file; int dirty, crlf, final_nl;
    char msg[512]; time_t msgt;
    char *clip; size_t cliplen; int cliplines;
    Snap *undo; int nundo; Snap *redo; int nredo;
    int lastkind, prevkind;
    time_t lastedit;
    char *lastq;
    int quit_warn;
    struct termios orig; int raw;
} E;

static volatile sig_atomic_t g_resize, g_term;
static int hl_valid; /* syntax highlight cache (see below) */
static void hl_invalidate(int r);

/* mouse + paste state filled in by read_key() */
static int mouse_b, mouse_x, mouse_y, mouse_release;
static char *paste_buf; static size_t paste_len;

/* ---------- small utils ---------- */

static void *xrealloc(void *p, size_t n) {
    p = realloc(p, n ? n : 1);
    if (!p) { ssize_t w = write(STDERR_FILENO, "out of memory\n", 14); (void)w; _exit(1); }
    return p;
}

static void ab_add(Abuf *a, const char *s, size_t n) {
    if (a->len + n + 1 > a->cap) {
        a->cap = (a->len + n + 1) * 2;
        a->b = xrealloc(a->b, a->cap);
    }
    memcpy(a->b + a->len, s, n);
    a->len += n;
}
static void ab_str(Abuf *a, const char *s) { ab_add(a, s, strlen(s)); }
static void ab_fmt(Abuf *a, const char *fmt, ...) {
    char t[256]; va_list ap; va_start(ap, fmt);
    int n = vsnprintf(t, sizeof t, fmt, ap); va_end(ap);
    if (n > 0) ab_add(a, t, n < (int)sizeof t ? n : (int)sizeof t - 1);
}

static void set_msg(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    vsnprintf(E.msg, sizeof E.msg, fmt, ap);
    va_end(ap);
    E.msgt = time(NULL);
}

/* ---------- utf8 ---------- */

/* Decode one char. Returns bytes consumed; *cp = -1 on invalid input. */
static int u8dec(const char *s, int len, int *cp) {
    unsigned char c = s[0];
    int n, v;
    if (c < 0x80) { *cp = c; return 1; }
    if (c >= 0xC2 && c < 0xE0) { n = 2; v = c & 0x1F; }
    else if (c >= 0xE0 && c < 0xF0) { n = 3; v = c & 0x0F; }
    else if (c >= 0xF0 && c < 0xF5) { n = 4; v = c & 0x07; }
    else { *cp = -1; return 1; }
    if (len < n) { *cp = -1; return 1; }
    for (int i = 1; i < n; i++) {
        if (((unsigned char)s[i] & 0xC0) != 0x80) { *cp = -1; return 1; }
        v = (v << 6) | ((unsigned char)s[i] & 0x3F);
    }
    *cp = v;
    return n;
}

static int u8enc(int cp, char *o) {
    if (cp < 0x80) { o[0] = cp; return 1; }
    if (cp < 0x800) { o[0] = 0xC0 | (cp >> 6); o[1] = 0x80 | (cp & 0x3F); return 2; }
    if (cp < 0x10000) {
        o[0] = 0xE0 | (cp >> 12); o[1] = 0x80 | ((cp >> 6) & 0x3F);
        o[2] = 0x80 | (cp & 0x3F); return 3;
    }
    o[0] = 0xF0 | (cp >> 18); o[1] = 0x80 | ((cp >> 12) & 0x3F);
    o[2] = 0x80 | ((cp >> 6) & 0x3F); o[3] = 0x80 | (cp & 0x3F);
    return 4;
}

static int cpwidth(int cp) {
    if (cp < 0x300) return 1;
    if ((cp >= 0x300 && cp <= 0x36F) || (cp >= 0x200B && cp <= 0x200F) ||
        (cp >= 0xFE00 && cp <= 0xFE0F) || cp == 0xFEFF) return 0;
    if ((cp >= 0x1100 && cp <= 0x115F) || (cp >= 0x2E80 && cp <= 0xA4CF) ||
        (cp >= 0xAC00 && cp <= 0xD7A3) || (cp >= 0xF900 && cp <= 0xFAFF) ||
        (cp >= 0xFE30 && cp <= 0xFE6F) || (cp >= 0xFF00 && cp <= 0xFF60) ||
        (cp >= 0xFFE0 && cp <= 0xFFE6) || (cp >= 0x1F300 && cp <= 0x1F64F) ||
        (cp >= 0x1F900 && cp <= 0x1F9FF) || (cp >= 0x20000 && cp <= 0x3FFFD)) return 2;
    return 1;
}

static int prev_c(const Line *L, int c) {
    if (c <= 0) return 0;
    c--;
    while (c > 0 && ((unsigned char)L->s[c] & 0xC0) == 0x80) c--;
    return c;
}
static int next_c(const Line *L, int c) {
    if (c >= L->len) return L->len;
    int cp; int n = u8dec(L->s + c, L->len - c, &cp);
    return c + n;
}

static int col_of(const Line *L, int c) {
    int vc = 0;
    for (int i = 0; i < c && i < L->len;) {
        int cp; int n = u8dec(L->s + i, L->len - i, &cp);
        vc += cp == '\t' ? TABW - vc % TABW : (cp < 0 ? 1 : cpwidth(cp));
        i += n;
    }
    return vc;
}

/* ---------- buffer primitives ---------- */

static void line_init(Line *L) { L->s = NULL; L->len = L->cap = 0; }
static void line_free(Line *L) { free(L->s); line_init(L); }
static void line_reserve(Line *L, int need) {
    if (need > L->cap) {
        int nc = L->cap ? L->cap * 2 : 16;
        while (nc < need) nc *= 2;
        L->s = xrealloc(L->s, nc);
        L->cap = nc;
    }
}
static void line_insert(Line *L, int at, const char *t, int n) {
    line_reserve(L, L->len + n);
    memmove(L->s + at + n, L->s + at, L->len - at);
    memcpy(L->s + at, t, n);
    L->len += n;
}
static void line_del(Line *L, int at, int n) {
    memmove(L->s + at, L->s + at + n, L->len - at - n);
    L->len -= n;
}

static void buf_insert_line(int at) {
    if (E.n + 1 > E.cap) {
        E.cap = E.cap ? E.cap * 2 : 64;
        E.l = xrealloc(E.l, E.cap * sizeof(Line));
    }
    memmove(E.l + at + 1, E.l + at, (E.n - at) * sizeof(Line));
    line_init(&E.l[at]);
    E.n++;
}
static void buf_remove_lines(int at, int cnt) {
    for (int i = 0; i < cnt; i++) line_free(&E.l[at + i]);
    memmove(E.l + at, E.l + at + cnt, (E.n - at - cnt) * sizeof(Line));
    E.n -= cnt;
}

static int pos_cmp(Pos a, Pos b) { return a.r != b.r ? a.r - b.r : a.c - b.c; }

/* Insert text (may contain \n) at p. Returns the position after the text. */
static Pos text_insert(Pos p, const char *t, size_t n) {
    Line *L = &E.l[p.r];
    int tail_len = L->len - p.c;
    char *tail = xrealloc(NULL, tail_len + 1);
    memcpy(tail, L->s + p.c, tail_len);
    L->len = p.c;
    size_t i = 0;
    int row = p.r;
    for (;;) {
        size_t j = i;
        while (j < n && t[j] != '\n') j++;
        line_insert(&E.l[row], E.l[row].len, t + i, (int)(j - i));
        if (j >= n) break;
        row++;
        buf_insert_line(row);
        i = j + 1;
    }
    Pos end = { row, E.l[row].len };
    line_insert(&E.l[row], E.l[row].len, tail, tail_len);
    free(tail);
    return end;
}

static void text_delete(Pos a, Pos b) {
    if (a.r == b.r) {
        line_del(&E.l[a.r], a.c, b.c - a.c);
        return;
    }
    Line *A = &E.l[a.r], *B = &E.l[b.r];
    A->len = a.c;
    line_insert(A, A->len, B->s + b.c, B->len - b.c);
    buf_remove_lines(a.r + 1, b.r - a.r);
}

static char *text_get(Pos a, Pos b, size_t *outlen) {
    size_t total = 0;
    for (int r = a.r; r <= b.r; r++) total += E.l[r].len + 1;
    char *o = xrealloc(NULL, total + 1), *w = o;
    for (int r = a.r; r <= b.r; r++) {
        int s = r == a.r ? a.c : 0, e = r == b.r ? b.c : E.l[r].len;
        memcpy(w, E.l[r].s + s, e - s); w += e - s;
        if (r != b.r) *w++ = '\n';
    }
    *w = 0;
    *outlen = w - o;
    return o;
}

/* ---------- selection ---------- */

static int has_sel(void) { return E.sel && pos_cmp(E.cur, E.anc) != 0; }
static void sel_range(Pos *a, Pos *b) {
    if (pos_cmp(E.cur, E.anc) < 0) { *a = E.cur; *b = E.anc; }
    else { *a = E.anc; *b = E.cur; }
}

/* ---------- undo ---------- */

static void snap_take(Snap *s) {
    s->n = E.n;
    s->l = xrealloc(NULL, E.n * sizeof(Line));
    for (int i = 0; i < E.n; i++) {
        s->l[i].len = E.l[i].len;
        s->l[i].cap = E.l[i].len;
        s->l[i].s = xrealloc(NULL, E.l[i].len);
        memcpy(s->l[i].s, E.l[i].s, E.l[i].len);
    }
    s->cur = E.cur; s->anc = E.anc; s->sel = E.sel;
}
static void snap_free(Snap *s) {
    for (int i = 0; i < s->n; i++) free(s->l[i].s);
    free(s->l); s->l = NULL; s->n = 0;
}
static void snap_restore(Snap *s) {
    for (int i = 0; i < E.n; i++) line_free(&E.l[i]);
    free(E.l);
    E.l = s->l; E.n = E.cap = s->n;
    s->l = NULL; s->n = 0;
    E.cur = s->cur; E.anc = s->anc; E.sel = s->sel;
    hl_valid = 0;
}
static void stack_push(Snap **st, int *n) {
    if (*n >= MAX_UNDO) {
        snap_free(&(*st)[0]);
        memmove(*st, *st + 1, (*n - 1) * sizeof(Snap));
        (*n)--;
    }
    *st = xrealloc(*st, (*n + 1) * sizeof(Snap));
    snap_take(&(*st)[*n]);
    (*n)++;
}
static void stack_clear(Snap **st, int *n) {
    for (int i = 0; i < *n; i++) snap_free(&(*st)[i]);
    *n = 0;
}

/* Call before every edit. kind != 0 coalesces with the previous edit of the same kind. */
static void undo_begin(int kind) {
    if (!(kind && kind == E.prevkind && E.nundo > 0)) stack_push(&E.undo, &E.nundo);
    E.lastkind = kind;
    stack_clear(&E.redo, &E.nredo);
    E.dirty = 1;
    E.lastedit = time(NULL);
    E.quit_warn = 0;
    hl_invalidate((E.sel && E.anc.r < E.cur.r ? E.anc.r : E.cur.r) - 1);
}

static void do_undo(void) {
    if (!E.nundo) { set_msg("Nothing to undo"); return; }
    stack_push(&E.redo, &E.nredo);
    Snap *s = &E.undo[--E.nundo];
    snap_restore(s);
    E.dirty = 1;
    E.lastedit = time(NULL);
}
static void do_redo(void) {
    if (!E.nredo) { set_msg("Nothing to redo"); return; }
    stack_push(&E.undo, &E.nundo);
    Snap *s = &E.redo[--E.nredo];
    snap_restore(s);
    E.dirty = 1;
    E.lastedit = time(NULL);
}

/* ---------- terminal ---------- */

static void term_write(const char *s, size_t n) {
    while (n) {
        ssize_t w = write(STDOUT_FILENO, s, n);
        if (w < 0) { if (errno == EINTR || errno == EAGAIN) continue; return; }
        s += w; n -= w;
    }
}

static void term_restore(void) {
    if (!E.raw) return;
    E.raw = 0;
    const char *s = "\x1b[?1006l\x1b[?1002l\x1b[?1000l\x1b[?2004l\x1b[m\x1b[?25h\x1b[?1049l";
    term_write(s, strlen(s));
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &E.orig);
}

static void term_raw(void) {
    tcgetattr(STDIN_FILENO, &E.orig);
    struct termios t = E.orig;
    t.c_iflag &= ~(BRKINT | ICRNL | INPCK | ISTRIP | IXON | INLCR | IGNCR);
    t.c_oflag &= ~(OPOST);
    t.c_cflag |= CS8;
    t.c_lflag &= ~(ECHO | ICANON | IEXTEN | ISIG);
    t.c_cc[VMIN] = 0;
    t.c_cc[VTIME] = 1;
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &t);
    E.raw = 1;
    const char *s = "\x1b[?1049h\x1b[?2004h\x1b[?1000h\x1b[?1002h\x1b[?1006h";
    term_write(s, strlen(s));
}

static void on_signal(int sig) {
    if (sig == SIGWINCH) g_resize = 1;
    else g_term = sig;
}

static void get_size(void) {
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == -1 || ws.ws_col == 0) {
        E.rows = 24; E.cols = 80;
    } else {
        E.rows = ws.ws_row; E.cols = ws.ws_col;
    }
    if (E.rows < 4) E.rows = 4;
    if (E.cols < 20) E.cols = 20;
}

/* ---------- input ---------- */

static int rd(void) {
    unsigned char c;
    for (;;) {
        ssize_t n = read(STDIN_FILENO, &c, 1);
        if (n == 1) return c;
        if (n < 0 && errno != EINTR && errno != EAGAIN) return -2;
        return -1; /* timeout */
    }
}

static void read_paste(void) {
    free(paste_buf);
    paste_buf = NULL; paste_len = 0;
    size_t cap = 0; int idle = 0;
    static const char end[] = "\x1b[201~";
    while (idle < 30) {
        int c = rd();
        if (c == -2) break;
        if (c == -1) { idle++; continue; }
        idle = 0;
        if (paste_len + 1 >= cap) { cap = cap ? cap * 2 : 4096; paste_buf = xrealloc(paste_buf, cap); }
        paste_buf[paste_len++] = c;
        if (paste_len >= 6 && memcmp(paste_buf + paste_len - 6, end, 6) == 0) {
            paste_len -= 6;
            break;
        }
    }
    if (!paste_buf) paste_buf = xrealloc(NULL, 1);
    /* normalise line endings */
    size_t w = 0;
    for (size_t i = 0; i < paste_len; i++) {
        if (paste_buf[i] == '\r') {
            paste_buf[w++] = '\n';
            if (i + 1 < paste_len && paste_buf[i + 1] == '\n') i++;
        } else paste_buf[w++] = paste_buf[i];
    }
    paste_len = w;
}

static int read_csi(void) {
    int params[8] = {0}, np = 0, have = 0, priv = 0;
    int c;
    for (;;) {
        c = rd();
        if (c < 0) return KEY_ESC;
        if (c == '<' || c == '?') { priv = c; continue; }
        if (c >= '0' && c <= '9') {
            if (np < 8) params[np] = params[np] * 10 + (c - '0');
            have = 1;
            continue;
        }
        if (c == ';') { if (np < 7) np++; continue; }
        break;
    }
    int nparams = have ? np + 1 : 0;
    int mod = 0;
    if (nparams >= 2 && params[1] > 1) {
        int m = params[1] - 1;
        if (m & 1) mod |= M_SHIFT;
        if (m & 2) mod |= M_ALT;
        if (m & 8) mod |= M_ALT; /* some terminals report Alt as Meta */
        if (m & 4) mod |= M_CTRL;
    }
    if (priv == '<' && (c == 'M' || c == 'm') && nparams >= 3) {
        mouse_b = params[0]; mouse_x = params[1]; mouse_y = params[2];
        mouse_release = c == 'm';
        return K_MOUSE;
    }
    switch (c) {
    case 'A': return K_UP | mod;
    case 'B': return K_DOWN | mod;
    case 'C': return K_RIGHT | mod;
    case 'D': return K_LEFT | mod;
    case 'H': return K_HOME | mod;
    case 'F': return K_END | mod;
    case 'Z': return K_BTAB;
    case 'P': return K_F1 | mod;
    case 'Q': return K_F2 | mod;
    case 'R': return K_F3 | mod;
    case '~':
        switch (params[0]) {
        case 1: case 7: return K_HOME | mod;
        case 2: return K_INS | mod;
        case 3: return K_DEL | mod;
        case 4: case 8: return K_END | mod;
        case 5: return K_PGUP | mod;
        case 6: return K_PGDN | mod;
        case 11: return K_F1 | mod;
        case 12: return K_F2 | mod;
        case 13: return K_F3 | mod;
        case 200: read_paste(); return K_PASTE;
        }
    }
    return K_NONE;
}

static int autosave_tick(void);

static int read_key(void) {
    for (;;) {
        if (g_term) { term_restore(); _exit(128 + g_term); }
        if (g_resize) { g_resize = 0; get_size(); return K_RESIZE; }
        int c = rd();
        if (c == -2) { term_restore(); _exit(1); }
        if (c == -1) { if (autosave_tick()) return K_RESIZE; continue; }
        if (c == KEY_ESC) {
            int c2 = rd();
            if (c2 < 0) return KEY_ESC;
            if (c2 == '[') return read_csi();
            if (c2 == 'O') {
                int c3 = rd();
                switch (c3) {
                case 'A': return K_UP; case 'B': return K_DOWN;
                case 'C': return K_RIGHT; case 'D': return K_LEFT;
                case 'H': return K_HOME; case 'F': return K_END;
                case 'P': return K_F1; case 'Q': return K_F2; case 'R': return K_F3;
                }
                return K_NONE;
            }
            if (c2 == KEY_ESC) { /* ESC ESC [ A style Alt+Arrow */
                int c3 = rd();
                if (c3 == '[') { int k = read_csi(); return k >= K_SPECIAL ? (k | M_ALT) : KEY_ESC; }
                if (c3 == 'O') {
                    switch (rd()) {
                    case 'A': return K_UP | M_ALT; case 'B': return K_DOWN | M_ALT;
                    case 'C': return K_RIGHT | M_ALT; case 'D': return K_LEFT | M_ALT;
                    }
                }
                return KEY_ESC;
            }
            if (c2 == KEY_BS || c2 == 8) return KEY_BS | M_ALT; /* Alt+Backspace */
            return c2 | M_ALT;
        }
        if (c >= 0x80) {
            char b[4]; b[0] = c;
            int need = c >= 0xF0 ? 3 : c >= 0xE0 ? 2 : c >= 0xC0 ? 1 : 0, got = 0;
            while (got < need) {
                int x = rd();
                if (x < 0) break;
                b[1 + got++] = x;
            }
            int cp; u8dec(b, got + 1, &cp);
            return cp < 0 ? K_NONE : cp;
        }
        return c;
    }
}

/* ---------- file io ---------- */

static void buf_reset(void) {
    for (int i = 0; i < E.n; i++) line_free(&E.l[i]);
    E.n = 0;
    buf_insert_line(0);
}

static int load_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) return errno == ENOENT ? 0 : -1;
    struct stat st;
    if (fstat(fileno(f), &st) == 0 && S_ISDIR(st.st_mode)) { fclose(f); errno = EISDIR; return -1; }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz < 0) sz = 0;
    char *data = xrealloc(NULL, sz + 1);
    size_t got = fread(data, 1, sz, f);
    fclose(f);
    data[got] = 0;

    buf_reset();
    int crlf = 0, lf = 0;
    size_t i = 0;
    while (i < got) {
        char *nl = memchr(data + i, '\n', got - i);
        size_t end = nl ? (size_t)(nl - data) : got;
        size_t le = end;
        if (nl) { if (le > i && data[le - 1] == '\r') { le--; crlf++; } else lf++; }
        Line *L = &E.l[E.n - 1];
        line_insert(L, 0, data + i, (int)(le - i));
        if (!nl) { i = got; break; }
        buf_insert_line(E.n);
        i = end + 1;
    }
    E.final_nl = got == 0 || data[got - 1] == '\n';
    if (got > 0 && data[got - 1] == '\n') {
        /* last (empty) line comes from the trailing newline */
        if (E.n > 1) buf_remove_lines(E.n - 1, 1);
    }
    E.crlf = crlf > lf;
    free(data);
    return 1;
}

static int save_file(void) {
    FILE *f = fopen(E.file, "wb");
    if (!f) return -1;
    size_t bytes = 0;
    int empty = E.n == 1 && E.l[0].len == 0;
    for (int i = 0; i < E.n && !empty; i++) {
        fwrite(E.l[i].s, 1, E.l[i].len, f);
        bytes += E.l[i].len;
        if (i < E.n - 1 || E.final_nl) {
            if (E.crlf) { fputc('\r', f); bytes++; }
            fputc('\n', f); bytes++;
        }
    }
    int err = ferror(f);
    if (fclose(f) != 0) err = 1;
    if (err) return -1;
    set_msg("Saved %s (%d lines, %zu bytes)", E.file, E.n, bytes);
    E.dirty = 0;
    return 0;
}

/* ---------- syntax highlighting ---------- */

enum { C_NONE, C_KEYWORD, C_TYPE, C_STRING, C_NUMBER, C_COMMENT, C_FUNC, C_TAG, C_ATTR,
       C_HEAD, C_BOLD, C_ITALIC, C_CODE, C_LINK, C_URL, C_MARK, C_QUOTE, C_HR, C_DONE, C_SEL };

/* The markdown colours follow the notes editor on the download site: bold in pink-red,
 * headings bold in the neon green accent, green underlined links, dim struck-through done items. */
static const char *const class_sgr[] = {
    [C_NONE] = "", [C_KEYWORD] = "38;5;176", [C_TYPE] = "38;5;80", [C_STRING] = "38;5;114",
    [C_NUMBER] = "38;5;215", [C_COMMENT] = "38;5;243", [C_FUNC] = "38;5;111",
    [C_TAG] = "38;5;75", [C_ATTR] = "38;5;180",
    [C_HEAD] = "1;38;5;83", [C_BOLD] = "1;38;5;217", [C_ITALIC] = "3;38;5;253",
    [C_CODE] = "38;5;150;48;5;236", [C_LINK] = "4;38;5;72", [C_URL] = "38;5;243",
    [C_MARK] = "38;5;83", [C_QUOTE] = "3;38;5;108", [C_HR] = "38;5;243", [C_DONE] = "2;9",
    [C_SEL] = "48;5;24;38;5;255",
};

enum { L_NONE, L_MD, L_C, L_JS, L_PY, L_JSON, L_HTML, L_CSS, L_SH };
enum { ST_NONE, ST_BLOCK, ST_TQ1, ST_TQ2, ST_BT, ST_FENCE, ST_HCOMMENT, ST_HTAG, ST_HTAG_SCRIPT,
       ST_HTAG_STYLE, ST_SCRIPT, ST_STYLE };

typedef struct {
    const char *lc, *bo, *bc, *quotes;
    const char *const *kw, *const *ty;
    int triple, backtick, preproc, json, shell, css, func;
} Lang;

static const char *const kw_c[] = { "if", "else", "for", "while", "do", "switch", "case", "default", "break",
    "continue", "return", "goto", "sizeof", "typedef", "struct", "union", "enum", "static", "extern", "const",
    "volatile", "inline", "register", "NULL", "true", "false", "class", "public", "private", "protected",
    "namespace", "template", "typename", "new", "delete", "using", "nullptr", "auto", "this", "virtual",
    "try", "catch", "throw", NULL };
static const char *const ty_c[] = { "int", "char", "short", "long", "unsigned", "signed", "float", "double",
    "void", "size_t", "ssize_t", "bool", "uint8_t", "uint16_t", "uint32_t", "uint64_t", "int8_t", "int16_t",
    "int32_t", "int64_t", "FILE", NULL };
static const char *const kw_js[] = { "var", "let", "const", "function", "return", "if", "else", "for", "while",
    "do", "switch", "case", "default", "break", "continue", "new", "delete", "typeof", "instanceof", "in", "of",
    "class", "extends", "super", "import", "export", "from", "as", "async", "await", "yield", "try", "catch",
    "finally", "throw", "this", "null", "undefined", "true", "false", "void", "static", "get", "set",
    "interface", "type", "enum", "implements", "public", "private", "readonly", NULL };
static const char *const kw_py[] = { "def", "class", "return", "if", "elif", "else", "for", "while", "in", "not",
    "and", "or", "is", "import", "from", "as", "with", "try", "except", "finally", "raise", "pass", "break",
    "continue", "lambda", "yield", "global", "nonlocal", "assert", "del", "None", "True", "False", "async",
    "await", NULL };
static const char *const ty_py[] = { "print", "len", "range", "int", "str", "float", "list", "dict", "set",
    "tuple", "bool", "open", "isinstance", "self", "super", "enumerate", "zip", "map", "sorted", NULL };
static const char *const kw_sh[] = { "if", "then", "else", "elif", "fi", "for", "while", "until", "do", "done",
    "case", "esac", "function", "in", "return", "exit", "export", "local", "readonly", "echo", "cd", "source",
    "set", "unset", "shift", "true", "false", NULL };
static const char *const kw_json[] = { "true", "false", "null", NULL };

static const Lang lang_c = { "//", "/*", "*/", "\"'", kw_c, ty_c, 0, 0, 1, 0, 0, 0, 1 };
static const Lang lang_js = { "//", "/*", "*/", "\"'", kw_js, NULL, 0, 1, 0, 0, 0, 0, 1 };
static const Lang lang_py = { "#", NULL, NULL, "\"'", kw_py, ty_py, 1, 0, 0, 0, 0, 0, 1 };
static const Lang lang_json = { NULL, NULL, NULL, "\"", kw_json, NULL, 0, 0, 0, 1, 0, 0, 0 };
static const Lang lang_sh = { "#", NULL, NULL, "\"'", kw_sh, NULL, 0, 0, 0, 0, 1, 0, 0 };
static const Lang lang_css = { NULL, "/*", "*/", "\"'", NULL, NULL, 0, 0, 0, 0, 0, 1, 0 };

static int in_list(const char *const *l, const char *s, int n) {
    for (; l && *l; l++) if ((int)strlen(*l) == n && memcmp(*l, s, n) == 0) return 1;
    return 0;
}
static int id_start(int c) { return isalpha(c) || c == '_' || c == '$' || c >= 0x80; }
static int id_char(int c) { return isalnum(c) || c == '_' || c == '$' || c >= 0x80; }
static void paint(uint8_t *cls, int a, int b, int c) { for (int i = a; i < b; i++) cls[i] = c; }
static const char *find_str(const char *s, int n, int from, const char *t) {
    int tl = (int)strlen(t);
    for (int i = from; i + tl <= n; i++) if (memcmp(s + i, t, tl) == 0) return s + i;
    return NULL;
}

/* Scan one line of a C-like language. Returns the state at the end of the line. */
static int scan_code(const Lang *g, const char *s, int n, int st, uint8_t *cls) {
    int i = 0;
    paint(cls, 0, n, C_NONE);
    for (;;) {
        if (st == ST_BLOCK) {
            const char *e = find_str(s, n, i, g->bc);
            int end = e ? (int)(e - s) + (int)strlen(g->bc) : n;
            paint(cls, i, end, C_COMMENT); i = end;
            if (e) st = ST_NONE;
            if (!e) return st;
        } else if (st == ST_TQ1 || st == ST_TQ2) {
            const char *e = find_str(s, n, i, st == ST_TQ1 ? "'''" : "\"\"\"");
            int end = e ? (int)(e - s) + 3 : n;
            paint(cls, i, end, C_STRING); i = end;
            if (e) st = ST_NONE; else return st;
        } else if (st == ST_BT) {
            int j = i;
            while (j < n && s[j] != '`') j += s[j] == '\\' ? 2 : 1;
            if (j > n) j = n;
            int end = j < n ? j + 1 : n;
            paint(cls, i, end, C_STRING); i = end;
            if (j < n) st = ST_NONE; else return st;
        }
        break;
    }
    int first = 1; /* nothing but spaces seen yet */
    while (i < n) {
        unsigned char c = s[i];
        if (c == ' ' || c == '\t') { i++; continue; }
        int was_first = first; first = 0;
        if (g->lc && strncmp(s + i, g->lc, strlen(g->lc)) == 0 &&
            (!g->shell || i == 0 || s[i - 1] == ' ' || s[i - 1] == '\t' || was_first)) {
            paint(cls, i, n, C_COMMENT); return st;
        }
        if (g->bo && strncmp(s + i, g->bo, strlen(g->bo)) == 0) {
            const char *e = find_str(s, n, i + (int)strlen(g->bo), g->bc);
            int end = e ? (int)(e - s) + (int)strlen(g->bc) : n;
            paint(cls, i, end, C_COMMENT); i = end;
            if (!e) return ST_BLOCK;
            continue;
        }
        if (g->preproc && c == '#' && was_first) {
            int j = i + 1;
            while (j < n && (s[j] == ' ' || s[j] == '\t')) j++;
            int k = j;
            while (k < n && isalpha((unsigned char)s[k])) k++;
            paint(cls, i, k, C_KEYWORD);
            int isinc = k - j == 7 && memcmp(s + j, "include", 7) == 0;
            i = k;
            while (isinc && i < n && s[i] == ' ') i++;
            if (isinc && i < n && s[i] == '<') {
                int e = i; while (e < n && s[e] != '>') e++;
                if (e < n) e++;
                paint(cls, i, e, C_STRING); i = e;
            }
            continue;
        }
        if (g->quotes && strchr(g->quotes, c)) {
            if (g->triple && i + 2 < n && s[i + 1] == c && s[i + 2] == c) {
                st = c == '\'' ? ST_TQ1 : ST_TQ2;
                const char *e = find_str(s, n, i + 3, c == '\'' ? "'''" : "\"\"\"");
                int end = e ? (int)(e - s) + 3 : n;
                paint(cls, i, end, C_STRING); i = end;
                if (e) st = ST_NONE; else return st;
                continue;
            }
            int j = i + 1;
            while (j < n && s[j] != c) j += s[j] == '\\' ? 2 : 1;
            if (j > n) j = n;
            int end = j < n ? j + 1 : n, kind = C_STRING;
            if (g->json) {
                int k = end;
                while (k < n && (s[k] == ' ' || s[k] == '\t')) k++;
                if (k < n && s[k] == ':') kind = C_ATTR;
            }
            paint(cls, i, end, kind); i = end;
            continue;
        }
        if (g->backtick && c == '`') {
            int j = i + 1;
            while (j < n && s[j] != '`') j += s[j] == '\\' ? 2 : 1;
            if (j > n) j = n;
            int end = j < n ? j + 1 : n;
            paint(cls, i, end, C_STRING); i = end;
            if (j >= n) return ST_BT;
            continue;
        }
        if (g->shell && c == '$') {
            int j = i + 1;
            if (j < n && s[j] == '{') { while (j < n && s[j] != '}') j++; if (j < n) j++; }
            else if (j < n && (id_start(s[j]) || isdigit((unsigned char)s[j]) || strchr("?@*#!$", s[j]))) {
                j++; while (j < n && id_char(s[j])) j++;
            }
            paint(cls, i, j, C_ATTR); i = j > i ? j : i + 1;
            continue;
        }
        if (g->css && c == '#') {
            int j = i + 1;
            while (j < n && isxdigit((unsigned char)s[j])) j++;
            if (j - i >= 4) { paint(cls, i, j, C_NUMBER); i = j; continue; }
        }
        if ((c == '@' && (g->css || (g->triple && was_first)))) {
            int j = i + 1;
            while (j < n && (id_char(s[j]) || s[j] == '-' || s[j] == '.')) j++;
            paint(cls, i, j, g->css ? C_KEYWORD : C_FUNC); i = j;
            continue;
        }
        if (isdigit(c) || (c == '.' && i + 1 < n && isdigit((unsigned char)s[i + 1]))) {
            int j = i + 1;
            while (j < n && (isalnum((unsigned char)s[j]) || s[j] == '.' || s[j] == '_' || (g->css && s[j] == '%'))) j++;
            paint(cls, i, j, C_NUMBER); i = j;
            continue;
        }
        if (id_start(c) || (g->css && c == '-' && i + 1 < n && isalpha((unsigned char)s[i + 1]))) {
            int j = i + 1;
            while (j < n && (id_char(s[j]) || (g->css && s[j] == '-'))) j++;
            int k = j;
            while (k < n && s[k] == ' ') k++;
            if (in_list(g->kw, s + i, j - i)) paint(cls, i, j, C_KEYWORD);
            else if (in_list(g->ty, s + i, j - i)) paint(cls, i, j, C_TYPE);
            else if (g->func && k < n && s[k] == '(') paint(cls, i, j, C_FUNC);
            i = j;
            continue;
        }
        i++;
    }
    return st;
}

static int scan_html(const char *s, int n, int st, uint8_t *cls) {
    int i = 0;
    paint(cls, 0, n, C_NONE);
    while (i < n) {
        if (st == ST_HCOMMENT) {
            const char *e = find_str(s, n, i, "-->");
            int end = e ? (int)(e - s) + 3 : n;
            paint(cls, i, end, C_COMMENT); i = end;
            if (e) st = ST_NONE;
        } else if (st == ST_SCRIPT || st == ST_STYLE) {
            const char *close = st == ST_SCRIPT ? "</script" : "</style";
            int cl = (int)strlen(close), j = i;
            while (j + cl <= n && strncasecmp(s + j, close, cl) != 0) j++;
            if (j + cl > n) j = n;
            scan_code(st == ST_SCRIPT ? &lang_js : &lang_css, s + i, j - i, ST_NONE, cls + i);
            i = j;
            if (j < n) st = ST_NONE;
        } else if (st == ST_HTAG || st == ST_HTAG_SCRIPT || st == ST_HTAG_STYLE) {
            unsigned char c = s[i];
            if (c == '>') {
                cls[i++] = C_TAG;
                st = st == ST_HTAG_SCRIPT ? ST_SCRIPT : st == ST_HTAG_STYLE ? ST_STYLE : ST_NONE;
            } else if (c == '"' || c == '\'') {
                int j = i + 1;
                while (j < n && s[j] != c) j++;
                int end = j < n ? j + 1 : n;
                paint(cls, i, end, C_STRING); i = end;
            } else if (id_char(c) || c == '-' || c == ':') {
                int j = i;
                while (j < n && (id_char(s[j]) || s[j] == '-' || s[j] == ':')) j++;
                paint(cls, i, j, C_ATTR); i = j;
            } else { if (c == '/' || c == '=') cls[i] = C_TAG; i++; }
        } else if (s[i] == '<') {
            if (strncmp(s + i, "<!--", 4) == 0) { st = ST_HCOMMENT; paint(cls, i, i + 4, C_COMMENT); i += 4; continue; }
            int j = i + 1, closing = 0;
            if (j < n && s[j] == '/') { closing = 1; j++; }
            if (j < n && s[j] == '!') j++;
            if (j < n && isalpha((unsigned char)s[j])) {
                int k = j;
                while (k < n && (isalnum((unsigned char)s[k]) || s[k] == '-' || s[k] == ':')) k++;
                paint(cls, i, k, C_TAG);
                st = ST_HTAG;
                if (!closing && k - j == 6 && strncasecmp(s + j, "script", 6) == 0) st = ST_HTAG_SCRIPT;
                if (!closing && k - j == 5 && strncasecmp(s + j, "style", 5) == 0) st = ST_HTAG_STYLE;
                i = k;
            } else if (j > i + 1 && j <= n) { /* <!DOCTYPE ... */
                paint(cls, i, j, C_TAG); i = j; st = ST_HTAG;
            } else i++;
        } else if (s[i] == '&') {
            int j = i + 1;
            while (j < n && isalnum((unsigned char)s[j])) j++;
            if (j < n && s[j] == ';') { paint(cls, i, j + 1, C_NUMBER); i = j + 1; } else i++;
        } else i++;
    }
    return st;
}

/* Inline markdown over s[a,b): bold, italic, code, links, bare URLs. */
static void md_inline(const char *s, int a, int b, uint8_t *cls) {
    for (int i = a; i < b;) {
        char c = s[i];
        if (c == '\\' && i + 1 < b) { i += 2; continue; }
        if (c == '`') {
            const char *e = find_str(s, b, i + 1, "`");
            if (e) { int end = (int)(e - s) + 1; paint(cls, i, end, C_CODE); i = end; continue; }
        } else if ((c == '*' || c == '_') && i + 1 < b && s[i + 1] == c) {
            char t[3] = { c, c, 0 };
            const char *e = find_str(s, b, i + 2, t);
            if (e && (int)(e - s) > i + 2 && (c == '*' || i == a || !id_char(s[i - 1]))) {
                int end = (int)(e - s) + 2; paint(cls, i, end, C_BOLD); i = end; continue;
            }
        } else if (c == '*' && i + 1 < b && s[i + 1] != ' ') {
            const char *e = find_str(s, b, i + 1, "*");
            if (e && (int)(e - s) > i + 1) { int end = (int)(e - s) + 1; paint(cls, i, end, C_ITALIC); i = end; continue; }
        } else if (c == '[' || (c == '!' && i + 1 < b && s[i + 1] == '[')) {
            int o = c == '!' ? i + 1 : i;
            const char *cb = find_str(s, b, o + 1, "](");
            if (cb) {
                int mid = (int)(cb - s);
                const char *cp = find_str(s, b, mid + 2, ")");
                if (cp) {
                    int end = (int)(cp - s) + 1;
                    paint(cls, i, mid + 1, C_LINK);
                    paint(cls, mid + 1, end, C_URL);
                    i = end; continue;
                }
            }
        } else if (c == 'h' && (strncmp(s + i, "http://", i + 7 <= b ? 7 : 0) == 0 || strncmp(s + i, "https://", i + 8 <= b ? 8 : 0) == 0)
                   && i + 7 <= b) {
            int j = i;
            while (j < b && s[j] != ' ' && s[j] != '\t' && s[j] != ')' && s[j] != '>') j++;
            paint(cls, i, j, C_LINK); i = j; continue;
        }
        i++;
    }
}

static int scan_md(const char *s, int n, int st, uint8_t *cls) {
    paint(cls, 0, n, C_NONE);
    int i = 0;
    while (i < n && i < 3 && s[i] == ' ') i++;
    int fence = n - i >= 3 && (memcmp(s + i, "```", 3) == 0 || memcmp(s + i, "~~~", 3) == 0);
    if (st == ST_FENCE) {
        paint(cls, 0, n, C_CODE);
        return fence ? ST_NONE : ST_FENCE;
    }
    if (fence) { paint(cls, 0, n, C_CODE); return ST_FENCE; }
    int j = 0;
    while (j < n && (s[j] == ' ' || s[j] == '\t')) j++;
    /* horizontal rule */
    if (j < n && (s[j] == '-' || s[j] == '*' || s[j] == '_')) {
        int k = j, cnt = 0;
        while (k < n && s[k] == s[j]) { k++; cnt++; }
        while (k < n && s[k] == ' ') k++;
        if (cnt >= 3 && k == n) { paint(cls, 0, n, C_HR); return st; }
    }
    int base = C_NONE, body = j;
    if (j < n && s[j] == '#') {
        int k = j; while (k < n && s[k] == '#') k++;
        if (k - j <= 6 && (k == n || s[k] == ' ')) { base = C_HEAD; paint(cls, 0, n, C_HEAD); }
    } else if (j < n && s[j] == '>') {
        paint(cls, j, j + 1, C_MARK);
        base = C_QUOTE; body = j + 1;
        paint(cls, body, n, C_QUOTE);
    } else {
        int k = j;
        if (k < n && (s[k] == '-' || s[k] == '*' || s[k] == '+') && k + 1 < n && s[k + 1] == ' ') k++;
        else { while (k < n && isdigit((unsigned char)s[k])) k++; if (k > j && k + 1 < n && (s[k] == '.' || s[k] == ')') && s[k + 1] == ' ') k++; else k = j; }
        if (k > j) {
            paint(cls, j, k, C_MARK);
            body = k;
            while (body < n && s[body] == ' ') body++;
            if (n - body >= 3 && s[body] == '[' && s[body + 2] == ']' && (s[body + 1] == ' ' || s[body + 1] == 'x' || s[body + 1] == 'X')) {
                paint(cls, body, body + 3, C_MARK);
                if (s[body + 1] != ' ') { base = C_DONE; paint(cls, body + 3, n, C_DONE); }
                body += 3;
            }
        }
    }
    if (base != C_DONE) md_inline(s, body, n, cls);
    return st;
}

static uint8_t *hl_state; /* hl_state[r] = scanner state at the start of line r */
static int hl_cap, hl_lang = L_NONE;
static uint8_t *hl_cls; static int hl_clscap;

static void hl_invalidate(int r) { if (r < 0) r = 0; if (r < hl_valid) hl_valid = r; }

static int hl_scan_line(int r, int st, uint8_t *cls) {
    Line *L = &E.l[r];
    if (L->len > 4000) { memset(cls, C_NONE, L->len); return st; }
    switch (hl_lang) {
    case L_MD: return scan_md(L->s, L->len, st, cls);
    case L_HTML: return scan_html(L->s, L->len, st, cls);
    case L_C: return scan_code(&lang_c, L->s, L->len, st, cls);
    case L_JS: return scan_code(&lang_js, L->s, L->len, st, cls);
    case L_PY: return scan_code(&lang_py, L->s, L->len, st, cls);
    case L_JSON: return scan_code(&lang_json, L->s, L->len, st, cls);
    case L_CSS: return scan_code(&lang_css, L->s, L->len, st, cls);
    case L_SH: return scan_code(&lang_sh, L->s, L->len, st, cls);
    }
    memset(cls, C_NONE, L->len);
    return st;
}

/* Colour classes for line r (valid until the next call), or NULL when not highlighting. */
static const uint8_t *hl_line(int r) {
    if (hl_lang == L_NONE) return NULL;
    if (hl_cap < E.n + 1) { hl_cap = E.n + 64; hl_state = xrealloc(hl_state, hl_cap); }
    if (hl_valid > E.n) hl_valid = E.n;
    if (E.l[r].len + 1 > hl_clscap) { hl_clscap = E.l[r].len + 256; hl_cls = xrealloc(hl_cls, hl_clscap); }
    if (hl_valid == 0) hl_state[0] = ST_NONE;
    while (hl_valid < r) {
        Line *P = &E.l[hl_valid];
        if (P->len > hl_clscap) { hl_clscap = P->len + 256; hl_cls = xrealloc(hl_cls, hl_clscap); }
        hl_state[hl_valid + 1] = hl_scan_line(hl_valid, hl_state[hl_valid], hl_cls);
        hl_valid++;
    }
    hl_scan_line(r, hl_state[r], hl_cls);
    return hl_cls;
}

static void detect_lang(void) {
    hl_lang = L_NONE; hl_valid = 0;
    if (!E.file) return;
    const char *b = strrchr(E.file, '/'); b = b ? b + 1 : E.file;
    const char *dot = strrchr(b, '.');
    char ext[16] = "";
    if (dot && strlen(dot + 1) < sizeof ext) { for (int i = 0; dot[1 + i]; i++) ext[i] = tolower((unsigned char)dot[1 + i]); }
    static const struct { const char *e; int l; } map[] = {
        {"md", L_MD}, {"markdown", L_MD}, {"c", L_C}, {"h", L_C}, {"cc", L_C}, {"cpp", L_C}, {"hpp", L_C},
        {"js", L_JS}, {"mjs", L_JS}, {"cjs", L_JS}, {"jsx", L_JS}, {"ts", L_JS}, {"tsx", L_JS},
        {"py", L_PY}, {"json", L_JSON}, {"html", L_HTML}, {"htm", L_HTML}, {"xml", L_HTML}, {"svg", L_HTML},
        {"css", L_CSS}, {"sh", L_SH}, {"bash", L_SH}, {"zsh", L_SH}, {"yml", L_SH}, {"yaml", L_SH},
        {"toml", L_SH}, {"conf", L_SH}, {"ini", L_SH}, {"mk", L_SH},
    };
    if (ext[0]) for (size_t i = 0; i < sizeof map / sizeof *map; i++) if (!strcmp(map[i].e, ext)) hl_lang = map[i].l;
    if (!strcmp(b, "Makefile") || !strcmp(b, "makefile") || !strcmp(b, ".bashrc") || !strcmp(b, ".gitignore")) hl_lang = L_SH;
}

/* ---------- drawing ---------- */

static int gutter_w(void) {
    int d = 1;
    for (int n = E.n; n >= 10; n /= 10) d++;
    return d + 2;
}

/* Soft wrap: a logical line is shown as one or more visual rows. One column is kept
 * spare so the cursor can sit after the last character of a full row. */
typedef struct { int r, sub; } VRow;

static int wrapw(void) {
    int w = E.cols - gutter_w() - 1;
    return w < 1 ? 1 : w;
}

/* End byte (exclusive) of the visual row starting at byte s. */
static int row_end(const Line *L, int s) {
    int vc = 0, i = s, W = wrapw();
    while (i < L->len) {
        int cp; int n = u8dec(L->s + i, L->len - i, &cp);
        int w = cp == '\t' ? TABW - vc % TABW : (cp < 0 ? 1 : cpwidth(cp));
        if (vc + w > W && i > s) break;
        vc += w; i += n;
    }
    return i;
}

static int line_nrows(const Line *L) {
    int n = 1;
    for (int s = row_end(L, 0); s < L->len; s = row_end(L, s)) n++;
    return n;
}

static void row_bounds(const Line *L, int sub, int *s, int *e) {
    int st = 0, en = row_end(L, 0);
    for (int k = 0; k < sub && en < L->len; k++) { st = en; en = row_end(L, st); }
    *s = st; *e = en;
}

/* Which wrapped row holds byte c; also gives that row's bounds. */
static int cur_row(const Line *L, int c, int *s, int *e) {
    int st = 0, en = row_end(L, 0), sub = 0;
    while (c >= en && en < L->len) { st = en; en = row_end(L, st); sub++; }
    *s = st; *e = en;
    return sub;
}

static int rcol(const Line *L, int s, int c) {
    int vc = 0;
    for (int i = s; i < c && i < L->len;) {
        int cp; int n = u8dec(L->s + i, L->len - i, &cp);
        vc += cp == '\t' ? TABW - vc % TABW : (cp < 0 ? 1 : cpwidth(cp));
        i += n;
    }
    return vc;
}

/* Byte in row [s,e) at display column col; never leaves the row. */
static int c_from_rcol(const Line *L, int s, int e, int col) {
    int vc = 0, i = s;
    while (i < e) {
        int cp; int n = u8dec(L->s + i, L->len - i, &cp);
        int w = cp == '\t' ? TABW - vc % TABW : (cp < 0 ? 1 : cpwidth(cp));
        if (vc + w > col) return i;
        vc += w; i += n;
    }
    return (e < L->len && e > s) ? prev_c(L, e) : e;
}

static int vrow_step(VRow *v, int d) {
    if (d > 0) {
        if (v->sub + 1 < line_nrows(&E.l[v->r])) { v->sub++; return 1; }
        if (v->r + 1 < E.n) { v->r++; v->sub = 0; return 1; }
    } else {
        if (v->sub > 0) { v->sub--; return 1; }
        if (v->r > 0) { v->r--; v->sub = line_nrows(&E.l[v->r]) - 1; return 1; }
    }
    return 0;
}
static int vrow_cmp(VRow a, VRow b) { return a.r != b.r ? a.r - b.r : a.sub - b.sub; }

static VRow cursor_vrow(void) {
    int s, e;
    VRow v = { E.cur.r, cur_row(&E.l[E.cur.r], E.cur.c, &s, &e) };
    return v;
}

static VRow top_vrow(void) {
    VRow t = { E.top, E.topsub };
    if (t.r >= E.n) t.r = E.n - 1;
    if (t.r < 0) t.r = 0;
    int nr = line_nrows(&E.l[t.r]);
    if (t.sub >= nr) t.sub = nr - 1;
    if (t.sub < 0) t.sub = 0;
    return t;
}

static int scr_cy, scr_cx; /* cursor position inside the text area, 0-based */

static void scroll(void) {
    int th = E.rows - 2;
    VRow c = cursor_vrow(), t = top_vrow();
    if (vrow_cmp(c, t) < 0) t = c;
    else {
        VRow x = t; int found = 0;
        for (int d = 0; d < th; d++) {
            if (vrow_cmp(x, c) == 0) { found = 1; break; }
            if (!vrow_step(&x, 1)) break;
        }
        if (!found) {
            t = c;
            for (int i = 0; i < th - 1; i++) vrow_step(&t, -1);
        }
    }
    E.top = t.r; E.topsub = t.sub;
    scr_cy = 0;
    for (VRow x = t; vrow_cmp(x, c) < 0 && scr_cy < th; scr_cy++) vrow_step(&x, 1);
    int s, e;
    cur_row(&E.l[c.r], E.cur.c, &s, &e);
    scr_cx = rcol(&E.l[c.r], s, E.cur.c);
}

/* Move the viewport by n visual rows, dragging the cursor along if it falls out of view. */
static void scroll_view(int n) {
    int th = E.rows - 2, d = n < 0 ? -1 : 1;
    VRow t = top_vrow();
    for (int i = 0; i < (n < 0 ? -n : n); i++) if (!vrow_step(&t, d)) break;
    E.top = t.r; E.topsub = t.sub;
    VRow bot = t;
    for (int i = 0; i < th - 1; i++) if (!vrow_step(&bot, 1)) break;
    VRow c = cursor_vrow(), target = c;
    if (vrow_cmp(c, t) < 0) target = t;
    else if (vrow_cmp(c, bot) > 0) target = bot;
    else return;
    int s, e;
    Line *L = &E.l[E.cur.r];
    cur_row(L, E.cur.c, &s, &e);
    int col = E.want >= 0 ? E.want : rcol(L, s, E.cur.c);
    Line *N = &E.l[target.r];
    row_bounds(N, target.sub, &s, &e);
    E.cur.r = target.r; E.cur.c = c_from_rcol(N, s, e, col);
    E.want = col; E.want_keep = 1;
}

/* Draw bytes [s,e) of line r (one visual row). */
static void draw_text_row(Abuf *ab, int r, int s, int e) {
    Line *L = &E.l[r];
    Pos a, b; int hs = has_sel();
    if (hs) sel_range(&a, &b);
    int vc = 0, cur_cls = C_NONE;
    const uint8_t *cls = hl_line(r);
    #define SETCLS(c) do { int c_ = (c); if (c_ != cur_cls) { ab_str(ab, "\x1b[m"); if (c_ != C_NONE) { ab_str(ab, "\x1b["); ab_str(ab, class_sgr[c_]); ab_str(ab, "m"); } cur_cls = c_; } } while (0)
    for (int i = s; i < e;) {
        int cp; int n = u8dec(L->s + i, L->len - i, &cp);
        int w = cp == '\t' ? TABW - vc % TABW : (cp < 0 ? 1 : cpwidth(cp));
        int sel = 0;
        if (hs) { Pos p = { r, i }; sel = pos_cmp(p, a) >= 0 && pos_cmp(p, b) < 0; }
        SETCLS(sel ? C_SEL : (cls ? cls[i] : C_NONE));
        if (cp == '\t') { for (int k = 0; k < w; k++) ab_str(ab, " "); }
        else if (cp < 0 || cp < 32 || cp == 127) ab_str(ab, "?");
        else ab_add(ab, L->s + i, n);
        vc += w; i += n;
    }
    if (hs && e == L->len) {
        Pos p = { r, L->len };
        if (pos_cmp(p, a) >= 0 && pos_cmp(p, b) < 0) { SETCLS(C_SEL); ab_str(ab, " "); }
    }
    SETCLS(C_NONE);
    ab_str(ab, "\x1b[K");
    #undef SETCLS
}

static void draw(void) {
    scroll();
    Abuf ab = {0};
    int th = E.rows - 2, gw = gutter_w();
    ab_str(&ab, "\x1b[?25l\x1b[H");
    VRow v = top_vrow();
    int more = 1;
    for (int y = 0; y < th; y++) {
        if (more) {
            Line *L = &E.l[v.r];
            int s, e;
            row_bounds(L, v.sub, &s, &e);
            if (v.sub == 0)
                ab_fmt(&ab, v.r == E.cur.r ? "\x1b[38;5;250m%*d \x1b[m" : "\x1b[38;5;240m%*d \x1b[m", gw - 1, v.r + 1);
            else
                ab_fmt(&ab, "%*s", gw, "");
            draw_text_row(&ab, v.r, s, e);
            more = vrow_step(&v, 1);
        } else {
            ab_str(&ab, "\x1b[38;5;240m~\x1b[m\x1b[K");
        }
        ab_str(&ab, "\r\n");
    }
    /* status bar */
    char left[600], right[128];
    int selchars = 0;
    if (has_sel()) {
        Pos a, b; sel_range(&a, &b);
        for (int r = a.r; r <= b.r; r++) {
            int s = r == a.r ? a.c : 0, e = r == b.r ? b.c : E.l[r].len;
            for (int i = s; i < e; i = next_c(&E.l[r], i)) selchars++;
            if (r != b.r) selchars++;
        }
    }
    snprintf(left, sizeof left, " tvim  %s%s", E.file ? E.file : "[No Name]", E.dirty ? " [+]" : "");
    int ccol = 0;
    { Line *L = &E.l[E.cur.r]; for (int i = 0; i < E.cur.c; i = next_c(L, i)) ccol++; }
    if (selchars) snprintf(right, sizeof right, "(%d selected)  Ln %d, Col %d  %s ", selchars, E.cur.r + 1, ccol + 1, E.crlf ? "CRLF" : "LF");
    else snprintf(right, sizeof right, "Ln %d, Col %d  %s ", E.cur.r + 1, ccol + 1, E.crlf ? "CRLF" : "LF");
    int ll = (int)strlen(left), rl = (int)strlen(right);
    ab_str(&ab, "\x1b[48;5;236;38;5;252m");
    if (ll > E.cols - rl - 1) ll = E.cols - rl - 1 > 0 ? E.cols - rl - 1 : 0;
    ab_add(&ab, left, ll);
    for (int k = ll; k < E.cols - rl; k++) ab_str(&ab, " ");
    ab_add(&ab, right, rl);
    ab_str(&ab, "\x1b[m\r\n");
    /* message line */
    const char *msg = E.msg;
    char hint[] = "Esc Exit (autosaves) | Ctrl+F Find | Ctrl+R Replace | F1 Help";
    if (!(msg[0] && time(NULL) - E.msgt < 5)) msg = hint;
    int ml = (int)strlen(msg); if (ml > E.cols) ml = E.cols;
    ab_str(&ab, "\x1b[38;5;245m");
    ab_add(&ab, msg, ml);
    ab_str(&ab, "\x1b[m\x1b[K");
    ab_fmt(&ab, "\x1b[%d;%dH\x1b[?25h", scr_cy + 1, scr_cx + gw + 1);
    term_write(ab.b, ab.len);
    free(ab.b);
}

/* ---------- prompt ---------- */

/* Returns malloc'd string, or NULL when cancelled. cb is invoked after every change
 * (and with key = Enter/Up/Down for navigation keys) for incremental search. */
typedef void (*PromptCb)(const char *text, int key);
static int prompt_enter_nav; /* when set, Enter is sent to the callback instead of ending the prompt */

static char *prompt(const char *label, const char *init, PromptCb cb) {
    size_t cap = 128, len = 0;
    char *buf = xrealloc(NULL, cap);
    buf[0] = 0;
    if (init) { len = strlen(init); if (len + 1 > cap) { cap = len + 1; buf = xrealloc(buf, cap); } memcpy(buf, init, len + 1); }
    for (;;) {
        snprintf(E.msg, sizeof E.msg, "%s%s", label, buf);
        E.msgt = time(NULL);
        draw();
        /* put cursor on the prompt line */
        char t[64];
        int col = (int)strlen(label) + 1;
        for (size_t i = 0; i < len; i++) if (((unsigned char)buf[i] & 0xC0) != 0x80) col++;
        if (col > E.cols) col = E.cols;
        snprintf(t, sizeof t, "\x1b[%d;%dH", E.rows, col);
        term_write(t, strlen(t));
        int k = read_key();
        if (k == KEY_ESC) { free(buf); E.msg[0] = 0; return NULL; }
        if (k == KEY_ENTER && !(prompt_enter_nav && cb)) { E.msg[0] = 0; return buf; }
        if (k == KEY_ENTER || k == K_UP || k == K_DOWN) { if (cb) cb(buf, k); continue; }
        if (k == KEY_BS || k == CTRL('h')) {
            while (len > 0 && ((unsigned char)buf[len - 1] & 0xC0) == 0x80) len--;
            if (len > 0) len--;
            buf[len] = 0;
        } else if (k == K_PASTE) {
            for (size_t i = 0; i < paste_len && paste_buf[i] != '\n'; i++) {
                if (len + 2 > cap) { cap *= 2; buf = xrealloc(buf, cap); }
                buf[len++] = paste_buf[i];
            }
            buf[len] = 0;
        } else if (k >= 32 && k < K_SPECIAL && k != 127) {
            char o[4]; int n = u8enc(k, o);
            if (len + n + 1 > cap) { cap *= 2; buf = xrealloc(buf, cap); }
            memcpy(buf + len, o, n); len += n; buf[len] = 0;
        } else continue;
        if (cb) cb(buf, 0);
    }
}

/* ---------- movement ---------- */

static int is_word(int cp) { return cp < 0 || cp >= 0x80 || isalnum(cp) || cp == '_'; }
static int char_class(const Line *L, int c) { /* class of char at c: 0 space, 1 word, 2 punct */
    int cp; u8dec(L->s + c, L->len - c, &cp);
    if (cp == ' ' || cp == '\t') return 0;
    return is_word(cp) ? 1 : 2;
}

static void word_right(void) {
    Line *L = &E.l[E.cur.r];
    if (E.cur.c >= L->len) {
        if (E.cur.r + 1 < E.n) { E.cur.r++; E.cur.c = 0; }
        return;
    }
    int c = E.cur.c;
    while (c < L->len && char_class(L, c) == 0) c = next_c(L, c);
    if (c < L->len) {
        int cls = char_class(L, c);
        while (c < L->len && char_class(L, c) == cls) c = next_c(L, c);
    }
    E.cur.c = c;
}

static void word_left(void) {
    Line *L = &E.l[E.cur.r];
    if (E.cur.c == 0) {
        if (E.cur.r > 0) { E.cur.r--; E.cur.c = E.l[E.cur.r].len; }
        return;
    }
    int c = E.cur.c;
    while (c > 0 && char_class(L, prev_c(L, c)) == 0) c = prev_c(L, c);
    if (c > 0) {
        int cls = char_class(L, prev_c(L, c));
        while (c > 0 && char_class(L, prev_c(L, c)) == cls) c = prev_c(L, c);
    }
    E.cur.c = c;
}

static void clamp_cursor(void) {
    if (E.cur.r >= E.n) E.cur.r = E.n - 1;
    if (E.cur.r < 0) E.cur.r = 0;
    if (E.cur.c > E.l[E.cur.r].len) E.cur.c = E.l[E.cur.r].len;
    if (E.anc.r >= E.n) { E.anc.r = E.n - 1; E.anc.c = E.l[E.anc.r].len; }
    if (E.anc.c > E.l[E.anc.r].len) E.anc.c = E.l[E.anc.r].len;
}

static int first_nonblank(const Line *L) {
    int i = 0;
    while (i < L->len && (L->s[i] == ' ' || L->s[i] == '\t')) i++;
    return i;
}

/* key is a K_* movement key (with modifier bits). */
static void move_key(int key) {
    int shift = key & M_SHIFT, ctrl = key & M_CTRL;
    int base = K_BASE(key);
    int th = E.rows - 2;
    if (shift) {
        if (!E.sel || !has_sel()) { E.anc = E.cur; }
        E.sel = 1;
    } else if (has_sel() && (base == K_LEFT || base == K_RIGHT) && !ctrl) {
        Pos a, b; sel_range(&a, &b);
        E.cur = base == K_LEFT ? a : b;
        E.sel = 0;
        return;
    } else E.sel = 0;

    Line *L = &E.l[E.cur.r];
    if (ctrl && (base == K_UP || base == K_DOWN)) { /* jump to previous/next blank line */
        int d = base == K_UP ? -1 : 1, r = E.cur.r + d;
        while (r > 0 && r < E.n - 1 && !(E.l[r].len == 0 && E.l[r - d].len != 0)) r += d;
        if (r < 0) r = 0;
        if (r >= E.n) r = E.n - 1;
        E.cur.r = r;
        E.cur.c = (d > 0 && r == E.n - 1) ? E.l[r].len : 0;
        return;
    }
    switch (base) {
    case K_LEFT:
        if (ctrl) word_left();
        else if (E.cur.c > 0) E.cur.c = prev_c(L, E.cur.c);
        else if (E.cur.r > 0) { E.cur.r--; E.cur.c = E.l[E.cur.r].len; }
        break;
    case K_RIGHT:
        if (ctrl) word_right();
        else if (E.cur.c < L->len) E.cur.c = next_c(L, E.cur.c);
        else if (E.cur.r + 1 < E.n) { E.cur.r++; E.cur.c = 0; }
        break;
    case K_UP: case K_DOWN: case K_PGUP: case K_PGDN: {
        int d = (base == K_UP || base == K_PGUP) ? -1 : 1;
        int amt = (base == K_PGUP || base == K_PGDN) ? th - 1 : 1;
        int rs, re;
        cur_row(L, E.cur.c, &rs, &re);
        if (!E.want_keep || E.want < 0) E.want = rcol(L, rs, E.cur.c);
        E.want_keep = 1;
        VRow v = cursor_vrow();
        int moved = 0;
        for (int i = 0; i < amt; i++) { if (!vrow_step(&v, d)) break; moved++; }
        if (!moved) {
            if (d < 0) { E.cur.c = 0; E.want = 0; }
            else { E.cur.c = L->len; E.want = -1; }
            break;
        }
        Line *N = &E.l[v.r];
        row_bounds(N, v.sub, &rs, &re);
        E.cur.r = v.r;
        E.cur.c = c_from_rcol(N, rs, re, E.want);
        break;
    }
    case K_HOME:
        if (ctrl) { E.cur.r = 0; E.cur.c = 0; }
        else {
            int fnb = first_nonblank(L);
            E.cur.c = (E.cur.c == fnb || fnb == L->len) ? 0 : fnb;
            if (E.cur.c == 0 && fnb != L->len && E.cur.c == fnb) E.cur.c = 0;
        }
        break;
    case K_END:
        if (ctrl) { E.cur.r = E.n - 1; E.cur.c = E.l[E.cur.r].len; }
        else E.cur.c = L->len;
        break;
    }
}

/* ---------- editing ---------- */

static void delete_selection(void) {
    Pos a, b; sel_range(&a, &b);
    text_delete(a, b);
    E.cur = a; E.sel = 0;
}

static void insert_text(const char *t, size_t n, int kind) {
    undo_begin(has_sel() ? 0 : kind);
    if (has_sel()) delete_selection();
    E.sel = 0;
    E.cur = text_insert(E.cur, t, n);
}

static void insert_cp(int cp) {
    char o[4]; int n = u8enc(cp, o);
    insert_text(o, n, 1);
}

static void insert_newline(void) {
    undo_begin(0);
    if (has_sel()) delete_selection();
    E.sel = 0;
    Line *L = &E.l[E.cur.r];
    int ind = 0;
    while (ind < L->len && ind < E.cur.c && (L->s[ind] == ' ' || L->s[ind] == '\t')) ind++;
    char *t = xrealloc(NULL, ind + 2);
    t[0] = '\n';
    memcpy(t + 1, L->s, ind);
    E.cur = text_insert(E.cur, t, ind + 1);
    free(t);
}

static int use_tabs(void) {
    if (!E.file) return 0;
    const char *b = strrchr(E.file, '/'); b = b ? b + 1 : E.file;
    size_t l = strlen(b);
    return strcmp(b, "Makefile") == 0 || strcmp(b, "makefile") == 0 || strcmp(b, "GNUmakefile") == 0 ||
           (l > 3 && strcmp(b + l - 3, ".go") == 0) || (l > 3 && strcmp(b + l - 3, ".mk") == 0);
}

static void indent_lines(int r1, int r2, int out) {
    for (int r = r1; r <= r2; r++) {
        Line *L = &E.l[r];
        if (!out) {
            if (use_tabs()) line_insert(L, 0, "\t", 1);
            else line_insert(L, 0, "    ", TABW);
            if (E.cur.r == r) E.cur.c += use_tabs() ? 1 : TABW;
            if (E.anc.r == r) E.anc.c += use_tabs() ? 1 : TABW;
        } else {
            int rm = 0;
            if (L->len && L->s[0] == '\t') rm = 1;
            else while (rm < TABW && rm < L->len && L->s[rm] == ' ') rm++;
            line_del(L, 0, rm);
            if (E.cur.r == r) E.cur.c = E.cur.c >= rm ? E.cur.c - rm : 0;
            if (E.anc.r == r) E.anc.c = E.anc.c >= rm ? E.anc.c - rm : 0;
        }
    }
}

static void do_tab(int back) {
    if (has_sel() && (E.cur.r != E.anc.r || back)) {
        Pos a, b; sel_range(&a, &b);
        undo_begin(0);
        int r2 = (b.c == 0 && b.r > a.r) ? b.r - 1 : b.r;
        indent_lines(a.r, r2, back);
        return;
    }
    if (back) {
        undo_begin(0);
        indent_lines(E.cur.r, E.cur.r, 1);
        return;
    }
    if (use_tabs()) { insert_text("\t", 1, 1); return; }
    int vc = col_of(&E.l[E.cur.r], E.cur.c);
    int n = TABW - vc % TABW;
    if (has_sel()) vc = 0, n = TABW;
    insert_text("        ", n, 1);
}

static void do_backspace(int word) {
    if (has_sel()) { undo_begin(0); delete_selection(); return; }
    if (E.cur.c == 0 && E.cur.r == 0) return;
    undo_begin(word ? 0 : 2);
    if (E.cur.c == 0) {
        Pos a = { E.cur.r - 1, E.l[E.cur.r - 1].len };
        text_delete(a, E.cur);
        E.cur = a;
        return;
    }
    Pos end = E.cur;
    if (word) word_left();
    else {
        /* smart backspace: inside leading whitespace remove up to the previous tab stop */
        Line *L = &E.l[E.cur.r];
        int c = E.cur.c, allsp = 1;
        for (int i = 0; i < c; i++) if (L->s[i] != ' ') { allsp = 0; break; }
        if (allsp && c > 1) { int rm = c % TABW ? c % TABW : TABW; E.cur.c = c - rm; }
        else E.cur.c = prev_c(L, c);
    }
    text_delete(E.cur, end);
}

static void do_delete(int word) {
    if (has_sel()) { undo_begin(0); delete_selection(); return; }
    Line *L = &E.l[E.cur.r];
    if (E.cur.c >= L->len && E.cur.r + 1 >= E.n) return;
    undo_begin(word ? 0 : 3);
    Pos start = E.cur;
    if (E.cur.c >= L->len) { E.cur.r++; E.cur.c = 0; }
    else if (word) word_right();
    else E.cur.c = next_c(L, E.cur.c);
    Pos end = E.cur;
    E.cur = start;
    text_delete(start, end);
}

static void line_span(int *r1, int *r2) {
    if (has_sel()) {
        Pos a, b; sel_range(&a, &b);
        *r1 = a.r; *r2 = (b.c == 0 && b.r > a.r) ? b.r - 1 : b.r;
    } else *r1 = *r2 = E.cur.r;
}

static void delete_line(void) {
    int r1, r2; line_span(&r1, &r2);
    undo_begin(0);
    E.sel = 0;
    if (r2 - r1 + 1 >= E.n) { line_free(&E.l[0]); E.n = 1; line_init(&E.l[0]); r1 = 0; }
    else buf_remove_lines(r1, r2 - r1 + 1);
    E.cur.r = r1 < E.n ? r1 : E.n - 1;
    E.cur.c = 0;
}

static void duplicate(void) {
    undo_begin(0);
    if (has_sel()) {
        Pos a, b; sel_range(&a, &b);
        size_t n; char *t = text_get(a, b, &n);
        E.sel = 0;
        E.cur = b;
        E.cur = text_insert(E.cur, t, n);
        E.anc = b; E.sel = 1;
        free(t);
        return;
    }
    Line *L = &E.l[E.cur.r];
    Pos p = { E.cur.r, L->len };
    char *t = xrealloc(NULL, L->len + 1);
    t[0] = '\n'; memcpy(t + 1, L->s, L->len);
    text_insert(p, t, L->len + 1);
    free(t);
    E.cur.r++;
}

/* ---------- clipboard ---------- */

static const char b64[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
static void osc52_copy(const char *t, size_t n) {
    if (n > 700000) return;
    Abuf ab = {0};
    ab_str(&ab, "\x1b]52;c;");
    for (size_t i = 0; i < n; i += 3) {
        unsigned v = (unsigned char)t[i] << 16;
        if (i + 1 < n) v |= (unsigned char)t[i + 1] << 8;
        if (i + 2 < n) v |= (unsigned char)t[i + 2];
        char o[4] = { b64[(v >> 18) & 63], b64[(v >> 12) & 63],
                      i + 1 < n ? b64[(v >> 6) & 63] : '=', i + 2 < n ? b64[v & 63] : '=' };
        ab_add(&ab, o, 4);
    }
    ab_str(&ab, "\x07");
    term_write(ab.b, ab.len);
    free(ab.b);
}

static void clip_set(char *t, size_t n, int lines) {
    free(E.clip);
    E.clip = t; E.cliplen = n; E.cliplines = lines;
    osc52_copy(t, n);
}

static void do_copy(int cut) {
    size_t n; char *t;
    if (has_sel()) {
        Pos a, b; sel_range(&a, &b);
        t = text_get(a, b, &n);
        clip_set(t, n, 0);
        if (cut) { undo_begin(0); delete_selection(); }
        set_msg("%s %zu bytes", cut ? "Cut" : "Copied", n);
    } else {
        Pos a = { E.cur.r, 0 }, b = { E.cur.r, E.l[E.cur.r].len };
        t = text_get(a, b, &n);
        clip_set(t, n, 1);
        if (cut) delete_line();
        set_msg("%s line", cut ? "Cut" : "Copied");
    }
}

static void do_paste(void) {
    if (!E.clip) { set_msg("Clipboard is empty (use your terminal's paste)"); return; }
    if (E.cliplines && !has_sel()) {
        undo_begin(0);
        Pos p = { E.cur.r, 0 };
        char *t = xrealloc(NULL, E.cliplen + 2);
        memcpy(t, E.clip, E.cliplen); t[E.cliplen] = '\n';
        text_insert(p, t, E.cliplen + 1);
        free(t);
        E.cur.r++;
        return;
    }
    insert_text(E.clip, E.cliplen, 0);
}

/* ---------- search ---------- */

static int ci_for(const char *q) {
    for (; *q; q++) if (isupper((unsigned char)*q)) return 0;
    return 1;
}
static int match_at(const char *s, const char *q, int ql, int ci) {
    for (int i = 0; i < ql; i++) {
        unsigned char x = s[i], y = q[i];
        if (ci) { x = tolower(x); y = tolower(y); }
        if (x != y) return 0;
    }
    return 1;
}

/* Find q starting at p (inclusive when fwd, exclusive-before when backward), wrapping. */
static int find_from(Pos p, const char *q, int fwd, Pos *out) {
    int ql = (int)strlen(q);
    if (!ql) return 0;
    int ci = ci_for(q);
    for (int k = 0; k <= E.n; k++) {
        int r = fwd ? (p.r + k) % E.n : ((p.r - k) % E.n + E.n) % E.n;
        Line *L = &E.l[r];
        if (fwd) {
            int start = k == 0 ? p.c : 0;
            for (int i = start; i + ql <= L->len; i++)
                if (match_at(L->s + i, q, ql, ci)) { out->r = r; out->c = i; return 1; }
        } else {
            int start = k == 0 ? p.c - 1 : L->len - ql;
            if (start > L->len - ql) start = L->len - ql;
            for (int i = start; i >= 0; i--)
                if (match_at(L->s + i, q, ql, ci)) { out->r = r; out->c = i; return 1; }
        }
    }
    return 0;
}

static void select_match(Pos m, int ql) {
    E.anc = m; E.cur.r = m.r; E.cur.c = m.c + ql; E.sel = 1;
}

static Pos find_start; /* where an incremental search began */

static void find_cb(const char *q, int key) {
    Pos m, from;
    int ql = (int)strlen(q);
    if (!ql) return;
    if (key == K_UP) {
        from = has_sel() ? ((pos_cmp(E.cur, E.anc) < 0) ? E.cur : E.anc) : E.cur;
        if (find_from(from, q, 0, &m)) select_match(m, ql); else set_msg("No match");
    } else if (key == K_DOWN || key == KEY_ENTER) {
        from = E.cur;
        if (find_from(from, q, 1, &m)) select_match(m, ql); else set_msg("No match");
    } else {
        if (find_from(find_start, q, 1, &m)) select_match(m, ql);
        else { E.sel = 0; E.cur = find_start; }
    }
}

static void find_next(int fwd) {
    if (!E.lastq || !*E.lastq) { set_msg("No previous search"); return; }
    Pos from, m;
    if (fwd) from = E.cur;
    else from = has_sel() ? ((pos_cmp(E.cur, E.anc) < 0) ? E.cur : E.anc) : E.cur;
    if (find_from(from, E.lastq, fwd, &m)) select_match(m, (int)strlen(E.lastq));
    else set_msg("No match for '%s'", E.lastq);
}

static void do_find(void) {
    Pos sc = E.cur, sa = E.anc; int ss = E.sel;
    find_start = has_sel() ? ((pos_cmp(E.cur, E.anc) < 0) ? E.cur : E.anc) : E.cur;
    prompt_enter_nav = 1;
    char *q = prompt("Find (Enter/Down next, Up prev, Esc done): ", NULL, find_cb);
    prompt_enter_nav = 0;
    /* prompt only returns NULL (Esc) when nav is on */
    if (q == NULL) {
        /* keep the current match selected; if nothing matched, restore */
        if (!has_sel()) { E.cur = sc; E.anc = sa; E.sel = ss; }
        return;
    }
    free(q);
}

static void do_replace(void) {
    char *q = prompt("Replace - find: ", E.lastq, NULL);
    if (!q || !*q) { free(q); return; }
    free(E.lastq); E.lastq = q;
    char *rep = prompt("Replace with: ", NULL, NULL);
    if (!rep) return;
    int ql = (int)strlen(q), rl = (int)strlen(rep), ci = ci_for(q), count = 0;
    undo_begin(0);
    for (int r = 0; r < E.n; r++) {
        Line *L = &E.l[r];
        for (int i = 0; i + ql <= L->len;) {
            if (match_at(L->s + i, q, ql, ci)) {
                line_del(L, i, ql);
                line_insert(L, i, rep, rl);
                i += rl ? rl : 1;
                count++;
            } else i++;
        }
    }
    free(rep);
    E.sel = 0;
    hl_valid = 0;
    clamp_cursor();
    set_msg("Replaced %d occurrence%s", count, count == 1 ? "" : "s");
}

/* ---------- save / quit ---------- */

static void do_save(int as) {
    if (!E.file || as) {
        char *f = prompt("Save as: ", E.file, NULL);
        if (!f || !*f) { free(f); set_msg("Save cancelled"); return; }
        free(E.file); E.file = f;
    }
    detect_lang();
    if (save_file() != 0) set_msg("Can't save %s: %s", E.file, strerror(errno));
}

static int autosave_tick(void) {
    if (!E.dirty || !E.file || time(NULL) - E.lastedit < 1) return 0;
    E.lastedit = time(NULL);
    if (save_file() != 0) { set_msg("Autosave failed for %s: %s", E.file, strerror(errno)); }
    else { size_t n = strlen(E.msg); (void)n; char t[512]; snprintf(t, sizeof t, "Autosaved %s", E.file); set_msg("%s", t); }
    return 1;
}

static void quit_now(void) {
    term_restore();
    exit(0);
}

/* Esc / Ctrl+Q: save (asking for a name if needed) and leave. */
static void do_quit(void) {
    if (E.file) {
        if (E.dirty && save_file() != 0) { set_msg("Can't save %s: %s - not quitting", E.file, strerror(errno)); return; }
        quit_now();
    }
    if (!E.dirty && E.n == 1 && E.l[0].len == 0) quit_now();
    for (;;) {
        char *f = prompt("File name (Esc to skip): ", NULL, NULL);
        if (f && *f) {
            free(E.file); E.file = f;
            if (save_file() != 0) { set_msg("Can't save %s: %s", E.file, strerror(errno)); free(E.file); E.file = NULL; return; }
            quit_now();
        }
        free(f);
        set_msg("Without a file name nothing is saved. Quit anyway? (y = quit, n = name it)");
        draw();
        int k;
        do k = read_key(); while (k == K_RESIZE || k == K_MOUSE);
        if (k == 'y' || k == 'Y') quit_now();
        if (k != 'n' && k != 'N' && k != KEY_ENTER) { set_msg("Not quitting"); return; }
    }
}

/* ---------- help ---------- */

static void show_help(void) {
    static const char *lines[] = {
        "tvim " TVIM_VERSION " - keys",
        "",
        "File       Esc, Esc save & exit   Ctrl+O save as (name the file)",
        "           (named files autosave about 1s after every change)",
        "Select     Shift+Arrows         Ctrl+Shift+Arrows (by word)",
        "           Shift+Home/End       Ctrl+A select all     mouse drag / shift+click",
        "           Ctrl+Shift+Up/Down select by paragraph",
        "Move       Ctrl+Left/Right word Home smart home       Ctrl+Home/End file ends",
        "           PgUp/PgDn page",
        "Clipboard  Ctrl+C copy          Ctrl+X cut            Ctrl+V paste",
        "           (no selection = whole line; terminal paste also works)",
        "Edit       Ctrl+Z undo          Ctrl+Y / Ctrl+Shift+Z redo",
        "           Ctrl+Backspace/Delete delete word          Ctrl+K delete line",
        "           Ctrl+D duplicate line/selection",
        "           Tab / Shift+Tab indent / unindent",
        "Search     Ctrl+F find          F3 / Shift+F3 next / prev",
        "           Ctrl+R replace all",
        "",
        "Press any key to return.",
    };
    Abuf ab = {0};
    ab_str(&ab, "\x1b[?25l\x1b[H\x1b[2J");
    for (size_t i = 0; i < sizeof lines / sizeof *lines; i++) {
        ab_str(&ab, i == 0 ? "\x1b[1m" : "");
        ab_str(&ab, lines[i]);
        ab_str(&ab, "\x1b[m\r\n");
    }
    term_write(ab.b, ab.len);
    free(ab.b);
    int k;
    do k = read_key(); while (k == K_RESIZE || k == K_MOUSE);
}

/* ---------- mouse ---------- */

static Pos screen_to_pos(int x, int y) {
    VRow v = top_vrow();
    for (int i = 0; i < y - 1; i++) if (!vrow_step(&v, 1)) break;
    Line *L = &E.l[v.r];
    int rs, re;
    row_bounds(L, v.sub, &rs, &re);
    int col = x - 1 - gutter_w();
    if (col < 0) col = 0;
    Pos p = { v.r, c_from_rcol(L, rs, re, col) };
    return p;
}

static void handle_mouse(void) {
    int b = mouse_b & 3, wheel = mouse_b & 64, drag = mouse_b & 32;
    int th = E.rows - 2;
    if (wheel) {
        scroll_view((mouse_b & 1) ? 3 : -3);
        return;
    }
    if (b != 0 || mouse_y > th) return;
    if (mouse_release) { if (!has_sel()) E.sel = 0; return; }
    Pos p = screen_to_pos(mouse_x, mouse_y);
    if (drag) {
        if (!E.sel) { E.anc = E.cur; E.sel = 1; }
        E.cur = p;
    } else if (mouse_b & 4) { /* shift+click extends */
        if (!E.sel) { E.anc = E.cur; E.sel = 1; }
        E.cur = p;
    } else {
        E.cur = p; E.anc = p; E.sel = 1;
    }
}

/* ---------- main loop ---------- */

static int esc_pending;

static void process_key(int key) {
    int base = K_BASE(key);
    int shift = key & M_SHIFT, ctrl = key & M_CTRL, alt = key & M_ALT;

    switch (base) {
    case K_UP: case K_DOWN:
        if (ctrl && !shift && !alt) { scroll_view(base == K_UP ? -1 : 1); return; } /* scroll viewport */
        /* fallthrough */
    case K_LEFT: case K_RIGHT: case K_HOME: case K_END: case K_PGUP: case K_PGDN:
        move_key(key & ~M_ALT);
        return;
    case K_DEL:
        if (shift && !ctrl) { do_copy(1); return; }
        do_delete(ctrl);
        return;
    case K_INS:
        if (shift) do_paste();
        else if (ctrl) do_copy(0);
        return;
    case K_BTAB: do_tab(1); return;
    case K_F1: show_help(); return;
    case K_F2: do_save(1); return;
    case K_F3: find_next(!shift); return;
    case K_MOUSE: handle_mouse(); return;
    case K_PASTE: insert_text(paste_buf, paste_len, 0); return;
    case K_RESIZE: return;
    }

    if (alt) {
        if (base == KEY_BS) do_backspace(1);
        return;
    }

    switch (key) {
    case CTRL('o'): do_save(1); return;
    case CTRL('a'):
        E.anc.r = 0; E.anc.c = 0; E.sel = 1;
        E.cur.r = E.n - 1; E.cur.c = E.l[E.cur.r].len;
        return;
    case CTRL('c'): do_copy(0); return;
    case CTRL('x'): do_copy(1); return;
    case CTRL('v'): do_paste(); return;
    case CTRL('z'): do_undo(); clamp_cursor(); return;
    case CTRL('y'): do_redo(); clamp_cursor(); return;
    case CTRL('f'): do_find(); return;
    case CTRL('r'): do_replace(); return;
    case CTRL('k'): delete_line(); return;
    case CTRL('d'): duplicate(); return;
    case CTRL('h'): do_backspace(1); return; /* Ctrl+Backspace on most terminals */
    case KEY_BS: do_backspace(0); return;
    case KEY_ENTER: insert_newline(); return;
    case KEY_TAB: do_tab(0); return;
    case KEY_ESC:
        esc_pending = 1;
        set_msg("Press Esc again to save & exit - any other key returns to the editor");
        return;
    }
    if (key >= 32 && key < K_SPECIAL) insert_cp(key);
}

int main(int argc, char **argv) {
    if (argc > 1 && (!strcmp(argv[1], "--version") || !strcmp(argv[1], "-v"))) {
        printf("tvim %s\n", TVIM_VERSION);
        return 0;
    }
    if (argc > 1 && (!strcmp(argv[1], "--help") || !strcmp(argv[1], "-h"))) {
        printf("usage: tvim [file]\n\nA small VS Code style terminal editor. Press F1 inside for keys.\n");
        return 0;
    }
    if (!isatty(STDIN_FILENO) || !isatty(STDOUT_FILENO)) {
        fprintf(stderr, "tvim: needs a terminal\n");
        return 1;
    }
    buf_reset();
    E.final_nl = 1;
    E.want = -1;
    if (argc > 1) {
        E.file = strdup(argv[1]);
        int r = load_file(E.file);
        if (r < 0) { fprintf(stderr, "tvim: %s: %s\n", E.file, strerror(errno)); return 1; }
        if (r == 0) set_msg("New file %s", E.file);
        else set_msg("Opened %s (%d lines)", E.file, E.n);
    }
    detect_lang();
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_signal;
    sigaction(SIGWINCH, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);
    sigaction(SIGHUP, &sa, NULL);
    signal(SIGPIPE, SIG_IGN);
    atexit(term_restore);
    get_size();
    term_raw();
    for (;;) {
        draw();
        int key = read_key();
        E.prevkind = E.lastkind;
        E.lastkind = 0;
        E.want_keep = 0;
                if (esc_pending) {
            if (key == K_RESIZE || key == K_MOUSE) continue; /* redraw only, keep waiting */
            esc_pending = 0;
            if (key == KEY_ESC) do_quit();
            else E.msg[0] = 0;
            continue;
        }
        process_key(key);
        clamp_cursor();
        if (!E.want_keep) E.want = -1;
    }
}
