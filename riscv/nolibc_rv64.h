/* Minimal Linux RV64 freestanding syscall shim for `main.c` (`-DCA_NOLIBC`).
 * Enables cross-compiling the exact shared `main.c` harness with
 * `riscv64-unknown-elf-gcc -DCA_NOLIBC -std=gnu23 -O2 -nostdlib -mno-relax`
 * and running under `qemu-riscv64` or Linux RV64 without a glibc sysroot.
 * Native RISC-V Linux builds omit `-DCA_NOLIBC` and link standard libc. */
#ifndef CA_NOLIBC_RV64_H
#define CA_NOLIBC_RV64_H

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>

typedef long ssize_t;

#define EINTR   4
#define ENOMEM  12

#define AT_FDCWD (-100)
#define O_RDONLY 0

#define PROT_READ  1
#define PROT_WRITE 2
#define MAP_PRIVATE   0x02
#define MAP_ANONYMOUS 0x20
#define MAP_NORESERVE 0x4000
#define MAP_FAILED ((void *)-1)
#define MADV_HUGEPAGE 14

#define S_IFMT  0170000u
#define S_IFREG 0100000u
#define S_ISREG(m) (((m) & S_IFMT) == S_IFREG)

/* Linux asm-generic 64-bit `struct stat` (riscv64). */
struct stat {
  unsigned long st_dev;
  unsigned long st_ino;
  unsigned int  st_mode;
  unsigned int  st_nlink;
  unsigned int  st_uid;
  unsigned int  st_gid;
  unsigned long st_rdev;
  unsigned long __pad1;
  long          st_size;
  int           st_blksize;
  int           __pad2;
  long          st_blocks;
  long          st_atime;
  unsigned long st_atime_nsec;
  long          st_mtime;
  unsigned long st_mtime_nsec;
  long          st_ctime;
  unsigned long st_ctime_nsec;
  unsigned int  __unused4;
  unsigned int  __unused5;
};

static int errno;

static inline long ca_sys6(long nr, long a0, long a1, long a2, long a3, long a4, long a5) {
  register long r0 __asm__("a0") = a0;
  register long r1 __asm__("a1") = a1;
  register long r2 __asm__("a2") = a2;
  register long r3 __asm__("a3") = a3;
  register long r4 __asm__("a4") = a4;
  register long r5 __asm__("a5") = a5;
  register long r7 __asm__("a7") = nr;
  __asm__ volatile("ecall"
                   : "+r"(r0)
                   : "r"(r1), "r"(r2), "r"(r3), "r"(r4), "r"(r5), "r"(r7)
                   : "memory");
  return r0;
}

static inline long ca_ret(long r) {
  if (r < 0 && r >= -4095) {
    errno = (int)(-r);
    return -1;
  }
  return r;
}

/* Linux asm-generic syscall numbers (riscv64). */
#define CA_NR_openat     56
#define CA_NR_close      57
#define CA_NR_read       63
#define CA_NR_write      64
#define CA_NR_fstat      80
#define CA_NR_exit_group 94
#define CA_NR_munmap     215
#define CA_NR_mmap       222
#define CA_NR_madvise    233

static inline int open(const char *path, int flags) {
  return (int)ca_ret(ca_sys6(CA_NR_openat, AT_FDCWD, (long)path, flags, 0, 0, 0));
}

static inline int close(int fd) {
  return (int)ca_ret(ca_sys6(CA_NR_close, fd, 0, 0, 0, 0, 0));
}

static inline ssize_t read(int fd, void *buf, size_t n) {
  return (ssize_t)ca_ret(ca_sys6(CA_NR_read, fd, (long)buf, (long)n, 0, 0, 0));
}

static inline ssize_t write(int fd, const void *buf, size_t n) {
  return (ssize_t)ca_ret(ca_sys6(CA_NR_write, fd, (long)buf, (long)n, 0, 0, 0));
}

static inline int fstat(int fd, struct stat *st) {
  return (int)ca_ret(ca_sys6(CA_NR_fstat, fd, (long)st, 0, 0, 0, 0));
}

static inline void *mmap(void *addr, size_t len, int prot, int flags, int fd, long off) {
  long r = ca_sys6(CA_NR_mmap, (long)addr, (long)len, prot, flags, fd, off);
  if (r < 0 && r >= -4095) {
    errno = (int)(-r);
    return MAP_FAILED;
  }
  return (void *)r;
}

static inline int munmap(void *addr, size_t len) {
  return (int)ca_ret(ca_sys6(CA_NR_munmap, (long)addr, (long)len, 0, 0, 0, 0));
}

static inline int madvise(void *addr, size_t len, int advice) {
  return (int)ca_ret(ca_sys6(CA_NR_madvise, (long)addr, (long)len, advice, 0, 0, 0));
}

static inline _Noreturn void exit(int code) {
  ca_sys6(CA_NR_exit_group, code, 0, 0, 0, 0, 0);
  __builtin_unreachable();
}

__attribute__((optimize("no-tree-loop-distribute-patterns")))
void *memcpy(void *dst, const void *src, size_t n) {
  uint8_t *d = (uint8_t *)dst;
  const uint8_t *s = (const uint8_t *)src;
  for (size_t i = 0; i < n; i++) d[i] = s[i];
  return dst;
}

__attribute__((optimize("no-tree-loop-distribute-patterns")))
void *memset(void *dst, int c, size_t n) {
  uint8_t *d = (uint8_t *)dst;
  for (size_t i = 0; i < n; i++) d[i] = (uint8_t)c;
  return dst;
}

__attribute__((optimize("no-tree-loop-distribute-patterns")))
size_t strlen(const char *s) {
  size_t n = 0;
  while (s[n]) n++;
  return n;
}

static int strcmp(const char *a, const char *b) {
  while (*a && *a == *b) { a++; b++; }
  return (unsigned char)*a - (unsigned char)*b;
}

static int strncmp(const char *a, const char *b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    if (a[i] != b[i] || !a[i]) return (unsigned char)a[i] - (unsigned char)b[i];
  }
  return 0;
}

static int atoi(const char *s) {
  while (*s == ' ' || *s == '\t') s++;
  int neg = 0;
  if (*s == '-') { neg = 1; s++; }
  else if (*s == '+') { s++; }
  int v = 0;
  while (*s >= '0' && *s <= '9') { v = v * 10 + (*s - '0'); s++; }
  return neg ? -v : v;
}

static const char *strerror(int err) {
  switch (err) {
    case 1:  return "Operation not permitted";
    case 2:  return "No such file or directory";
    case 4:  return "Interrupted system call";
    case 5:  return "Input/output error";
    case 9:  return "Bad file descriptor";
    case 12: return "Cannot allocate memory";
    case 13: return "Permission denied";
    case 21: return "Is a directory";
    case 22: return "Invalid argument";
    case 38: return "Function not implemented";
    default: return "error";
  }
}

/* Simple mmap-backed allocator (16-byte header storing mapped total bytes). */
static void *malloc(size_t n) {
  if (n > SIZE_MAX - 4096 - 16) { errno = ENOMEM; return NULL; }
  size_t total = ((n + 16) + 4095) & ~(size_t)4095;
  if (total == 0) total = 4096;
  void *p = mmap(0, total, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (p == MAP_FAILED) return NULL;
  ((uint64_t *)p)[0] = total;
  return (uint8_t *)p + 16;
}

static void free(void *p) {
  if (!p) return;
  uint8_t *raw = (uint8_t *)p - 16;
  size_t total = (size_t)((uint64_t *)raw)[0];
  munmap(raw, total);
}

static void *realloc(void *p, size_t n) {
  if (!p) return malloc(n);
  uint8_t *raw = (uint8_t *)p - 16;
  size_t old_total = (size_t)((uint64_t *)raw)[0];
  size_t old_usable = old_total - 16;
  if (n <= old_usable) return p;
  void *q = malloc(n);
  if (!q) return NULL;
  memcpy(q, p, old_usable);
  free(p);
  return q;
}

/* Minimal unbuffered FILE / printf / fprintf supporting `%s` and `%llu`. */
typedef struct { int fd; int err; } FILE;
static FILE ca_stdout_obj = { 1, 0 };
static FILE ca_stderr_obj = { 2, 0 };
#define stdout (&ca_stdout_obj)
#define stderr (&ca_stderr_obj)

static void ca_write_all(FILE *f, const char *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t k = write(f->fd, buf + off, len - off);
    if (k < 0 && errno == EINTR) continue;
    if (k <= 0) { f->err = 1; return; }
    off += (size_t)k;
  }
}

static int ca_vfprintf(FILE *f, const char *fmt, va_list ap) {
  char out[512];
  size_t pos = 0;
  for (const char *p = fmt; *p; p++) {
    if (*p != '%') {
      out[pos++] = *p;
      if (pos == sizeof out) { ca_write_all(f, out, pos); pos = 0; }
      continue;
    }
    p++;
    if (*p == 's') {
      if (pos) { ca_write_all(f, out, pos); pos = 0; }
      const char *s = va_arg(ap, const char *);
      if (!s) s = "(null)";
      ca_write_all(f, s, strlen(s));
    } else if (p[0] == 'l' && p[1] == 'l' && p[2] == 'u') {
      p += 2;
      unsigned long long v = va_arg(ap, unsigned long long);
      char tmp[24];
      size_t k = 0;
      do { tmp[k++] = (char)('0' + (v % 10)); v /= 10; } while (v);
      while (k--) {
        out[pos++] = tmp[k];
        if (pos == sizeof out) { ca_write_all(f, out, pos); pos = 0; }
      }
    } else if (*p == '%') {
      out[pos++] = '%';
      if (pos == sizeof out) { ca_write_all(f, out, pos); pos = 0; }
    } else {
      if (*p) {
        out[pos++] = *p;
        if (pos == sizeof out) { ca_write_all(f, out, pos); pos = 0; }
      } else {
        break;
      }
    }
  }
  if (pos) ca_write_all(f, out, pos);
  return f->err ? -1 : 0;
}

static int fprintf(FILE *f, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = ca_vfprintf(f, fmt, ap);
  va_end(ap);
  return r;
}

static int printf(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = ca_vfprintf(stdout, fmt, ap);
  va_end(ap);
  return r;
}

static int fflush(FILE *f) { return f->err ? -1 : 0; }
static int ferror(FILE *f) { return f->err; }

int main(int argc, char **argv);

__attribute__((used)) static _Noreturn void ca_start_c_entry(long *sp) {
  int argc = (int)sp[0];
  char **argv = (char **)(sp + 1);
  exit(main(argc, argv));
}

__asm__(
  ".text\n"
  ".globl _start\n"
  "_start:\n"
  "  mv a0, sp\n"
  "  andi sp, sp, -16\n"
  "  tail ca_start_c_entry\n"
);

#endif /* CA_NOLIBC_RV64_H */
