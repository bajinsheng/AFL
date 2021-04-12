
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <malloc.h>
#include <stdarg.h>
#include <pthread.h>

#if 1
#define DEBUG(...)
#else
#define DEBUG(msg, ...)                                                 \
    fprintf(stderr, "\33[35mDEBUG\33[0m: " msg "\n", ## __VA_ARGS__)
#endif

extern void *__libc_malloc(size_t);
extern void __libc_free(void *ptr);

#define QUARANTINE_MAX              4096
#define QUARANTINE_MAX_ALLOC_SIZE   4096

#define PAGE_SIZE       4096

static void *quarantine[QUARANTINE_MAX] = {NULL};
static size_t quarantine_ptr = 0;
static pthread_mutex_t quarantine_lock = PTHREAD_MUTEX_INITIALIZER;

void set_canary(uint64_t *ptr64, uint8_t delta);
bool test_canary(const uint64_t *ptr64);

asm (
    ".type set_canary, @function\n"
    ".globl set_canary\n"
    "set_canary:\n"
    "\tmov %fs:40, %rax\n"
    "\tnegq %rax\n"
    "\tandq $-0x8,%rax\n"
    "\txor %rsi,%rax\n"
    "\tmov %rax,(%rdi)\n"
    "\txor %eax,%eax\n"
    "\tretq\n"

    ".type test_canary, @function\n"
    ".globl test_canary\n"
    "test_canary:\n"
    "\tmov %fs:40, %rax\n"
    "\tmov (%rdi),%rdi\n"
    "\tandq $-0x8,%rdi\n"
    "\tlea (%rdi,%rax),%rax\n"
    "\ttestq %rax,%rax\n"
    "\tsete %al\n"
    "\tretq\n"
);

static void reset_canary(uint64_t *ptr64)
{
    if (test_canary(ptr64))
        *ptr64 = 0x0;
}

void *malloc(size_t size)
{
    if (size == 0) {
        return NULL;
    }
    size_t size_0 = size;
    size += sizeof(uint64_t);
    if (size % sizeof(uint64_t) != 0)
        size += sizeof(uint64_t) - size % sizeof(uint64_t);
    void *ptr = __libc_malloc(size);
    if (ptr == NULL)
        return ptr;
    uint64_t *ptr64 = (uint64_t *)ptr;
    ptr64 += (size / sizeof(uint64_t)) - 1;
    set_canary(ptr64, size_0 % sizeof(uint64_t));

    DEBUG("malloc(%zu) = %p", size_0, ptr);
    return ptr;
}

// Necessary to stop gcc optimizing the calloc impl to a calloc call...
static void *__malloc(size_t size) __attribute__((__alias__("malloc")));

void *calloc(size_t nmemb, size_t size_0)
{
    size_t size = size_0 * nmemb;
    void *ptr = __malloc(size);
    if (ptr == NULL)
        return ptr;
    memset(ptr, 0, size);

    DEBUG("calloc(%zu, %zu) = %p", nmemb, size_0, ptr);
    return ptr;
}

void *realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        return malloc(size);
    }
    if (size == 0) {
        free(ptr);
        return NULL;
    }
    size_t old_size = malloc_usable_size(ptr) - sizeof(uint64_t);
    void *old_ptr   = ptr;

    size_t new_size = size;
    void *new_ptr   = __malloc(new_size);
    if (new_ptr == NULL)
        return new_ptr;

    size_t copy_size = (new_size < old_size? new_size: old_size);

    uint64_t *old_ptr64 = (uint64_t *)old_ptr;
    uint64_t *new_ptr64 = (uint64_t *)new_ptr;
    size_t copy_size64  = copy_size / sizeof(uint64_t);
    for (size_t i = 0; i < copy_size64; i++)
    {
        new_ptr64[i] = old_ptr64[i];
    }

    uint8_t *old_ptr8 = (uint8_t *)old_ptr;
    uint8_t *new_ptr8 = (uint8_t *)new_ptr;
    for (size_t i = copy_size64 * sizeof(uint64_t); i < copy_size; i++)
    {
        new_ptr8[i] = old_ptr8[i];
    }

    free(old_ptr);

    DEBUG("realloc(%p, %zu) = %p", old_ptr, new_size, new_ptr);
    return new_ptr;
}

void free(void *ptr)
{
    if (ptr == NULL)
        return;

    DEBUG("free(%p)", ptr);

    size_t size = malloc_usable_size(ptr);
    if (size > QUARANTINE_MAX_ALLOC_SIZE)
    {
        __libc_free(ptr);
        return;
    }

    size -= size % sizeof(uint64_t);
    uint64_t *ptr64 = (uint64_t *)ptr;
    for (size_t i = 0; i < size / sizeof(uint64_t); i++)
        set_canary(ptr64 + i, 1); //set the minimal byte offset, so it will crash even as the last token

    void *old_ptr = NULL;
    pthread_mutex_lock(&quarantine_lock);
    old_ptr = quarantine[quarantine_ptr];
    quarantine[quarantine_ptr++] = ptr;
    if (quarantine_ptr >= QUARANTINE_MAX)
        quarantine_ptr = 0;
    pthread_mutex_unlock(&quarantine_lock);

    if (old_ptr != NULL)
        __libc_free(old_ptr);
}

void *memset (void *dst, int val, size_t n)
{
    // Check the canary of the destination
    uintptr_t idst = (uintptr_t)dst;
    size_t front_delta = idst % sizeof(uint64_t);
    int check_len = n + front_delta;
    idst -= front_delta;
    size_t end_delta = check_len % sizeof(uint64_t);
    if (end_delta)
        check_len += sizeof(uint64_t);
    check_len /= sizeof(uint64_t);
    uint64_t *dst64 = (uint64_t *)idst;
    for (size_t i = 0; i < check_len; i++) // Check the token of each memory
        if (test_canary(dst64 + i))
            asm ("ud2");
    if (end_delta) {    // Check the token after the current memory for byte-accurate checking
        dst64 += check_len;
        if ((uintptr_t)dst64 % PAGE_SIZE != 0 && test_canary((const uint64_t *)dst64))
        {
            uint64_t token = *dst64;
            if ((token & 0x7) && ((token & 0x7) < end_delta)) { // If the token equals to 0x00, which means 0x08
                asm ("ud2");
            }
        }
    }
    // do the memset work
    unsigned char *ptr = dst;
    while (n-- > 0)
        *ptr++ = val;
    return dst;
}

void *memcpy(void * restrict dst, const void * restrict src, size_t n)
{
    uint8_t *dst8 = (uint8_t *)dst;
    const uint8_t *src8 = (const uint8_t *)src;

    // Check the canary of the destination
    uintptr_t idst = (uintptr_t)dst;
    size_t front_delta = idst % sizeof(uint64_t);
    int check_len = n + front_delta;
    idst -= front_delta;
    size_t end_delta = check_len % sizeof(uint64_t);
    if (end_delta)
        check_len += sizeof(uint64_t);
    check_len /= sizeof(uint64_t);
    uint64_t *dst64 = (uint64_t *)idst;
    for (size_t i = 0; i < check_len; i++) // Check the token of each memory
        if (test_canary(dst64 + i))
            asm ("ud2");
    if (end_delta) {    // Check the token after the current memory for byte-accurate checking
        dst64 += check_len;
        if ((uintptr_t)dst64 % PAGE_SIZE != 0 && test_canary((const uint64_t *)dst64))
        {
            uint64_t token = *dst64;
            if ((token & 0x7) && ((token & 0x7) < end_delta)) { // If the token equals to 0x00, which means 0x08
                asm ("ud2");
            }
        }
    }

    // Check the canary of the source
    uintptr_t isrc = (uintptr_t)src;
    size_t src_front_delta = isrc % sizeof(uint64_t);
    int src_check_len = n + src_front_delta;
    isrc -= src_front_delta;
    size_t src_end_delta = src_check_len % sizeof(uint64_t);
    if (src_end_delta)
        src_check_len += sizeof(uint64_t);
    src_check_len /= sizeof(uint64_t);
    uint64_t *src64 = (uint64_t *)isrc;
    for (size_t i = 0; i < src_check_len; i++) // Check the token of each memory
        if (test_canary(src64 + i))
            asm ("ud2");
    if (src_end_delta) {    // Check the token after the current memory for byte-accurate checking
        src64 += src_check_len;
        if ((uintptr_t)src64 % PAGE_SIZE != 0 && test_canary((const uint64_t *)src64))
        {
            uint64_t token = *src64;
            if ((token & 0x7) && ((token & 0x7) < src_end_delta)) { // If the token equals to 0x00, which means 0x08
                asm ("ud2");
            }
        }
    }


    // Copy the raw data
    for (size_t i = 0; i < n; i++)
        dst8[i] = src8[i];
    return dst;
}

void *memmove(void * restrict dst, const void * restrict src, size_t n)
{
    uint8_t *dst8 = (uint8_t *)dst;
    const uint8_t *src8 = (const uint8_t *)src;
    DEBUG("memmove from %p to %p with size %zd", src, dst, n);
    // Check the canary of the destination
    uintptr_t idst = (uintptr_t)dst;
    size_t front_delta = idst % sizeof(uint64_t);
    int check_len = n + front_delta;
    idst -= front_delta;
    size_t end_delta = check_len % sizeof(uint64_t);
    if (end_delta)
        check_len += sizeof(uint64_t);
    check_len /= sizeof(uint64_t);
    uint64_t *dst64 = (uint64_t *)idst;
    for (size_t i = 0; i < check_len; i++) // Check the token of each memory
        if (test_canary(dst64 + i))
            asm ("ud2");
    if (end_delta) {    // Check the token after the current memory for byte-accurate checking
        dst64 += check_len;
        if ((uintptr_t)dst64 % PAGE_SIZE != 0 && test_canary((const uint64_t *)dst64))
        {
            uint64_t token = *dst64;
            if ((token & 0x7) && ((token & 0x7) < end_delta)) { // If the token equals to 0x00, which means 0x08
                asm ("ud2");
            }
        }
    }

    // Check the canary of the source
    uintptr_t isrc = (uintptr_t)src;
    size_t src_front_delta = isrc % sizeof(uint64_t);
    int src_check_len = n + src_front_delta;
    isrc -= src_front_delta;
    size_t src_end_delta = src_check_len % sizeof(uint64_t);
    if (src_end_delta)
        src_check_len += sizeof(uint64_t);
    src_check_len /= sizeof(uint64_t);
    uint64_t *src64 = (uint64_t *)isrc;
    for (size_t i = 0; i < src_check_len; i++) // Check the token of each memory
        if (test_canary(src64 + i))
            asm ("ud2");
    if (src_end_delta) {    // Check the token after the current memory for byte-accurate checking
        src64 += src_check_len;
        if ((uintptr_t)src64 % PAGE_SIZE != 0 && test_canary((const uint64_t *)src64))
        {
            uint64_t token = *src64;
            if ((token & 0x7) && ((token & 0x7) < src_end_delta)) { // If the token equals to 0x00, which means 0x08
                asm ("ud2");
            }
        }
    }


    // Copy the raw data
    if (dst8 < src8) {
        while (n--) {
            *dst8++ = *src8++;
        }
    }
    else {
        uint8_t *lasts = src8 + (n-1);
        uint8_t *lastd = dst8 + (n-1);
        while (n--) {
            *lastd-- = *lasts--;
        }
    }

    return dst;
}

size_t strnlen(const char *s, size_t maxlen)
{
    size_t i;
    for (i = 0; i < maxlen; ++i)
        if (s[i] == '\0')
            break;
    return i;
}

char* strcpy(char *dest, const char *src)
{
    return memcpy (dest, src, strlen(src) + 1);
}

char* strcat(char *dest, const char *src)
{
  strcpy(dest + strlen(dest), src);
  return dest;
}

char* strncpy(char *s1, const char *s2, size_t n)
{
    size_t size = strnlen(s2, n);
    if (size != n)
        memset(s1 + size, '\0', n - size);
    return memcpy(s1, s2, size);
}

char* strncat(char *s1, const char *s2, size_t n)
{
    char *s = s1;
    /* Find the end of S1.  */
    s1 += strlen(s1);
    size_t ss = strnlen(s2, n);
    s1[ss] = '\0';
    memcpy(s1, s2, ss);
    return s;
}

wchar_t* __wmemcpy(wchar_t *s1, const wchar_t *s2, size_t n)
{
  return (wchar_t *) memcpy ((char *) s1, (char *) s2, n * sizeof (wchar_t));
}

size_t __wcslen(const wchar_t *s)
{
  size_t len = 0;
  while (s[len] != L'\0')
    {
      if (s[++len] == L'\0')
        return len;
      if (s[++len] == L'\0')
        return len;
      if (s[++len] == L'\0')
        return len;
      ++len;
    }
  return len;
}

wchar_t* wcscpy(wchar_t *dest, const wchar_t *src)
{
  return __wmemcpy(dest, src, __wcslen(src) + 1);
}

int snprintf(char *dst, size_t n, const char *format, ...)
{
    // Check the canary of the destination
    uintptr_t idst = (uintptr_t)dst;
    size_t front_delta = idst % sizeof(uint64_t);
    int check_len = n + front_delta;
    idst -= front_delta;
    size_t end_delta = check_len % sizeof(uint64_t);
    if (end_delta)
        check_len += sizeof(uint64_t);
    check_len /= sizeof(uint64_t);
    uint64_t *dst64 = (uint64_t *)idst;
    for (size_t i = 0; i < check_len; i++) // Check the token of each memory
        if (test_canary(dst64 + i))
            asm ("ud2");
    if (end_delta) {    // Check the token after the current memory for byte-accurate checking
        dst64 += check_len;
        if ((uintptr_t)dst64 % PAGE_SIZE != 0 && test_canary((const uint64_t *)dst64))
        {
            uint64_t token = *dst64;
            if ((token & 0x7) && ((token & 0x7) < end_delta)) { // If the token equals to 0x00, which means 0x08
                asm ("ud2");
            }
        }
    }

    // do the original work
    va_list arg;
    int done;
    va_start(arg, format);
    done = __vsnprintf(dst, n, format, arg, 0);
    va_end (arg);
    return done;
}

void __attribute__((__constructor__(222))) init(void)
{
    mallopt(M_PERTURB, -1);
}
