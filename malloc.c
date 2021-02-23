
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <malloc.h>

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

static void *quarantine[QUARANTINE_MAX] = {NULL};
static size_t quarantine_ptr = 0;
static pthread_mutex_t quarantine_lock = PTHREAD_MUTEX_INITIALIZER;

void set_canary(uint64_t *ptr64);
bool test_canary(const uint64_t *ptr64);

asm (
    ".type set_canary, @function\n"
    ".globl set_canary\n"
    "set_canary:\n"
    "\tmov %fs:40, %rax\n"
    "\tmov %rax,(%rdi)\n"
    "\tnegq (%rdi)\n"
    "\txor %eax,%eax\n"
    "\tretq\n"

    ".type test_canary, @function\n"
    ".globl test_canary\n"
    "test_canary:\n"
    "\tmov %fs:40, %rax\n"
    "\tmov (%rdi),%rdi\n"
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
    size_t size_0 = size;
    size += sizeof(uint64_t);
    if (size % sizeof(uint64_t) != 0)
        size += sizeof(uint64_t) - size % sizeof(uint64_t);
    void *ptr = __libc_malloc(size);
    if (ptr == NULL)
        return ptr;
    uint64_t *ptr64 = (uint64_t *)ptr;
    ptr64 += (size / sizeof(uint64_t)) - 1;
    set_canary(ptr64);

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
    if (ptr == NULL)
        return malloc(size);

    size_t old_size = malloc_usable_size(ptr);
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
        reset_canary(new_ptr64 + i);
//        assert(!test_canary(new_ptr64 + i));
    }

    uint8_t *old_ptr8 = (uint8_t *)old_ptr;
    uint8_t *new_ptr8 = (uint8_t *)new_ptr;
    for (size_t i = copy_size64 * sizeof(uint64_t); i < copy_size; i++)
    {
        new_ptr8[i] = old_ptr8[i];
    }
    if (copy_size > copy_size64 * sizeof(uint64_t))
        reset_canary(new_ptr64 + copy_size64);

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
        set_canary(ptr64 + i);

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

void *memcpy(void * restrict dst, const void * restrict src, size_t n)
{
    uint8_t *dst8 = (uint8_t *)dst;
    const uint8_t *src8 = (const uint8_t *)src;
    for (size_t i = 0; i < n; i++)
        dst8[i] = src8[i];

    uintptr_t idst = (uintptr_t)dst;
    size_t delta =
        (idst % sizeof(uint64_t) == 0? 0: sizeof(uint64_t) - idst % sizeof(uint64_t));
    if (n <= delta)
        return dst;
    n -= delta;
    idst += delta;
    uint64_t *dst64 = (uint64_t *)idst;
    for (size_t i = 0; i < n / sizeof(uint64_t); i++)
        if (test_canary(dst64 + i))
            asm ("int3");
    return dst;
}

void __attribute__((__constructor__(222))) init(void)
{
    mallopt(M_PERTURB, -1);
}
