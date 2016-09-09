/*
 * Copyright (C) 2016 Red Hat
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#define LOG_TAG "properties_nonandroid"
// #define LOG_NDEBUG 0

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <inttypes.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cutils/properties.h>

/* This file implements a simple flat-file read/write key-value store.
 * It is designed to be safe for writers in different threads and
 * different processes, so that if process A writes key x.y and
 * process B writes key x.z, the result will reliably have both
 * keys. It is also designed so that if a process crashes or is killed
 * while writing a value, the old contents of the file will be left
 * (and possibly a left-over temporary file.)
 *
 * Implementing these semantics without a fancy database-like file
 * format or a central daemon is a bit tricky, and relies on assumptions
 * of the specifics of the interaction between metadata updates and
 * file locking in a way that isn't POSIX specified. See property_set()
 * for the tricky bit.
 *
 * No attempt is made to validate or restrict the keys and the values
 * to match Android system properties; they are treated as arbitrary byte
 * strings subject only to PROPERTY_KEY_MAX and PROPERTY_VALUE_MAX.
 */

typedef struct {
    int ref_count;
    size_t len;
    struct timespec modified_time;
    dev_t device;
    ino_t inode;
    char buf[1];
} Properties ;

typedef struct {
    Properties *properties;
    size_t line_start;
    size_t line_end;
    size_t equals;
    bool at_start;

    char *escaped_key;
    size_t escaped_key_len;
    char *escaped_value;
    size_t escaped_value_len;
} PropertiesIter;

static pthread_mutex_t properties_mutex = PTHREAD_MUTEX_INITIALIZER;
static Properties empty_properties = { 0 };

/* We cache the last contents of the properties database that we
 * used for a read operation, if the (hopefully high-resolution)
 * modification time is unchanged, we don't reread it. The
 * Properties object is checked out as a whole, and replaced,
 * so we can use refcounting to hold onto a copy without holding
 * on to the lock, which is important for property_list. The
 * locking for the refcount itself could be replaced with atomic
 * operations, but the gain would be minimal.
 */
static Properties *cached_properties = &empty_properties;

#ifdef TEST_NON_ANDROID_PROPERTIES
#define PROPERTIES_PATH "test.properties"
#else
#ifndef PROPERTIES_PATH
#error "PROPERTIES_PATH must be defined"
#endif
#endif

static char hexdigit(int i)
{
    if (i < 10)
        return '0' + i;
    else
        return 'a' + (i - 10);
}

static int hexdigit_value(char c)
{
    if (c >= '0' && c <= '9')
        return c - '0';
    else if (c >= 'A' && c <= 'F')
        return 10 + (c - 'A');
    else if (c >= 'a' && c <= 'f')
        return 10 + (c - 'a');
    else {
        assert (1 != 0);
        return 0;
    }
}

static bool is_graph(char c)
{
    return (c > ' ' && c < 127 /* DEL */);
}

static bool is_hexdigit(char c)
{
    return ((c >= '0' && c <= '9') ||
            (c >= 'A' && c <= 'F') ||
            (c >= 'a' && c <= 'f'));
}

static size_t escape(char *res, const char *str, bool escape_equals)
{
    size_t newlen = 0;
    const char *p;
    const char *last_nonspace_p = NULL;
    size_t last_nonspace_newlen = 0;
    bool seen_nonspace = false;

    for (p = str; *p; p++) {
        int c = *((const unsigned char *)p);
        if (c == ' ') {
            if (seen_nonspace) {
                res[newlen++] = ' ';
            } else {
                res[newlen++] = '\\';
                res[newlen++] = ' ';
            }
        } else if (c == '\\' || c == '#' || (escape_equals && c == '=')) {
            res[newlen++] = '\\';
            res[newlen++] = c;
        } else if (c == '\n') {
            res[newlen++] = '\\';
            res[newlen++] = 'n';
        } else if (c == '\t') {
            res[newlen++] = '\\';
            res[newlen++] = 't';
        } else if (is_graph(c)) {
            res[newlen++] = c;
        } else {
            res[newlen++] = '\\';
            res[newlen++] = 'x';
            res[newlen++] = hexdigit((c & 0xf0) >> 4);
            res[newlen++] = hexdigit(c & 0x0f);
        }
        if (c != ' ') {
            seen_nonspace = true;
            last_nonspace_p = p + 1;
            last_nonspace_newlen = newlen;
        }
    }

    if (last_nonspace_p) {
        p = last_nonspace_p;
        newlen = last_nonspace_newlen;
        while (*p++) {
            res[newlen++] = '\\';
            res[newlen++] = ' ';
        }
    }

    res[newlen] = '\0';
    return newlen;
}

static size_t unescape(char *res, size_t res_len, const char *str, size_t len)
{
    size_t newlen = 0;
    const unsigned char *p;

    for (p = (const unsigned char *)str; p < ((const unsigned char *)str + len) && newlen < res_len - 1;) {
        if (p + 3 < (const unsigned char *)str + len &&
            p[0] == '\\' && p[1] == 'x' && is_hexdigit(p[2]) && is_hexdigit(p[3])) {
            ((unsigned char *)res)[newlen] = hexdigit_value(p[2]) * 16 + hexdigit_value(p[3]);
            p += 4;
        } else if (p + 1 < (const unsigned char *)str + len && p[0] == '\\') {
            if (p[1] == 'n')
                res[newlen] = '\n';
            else if (p[1] == 't')
                res[newlen] = '\t';
            else
                res[newlen] = p[1];
            p += 2;
        } else {
            res[newlen] = p[0];
            p += 1;
        }
        newlen++;
    }

    res[newlen] = '\0';
    return newlen;
}

static void release_properties_unlocked(Properties *props)
{
    if (props == &empty_properties)
        return;

    if (--props->ref_count == 0) {
        free(props);
    }
}

static void release_properties(Properties *props)
{
    pthread_mutex_lock(&properties_mutex);
    release_properties_unlocked(props);
    pthread_mutex_unlock(&properties_mutex);
}

static void properties_iter_init (Properties     *props,
                                  PropertiesIter *iter)
{
    iter->properties = props;
    iter->line_start = iter->line_end = iter->equals = 0;
    iter->at_start = true;
}

static bool properties_iter_next (PropertiesIter *iter)
{
    Properties *props = iter->properties;

    while (true) {
        bool escaped, seen_equals;
        char *p;
        char *first_nonwhite, *last_nonwhite;

        if (iter->at_start) {
            iter->at_start = false;
        } else {
            iter->line_start = iter->line_end + 1;
            if (iter->line_start >= props->len)
                return false;
        }

        p = props->buf + iter->line_start;
        while (*p != '\n' && *p != '\0')
            p++;
        iter->line_end = p - props->buf;

        p = props->buf + iter->line_start;

        /* Skip leading white space */
        while (*p == ' ' || *p == '\t')
            p++;
        if (*p == '#') /* comment */
            continue;

        escaped = false;
        seen_equals = false;
        first_nonwhite = last_nonwhite = NULL;
        while (*p != '\n' && *p != '\0') {
            if (!seen_equals && !escaped && *p == '=') {
                if (first_nonwhite) {
                    iter->escaped_key = first_nonwhite;
                    iter->escaped_key_len = last_nonwhite + 1 - first_nonwhite;
                } else {
                    iter->escaped_key = NULL;
                    iter->escaped_key_len = 0;
                }
                first_nonwhite = last_nonwhite = NULL;
                seen_equals = true;
                goto next;
            }

            if (escaped || (*p != ' ' && *p != '\t')) {
                if (first_nonwhite == NULL)
                    first_nonwhite = p;
                last_nonwhite = p;
            }

        next:
            escaped = !escaped && (*p == '\\');
            p++;
        }

        if (!seen_equals)
            continue;

        if (first_nonwhite) {
            iter->escaped_value = first_nonwhite;
            iter->escaped_value_len = last_nonwhite + 1 - first_nonwhite;
        } else {
            iter->escaped_value = NULL;
            iter->escaped_value_len = 0;
        }
        return true;
    }
}

static bool properties_iter_equal(PropertiesIter *iter,
                                  const char     *escaped_key,
                                  size_t          escaped_key_len)
{
    if (escaped_key_len != iter->escaped_key_len)
        return false;

    return memcmp(iter->escaped_key, escaped_key, escaped_key_len) == 0;
}

static Properties *read_properties (int fd)
{
    struct stat buf;
    size_t alloc_size;
    Properties *props = NULL;
    size_t pos;

    if (fstat(fd, &buf) == -1)
        goto err;

    alloc_size = offsetof(Properties, buf);
    if ((off_t)(size_t)buf.st_size != buf.st_size ||
        alloc_size + (size_t)buf.st_size < alloc_size) {
        goto err;
    }

    alloc_size += buf.st_size;
    props = malloc(alloc_size + 1);
    if (!props)
        goto err;

    props->ref_count = 1;
    props->len = buf.st_size;
    props->modified_time = buf.st_mtim;
    props->device = buf.st_dev;
    props->inode = buf.st_ino;

    pos = 0;
    while (pos < props->len) {
        int l = read(fd, props->buf + pos, props->len - pos);
        if (l == -1) {
            if (errno != EINTR)
                goto err;
        } else if (l == 0) {
            /* Unexpectedly truncated */
            props->len = pos;
            break;
        } else {
            pos += l;
        }
    }
    props->buf[props->len] = '\0';

    return props;

err:
    free(props);
    return NULL;
}

static Properties *get_properties(void)
{
    struct stat buf;
    Properties *new_props = NULL;
    Properties *res = NULL;
    int fd = -1;

    pthread_mutex_lock(&properties_mutex);

    if (stat (PROPERTIES_PATH, &buf) == -1) {
        if (errno != ENOENT)
            perror("Cannot stat " PROPERTIES_PATH);

        goto out;
    } else {
        if (memcmp(&buf.st_mtim, &cached_properties->modified_time, sizeof(buf.st_mtim)) == 0) {
            goto out;
        }
    }

    fd = open(PROPERTIES_PATH, O_RDONLY);
    if (fd < 0) {
        perror("Cannot open " PROPERTIES_PATH);
        goto out;
    }

    new_props = read_properties(fd);
    if (new_props) {
        release_properties_unlocked(cached_properties);
        cached_properties = new_props;
    }

out:
    if (fd != -1)
        close(fd);

    res = cached_properties;
    res->ref_count++;

    pthread_mutex_unlock(&properties_mutex);
    return res;
}

ssize_t write_all(int fd, const void *buf, size_t count)
{
    size_t pos = 0;
    while (pos < count) {
        ssize_t l = write(fd, buf + pos, count - pos);
        if (l == -1) {
            perror("Error writing properties file");
            if (errno != EINTR)
                return -1;
        } else {
            pos += l;
        }
    }

    return count;
}

int property_set(const char *key, const char *value)
{
    Properties *props;
    PropertiesIter iter;
    char escaped_key[PROPERTY_KEY_MAX * 4];
    size_t escaped_key_len;
    char escaped_value[PROPERTY_VALUE_MAX * 4];
    size_t escaped_value_len;
    int res = -1;
    int fd = - 1;
    int new_fd = -1;
    int update_start, update_end;
    char template[] = PROPERTIES_PATH ".XXXXXX";
    bool unlink_tempfile = false;

    if (strlen(key) > PROPERTY_KEY_MAX - 1)
        return -1;
    if (strlen(value) > PROPERTY_VALUE_MAX - 1)
        return -1;

    escaped_key_len = escape(escaped_key, key, true);
    escaped_value_len = escape(escaped_value, value, false);

    /* We want to do a read/modify/write operation on the properties
     * file that is atomic with respect to anybody else doing the
     * same thing. We can't *just* use file locking, because the file
     * is going to be atomically replaced during the operation, but
     * locking the file we want to replace, combined with some careful
     * ordering does the trick.
     */
    while (true) {
        /* First, open the file and get an exclusive lock on it */
        fd = open(PROPERTIES_PATH, O_RDWR);
        if (fd == -1) {
            if (errno != ENOENT) {
                perror("Can't open " PROPERTIES_PATH);
                goto out;
            }

            /* File doesn't exist yet. This screws up our locking
             * scheme, so create an empty file, and try again.
             */
            fd = open(PROPERTIES_PATH, O_RDWR | O_CREAT, 0644);
            if (fd == -1) {
                perror("Can't create " PROPERTIES_PATH);
                goto out;
            }
            (void)close (fd);

        } else {
            struct stat buf;

            while (true) {
                if (flock (fd, LOCK_EX) == 0)
                    break;

                if (errno != EINTR) {
                    perror("Can't lock " PROPERTIES_PATH);
                    goto out;
                }
            }

            /* OK, we have the file locked. We need to make sure that
             * some other process didn't get a lock first and replace
             * the file.
             */
            props = read_properties(fd);
            if (props == NULL)
                goto out;

            if (stat(PROPERTIES_PATH, &buf) == -1) {
                perror ("Error rechecking " PROPERTIES_PATH);
                goto out;
            }
            if (buf.st_dev != props->device || buf.st_ino != props->inode) {
                /* File was replaced, start over */
                close(fd);
                release_properties(props);
                props = NULL;
            }

            break;
        }
    }

    /* As the holder of the lock, we can go ahead and replace the file.
     * See if there is an existing line to replace
     */
    properties_iter_init(props, &iter);
    while (properties_iter_next(&iter)) {
        if (properties_iter_equal(&iter, escaped_key, escaped_key_len)) {
            update_start = iter.line_start;
            update_end = iter.line_end + 1;
            if (update_end > props->len)
                update_end = props->len;
            goto found;
        }
    }

    update_start = props->len;
    update_end = props->len;

found:
    new_fd = mkstemp(template);
    if (new_fd == -1) {
        perror("Error creating temporary file");
        goto out;
    }
    unlink_tempfile = true;

    if (fchmod(new_fd, 0644) == -1) {
        perror("Error setting permissions of temporary file");
        goto out;
    }

    if (write_all(new_fd, props->buf, update_start) == -1)
        goto out;
    if (update_start == props->len && props->len > 0 &&
        props->buf[props->len -1 ] != '\n' && props->buf[props->len - 1] != '\0' &&
        write_all(new_fd, "\n", 1) == -1)
        goto out;
    if (write_all(new_fd, escaped_key, escaped_key_len) == -1)
        goto out;
    if (write_all(new_fd, "=", 1) == -1)
        goto out;
    if (write_all(new_fd, escaped_value, escaped_value_len) == -1)
        goto out;
    if (write_all(new_fd, "\n", 1) == -1)
        goto out;
    if (write_all(new_fd, props->buf + update_end, props->len - update_end) == -1)
        goto out;

    if (close(new_fd) == -1) {
        perror("Error writing temporary file");
        goto out;
    }
    new_fd = -1;

    if (rename(template, PROPERTIES_PATH) == -1) {
        perror("Error replacing " PROPERTIES_PATH);
        goto out;
    }

    unlink_tempfile = false;

    /* Make sure that a subsequent call to property_get() rereads the
     * new data, even if the mtime didn't change */
    pthread_mutex_lock(&properties_mutex);
    release_properties_unlocked(cached_properties);
    cached_properties = &empty_properties;
    pthread_mutex_unlock(&properties_mutex);

    res = 0;

out:
    if (fd != -1)
        close(fd); /* Releases lock */
    if (new_fd != -1)
        close(fd);
    if (unlink_tempfile)
        unlink(template);

    return res;
}

int property_get(const char *key, char *value, const char *default_value)
{
    Properties *props = get_properties();
    char escaped_key[PROPERTY_KEY_MAX * 4];
    size_t escaped_key_len;
    PropertiesIter iter;
    int len = -1;

    escaped_key_len = escape(escaped_key, key, true);
    properties_iter_init(props, &iter);
    while (properties_iter_next(&iter)) {
        if (properties_iter_equal(&iter, escaped_key, escaped_key_len)) {
            len = unescape(value, PROPERTY_VALUE_MAX,
                           iter.escaped_value, iter.escaped_value_len);
            break;
        }
    }

    if (len < 0 && default_value) {
        len = strlen(default_value);
        if (len > PROPERTY_VALUE_MAX - 1)
            len = PROPERTY_VALUE_MAX - 1;
        memcpy(value, default_value, len);
        value[len] = '\0';
    }

    release_properties(props);

    return len;
}

struct property_list_callback_data
{
    void (*propfn)(const char *key, const char *value, void *cookie);
    void *cookie;
};

int property_list(
        void (*propfn)(const char *key, const char *value, void *cookie),
        void *cookie)
{
    Properties *props = get_properties();
    PropertiesIter iter;
    char key[PROPERTY_KEY_MAX];
    char value[PROPERTY_VALUE_MAX];

    properties_iter_init(props, &iter);
    while (properties_iter_next(&iter)) {
        unescape(key, sizeof(key), iter.escaped_key, iter.escaped_key_len);
        unescape(value, sizeof(value), iter.escaped_value, iter.escaped_value_len);
        propfn(key, value, cookie);
    }

    release_properties(props);

    return 0;
}

#ifdef TEST_NON_ANDROID_PROPERTIES
void assert_get(char *key, char *value) {
    char result[PROPERTY_KEY_MAX];
    property_get(key, result, "UNSET");
    if (strcmp(result, value) != 0) {
        fprintf(stderr, "%s: expected '%s', got '%s'\n",
                key, value, result);
        exit(1);
    }
}

void assert_set_get(char *key, char *value) {
    property_set(key, value);
    assert_get(key, value);
}

void assert_unset(char *key) {
    char result[PROPERTY_KEY_MAX];
    property_get(key, result, "UNSET");
    if (strcmp(result, "UNSET") != 0) {
        fprintf(stderr, "%s: expected unset, got %s\n",
                key, result);
        exit(1);
    }
}

int main(int argc, char **argv)
{
    static char content[] = \
        "# A comment\n" \
        "#=Foo\n" \
        "#=Foo\n" \
        " a = b \n" \
        " a\\  = b\\  \n";
    int fd;

    assert_set_get("foo", "bar");
    assert_set_get("foo", "barbar");

    fd = open("test.properties", O_WRONLY | O_APPEND);
    write(fd, content, strlen(content));
    assert_unset("#");
    assert_unset(" #");
    assert_get("a", "b");
    assert_get("a ", "b ");
    assert_set_get("", "");
    assert_set_get(" ", " ");
    assert_set_get("  foo bar  ", "  foo bar  ");

    assert_set_get("foo.bar", "BAH");
    assert_set_get("escaped", "\x01\n\t#");
    assert_set_get("=", "=");
    assert_set_get("#", "Not a comment");
    assert_set_get("#", "Not a comment");
    assert_set_get("\\", "Backslash");
    assert_set_get("foo.bar.a", "\n");
    assert_set_get("foo.bar.b", "\t");

    return 0;
}
#endif
