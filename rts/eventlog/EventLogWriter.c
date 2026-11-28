/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2008-2009
 *
 * Support for fast binary event logging.
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "rts/EventLogWriter.h"

#include <string.h>
#include <stdio.h>
#include <fs_rts.h>
#if defined(HAVE_SYS_TYPES_H)
#include <sys/types.h>
#endif
#if defined(HAVE_UNISTD_H)
#include <unistd.h>
#endif

#if !defined(USE_RUST_RTS)
// PID of the process that writes to event_log_filename (#4512)
static pid_t event_log_pid = -1;

// File for logging events
static FILE *event_log_file = NULL;
#endif

#if defined(THREADED_RTS)
// Protects event_log_file
static Mutex event_log_mutex;

static void acquire_event_log_lock(void) { ACQUIRE_LOCK(&event_log_mutex); }
static void release_event_log_lock(void) { RELEASE_LOCK(&event_log_mutex); }
#else
static void acquire_event_log_lock(void) {}
static void release_event_log_lock(void) {}
#endif

#if !defined(USE_RUST_RTS)
static char *outputFileName(void)
{

    if (RtsFlags.TraceFlags.trace_output) {
        return strdup(RtsFlags.TraceFlags.trace_output);
    } else {
        char *prog = stgMallocBytes(strlen(prog_name) + 1,
                                    "initEventLogFileWriter");
        strcpy(prog, prog_name);
#if defined(mingw32_HOST_OS)
        // on Windows, drop the .exe suffix if there is one
        {
            char *suff;
            suff = strrchr(prog,'.');
            if (suff != NULL && !strcmp(suff,".exe")) {
                *suff = '\0';
            }
        }
#endif
        char *filename = stgMallocBytes(strlen(prog)
                                        + 10 /* .%d */
                                        + 10 /* .eventlog */,
                                        "initEventLogFileWriter");

#if !defined(HAVE_GETPID)
            sprintf(filename, "%s.eventlog", prog);
#else
        if (event_log_pid == -1) { // #4512
            // Single process
            sprintf(filename, "%s.eventlog", prog);
            event_log_pid = getpid();
        } else {
            // Forked process, eventlog already started by the parent
            // before fork
            event_log_pid = getpid();
            // We don't have a FMT* symbol for pid_t, so we go via Word64
            // to be sure of not losing range. It would be nicer to have a
            // FMT* symbol or similar, though.
            sprintf(filename, "%s.%" FMT_Word64 ".eventlog",
                    prog, (StgWord64)event_log_pid);
        }
#endif
        stgFree(prog);
        return filename;
    }
}

#endif

#if !defined(USE_RUST_RTS)
static FILE *
openEventLogFile(char *event_log_filename)
{
    /* Open event log file for writing. */
    FILE *file = __rts_fopen(event_log_filename, "wb+");
    if (file == NULL) {
        sysErrorBelch(
            "initEventLogFileWriter: can't open %s", event_log_filename);
        stg_exit(EXIT_FAILURE);
    }

    stgFree(event_log_filename);
#if defined(THREADED_RTS)
    initMutex(&event_log_mutex);
#endif
    return file;
}
#endif

#if defined(USE_RUST_RTS)
RTS_PRIVATE void ghc_rust_eventlog_init(const char *program, const char *output);
RTS_PRIVATE bool ghc_rust_eventlog_write(void *eventlog, size_t eventlog_size);
RTS_PRIVATE void ghc_rust_eventlog_flush(void);
RTS_PRIVATE void ghc_rust_eventlog_stop(void);

RTS_PRIVATE void ghc_rust_eventlog_open_failed(const char *filename) STG_NORETURN;
RTS_PRIVATE void ghc_rust_eventlog_init_mutex(void);
RTS_PRIVATE void ghc_rust_eventlog_acquire(void);
RTS_PRIVATE void ghc_rust_eventlog_release(void);
RTS_PRIVATE void ghc_rust_eventlog_close_mutex(void);

RTS_PRIVATE void ghc_rust_eventlog_open_failed(const char *filename)
{
    sysErrorBelch("initEventLogFileWriter: can't open %s", filename);
    stg_exit(EXIT_FAILURE);
}

RTS_PRIVATE void ghc_rust_eventlog_init_mutex(void)
{
#if defined(THREADED_RTS)
    initMutex(&event_log_mutex);
#endif
}

RTS_PRIVATE void ghc_rust_eventlog_acquire(void)
{
    acquire_event_log_lock();
}

RTS_PRIVATE void ghc_rust_eventlog_release(void)
{
    release_event_log_lock();
}

RTS_PRIVATE void ghc_rust_eventlog_close_mutex(void)
{
#if defined(THREADED_RTS)
    closeMutex(&event_log_mutex);
#endif
}
#else
static void flushEventLogFile(void);
#endif

static void
initEventLogFileWriter(void)
{
#if defined(USE_RUST_RTS)
    ghc_rust_eventlog_init(prog_name, RtsFlags.TraceFlags.trace_output);
#else
    event_log_file = openEventLogFile(outputFileName());
#endif
}

#if !defined(USE_RUST_RTS)
static bool
writeEventLogFile(void *eventlog, size_t eventlog_size)
{
    unsigned char *begin = eventlog;
    size_t remain = eventlog_size;

    acquire_event_log_lock();
    while (remain > 0) {
        size_t written = fwrite(begin, 1, remain, event_log_file);
        if (written == 0) {
            release_event_log_lock();
            return false;
        }
        remain -= written;
        begin += written;
    }
    release_event_log_lock();

    flushEventLogFile ();
    return true;
}

static void
flushEventLogFile(void)
{
    if (event_log_file != NULL) {
        fflush(event_log_file);
    }
}

static void
stopEventLogFileWriter(void)
{
    if (event_log_file != NULL) {
        fclose(event_log_file);
        event_log_file = NULL;
    }
#if defined(THREADED_RTS)
    closeMutex(&event_log_mutex);
#endif
}

#endif

static void
initEventLogFileWriterNoop(void) {}

static bool
writeEventLogFileNoop(void *eventlog STG_UNUSED, size_t eventlog_size STG_UNUSED) {
    return true; // writes succeed always
}

static void
flushEventLogFileNoop(void) {}

static void
stopEventLogFileWriterNoop(void) {}

const EventLogWriter FileEventLogWriter = {
    .initEventLogWriter = initEventLogFileWriter,
#if defined(USE_RUST_RTS)
    .writeEventLog = ghc_rust_eventlog_write,
    .flushEventLog = ghc_rust_eventlog_flush,
    .stopEventLogWriter = ghc_rust_eventlog_stop
#else
    .writeEventLog = writeEventLogFile,
    .flushEventLog = flushEventLogFile,
    .stopEventLogWriter = stopEventLogFileWriter
#endif
};

const EventLogWriter NullEventLogWriter = {
    .initEventLogWriter = initEventLogFileWriterNoop,
    .writeEventLog = writeEventLogFileNoop,
    .flushEventLog = flushEventLogFileNoop,
    .stopEventLogWriter = stopEventLogFileWriterNoop
};
