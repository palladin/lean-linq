/* FreeTDS DB-Library → Lean ABI shim for the lean-linq native SQL Server
 * driver.
 *
 * dblib requires global error/message handlers — without them it prints to
 * stderr and may abort the process. The handlers route the latest text to
 * the connection that caused it (dbgetuserdata), falling back to
 * mutex-guarded globals during connect (no DBPROCESS/userdata yet); any
 * FAIL raises a Lean IO userError carrying the captured text. Distinct
 * connections are therefore safe to use from distinct threads; a single
 * connection is one-request-at-a-time (TDS) — per-Conn exclusivity is the
 * caller's contract.
 *
 * The login forces TDS 7.1, so datetime2 columns arrive as nvarchar text
 * on the wire; every result cell is read via dbconvert(coltype → SYBCHAR)
 * and parsed by the shared Lean text decoders. */

#include <lean/lean.h>
#include <sybfront.h>
#include <sybdb.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- error capture ---------- */

typedef struct {
    DBPROCESS *dbproc;
    char err[1024];
    char msg[1024];
    /* malloc'd copies of RPC parameter values: dbrpcparam stores the raw
     * pointer and serializes only inside dbrpcsend, so the buffers must
     * outlive the whole build-send window (Lean frees its strings as soon
     * as the param call returns). Cleared after send and on reset/close. */
    char **rpc_vals;
    size_t rpc_nvals;
    size_t rpc_cap;
} ll_tdsconn;

static void ll_tds_rpc_vals_clear(ll_tdsconn *c) {
    for (size_t k = 0; k < c->rpc_nvals; k++) free(c->rpc_vals[k]);
    free(c->rpc_vals);
    c->rpc_vals = NULL;
    c->rpc_nvals = 0;
    c->rpc_cap = 0;
}

static char *ll_tds_rpc_vals_push(ll_tdsconn *c, const char *src, size_t len) {
    if (c->rpc_nvals == c->rpc_cap) {
        size_t cap = c->rpc_cap ? c->rpc_cap * 2 : 8;
        char **vs = (char **)realloc(c->rpc_vals, cap * sizeof(char *));
        if (!vs) return NULL;
        c->rpc_vals = vs;
        c->rpc_cap = cap;
    }
    char *copy = (char *)malloc(len + 1);
    if (!copy) return NULL;
    memcpy(copy, src, len + 1);
    c->rpc_vals[c->rpc_nvals++] = copy;
    return copy;
}

/* Connect-time errors only (no DBPROCESS/userdata exists yet). */
static pthread_mutex_t g_conn_err_lock = PTHREAD_MUTEX_INITIALIZER;
static char g_err[1024] = "";
static char g_msg[1024] = "";

static int ll_tds_err_handler(DBPROCESS *dbproc, int severity, int dberr,
                              int oserr, char *dberrstr, char *oserrstr) {
    (void)severity; (void)dberr; (void)oserr; (void)oserrstr;
    if (!dberrstr) return INT_CANCEL;
    ll_tdsconn *c = dbproc ? (ll_tdsconn *)dbgetuserdata(dbproc) : NULL;
    if (c) {
        snprintf(c->err, sizeof(c->err), "%s", dberrstr);
    } else {
        pthread_mutex_lock(&g_conn_err_lock);
        snprintf(g_err, sizeof(g_err), "%s", dberrstr);
        pthread_mutex_unlock(&g_conn_err_lock);
    }
    return INT_CANCEL;
}

static int ll_tds_msg_handler(DBPROCESS *dbproc, DBINT msgno, int msgstate,
                              int severity, char *msgtext, char *srvname,
                              char *procname, int line) {
    (void)msgno; (void)msgstate; (void)srvname; (void)procname; (void)line;
    if (severity <= 0 || !msgtext) return 0;
    ll_tdsconn *c = dbproc ? (ll_tdsconn *)dbgetuserdata(dbproc) : NULL;
    if (c) {
        snprintf(c->msg, sizeof(c->msg), "%s", msgtext);
    } else {
        pthread_mutex_lock(&g_conn_err_lock);
        snprintf(g_msg, sizeof(g_msg), "%s", msgtext);
        pthread_mutex_unlock(&g_conn_err_lock);
    }
    return 0;
}

static pthread_once_t g_init_once = PTHREAD_ONCE_INIT;
static int g_init_ok = 0;

static void ll_tds_init_once(void) {
    if (dbinit() == FAIL) return;
    dberrhandle(ll_tds_err_handler);
    dbmsghandle(ll_tds_msg_handler);
    dbsetlogintime(10);
    g_init_ok = 1;
}

static int ll_tds_init(void) {
    pthread_once(&g_init_once, ll_tds_init_once);
    return g_init_ok;
}

/* Raise IO userError from the buffers that captured the failure: the
 * connection's own when it exists, else the guarded connect-time globals. */
static lean_obj_res ll_tds_err(ll_tdsconn *c, const char *what) {
    char buf[2200];
    char *err = c ? c->err : g_err;
    char *msg = c ? c->msg : g_msg;
    if (!c) pthread_mutex_lock(&g_conn_err_lock);
    snprintf(buf, sizeof(buf), "freetds %s: %s%s%s", what, err,
             (err[0] && msg[0]) ? " | " : "", msg);
    err[0] = 0;
    msg[0] = 0;
    if (!c) pthread_mutex_unlock(&g_conn_err_lock);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

/* ---------- connection external ---------- */

static lean_external_class *g_tdsconn_class = NULL;
static pthread_once_t g_class_once = PTHREAD_ONCE_INIT;

static void ll_tdsconn_finalize(void *ptr) {
    ll_tdsconn *c = (ll_tdsconn *)ptr;
    if (c->dbproc) dbclose(c->dbproc);
    ll_tds_rpc_vals_clear(c);
    free(c);
}

static void ll_tds_noop_foreach(void *ptr, b_lean_obj_arg fn) { (void)ptr; (void)fn; }

static void ll_tdsconn_register_class(void) {
    g_tdsconn_class = lean_register_external_class(ll_tdsconn_finalize,
                                                   ll_tds_noop_foreach);
}

static lean_external_class *tdsconn_class(void) {
    pthread_once(&g_class_once, ll_tdsconn_register_class);
    return g_tdsconn_class;
}

static inline ll_tdsconn *tdsconn_of(b_lean_obj_arg o) {
    return (ll_tdsconn *)lean_get_external_data(o);
}

/* connect : (server="host:port") → user → pass → (db, "" = none) → IO MsConn */
LEAN_EXPORT lean_obj_res ll_tds_connect(b_lean_obj_arg server, b_lean_obj_arg user,
                                        b_lean_obj_arg pass, b_lean_obj_arg db,
                                        lean_obj_arg w) {
    (void)w;
    if (!ll_tds_init()) return ll_tds_err(NULL, "init");
    LOGINREC *login = dblogin();
    if (!login) return ll_tds_err(NULL, "login alloc");
    DBSETLUSER(login, lean_string_cstr(user));
    DBSETLPWD(login, lean_string_cstr(pass));
    DBSETLCHARSET(login, "UTF-8");
    DBSETLVERSION(login, DBVERSION_71); /* datetime2 arrives as nvarchar text */
    DBPROCESS *dbproc = dbopen(login, lean_string_cstr(server));
    dbloginfree(login);
    if (!dbproc) return ll_tds_err(NULL, "connect");
    ll_tdsconn *c = (ll_tdsconn *)malloc(sizeof(ll_tdsconn));
    if (!c) { dbclose(dbproc); return ll_tds_err(NULL, "conn alloc"); }
    c->dbproc = dbproc;
    c->err[0] = 0;
    c->msg[0] = 0;
    c->rpc_vals = NULL;
    c->rpc_nvals = 0;
    c->rpc_cap = 0;
    dbsetuserdata(dbproc, (BYTE *)c); /* route this connection's errors to c */
    if (lean_string_size(db) > 1) { /* non-empty */
        if (dbuse(dbproc, lean_string_cstr(db)) == FAIL) {
            lean_obj_res e = ll_tds_err(c, "use database");
            dbclose(dbproc);
            free(c);
            return e;
        }
    }
    return lean_io_result_mk_ok(lean_alloc_external(tdsconn_class(), c));
}

/* close : MsConn → IO Unit */
LEAN_EXPORT lean_obj_res ll_tds_close(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    if (c->dbproc) {
        dbclose(c->dbproc);
        c->dbproc = NULL;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_obj_res ll_tds_check_conn(ll_tdsconn *c, const char *what) {
    if (!c->dbproc) {
        char buf[128];
        snprintf(buf, sizeof(buf), "freetds %s: connection is closed", what);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
    }
    /* a *successful* prior command may have left an informational message
     * (severity 10); drop it so it cannot decorate an unrelated later error */
    c->msg[0] = 0;
    return NULL;
}

/* drain every pending result set */
static RETCODE drain_results(DBPROCESS *dbproc) {
    RETCODE r, r2;
    while ((r = dbresults(dbproc)) != NO_MORE_RESULTS) {
        if (r == FAIL) return FAIL;
        while ((r2 = dbnextrow(dbproc)) != NO_MORE_ROWS) {
            if (r2 == FAIL) return FAIL; /* dead connection: don't spin */
        }
    }
    return SUCCEED;
}

/* execRaw : MsConn → String → IO Unit (multi-statement batches, drained) */
LEAN_EXPORT lean_obj_res ll_tds_exec_raw(b_lean_obj_arg conn, b_lean_obj_arg sql,
                                         lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    lean_obj_res bad = ll_tds_check_conn(c, "exec");
    if (bad) return bad;
    dbcancel(c->dbproc);
    if (dbcmd(c->dbproc, lean_string_cstr(sql)) == FAIL)
        return ll_tds_err(c, "dbcmd");
    if (dbsqlexec(c->dbproc) == FAIL) return ll_tds_err(c, "exec");
    if (drain_results(c->dbproc) == FAIL) return ll_tds_err(c, "exec results");
    return lean_io_result_mk_ok(lean_box(0));
}

/* sendBatch : MsConn → String → IO Unit — like execRaw but leaves the
 * result sets readable (resultsNext/rowNext); the empty-string fallback
 * path sends `EXEC sp_executesql ...` batches through here. */
LEAN_EXPORT lean_obj_res ll_tds_send_batch(b_lean_obj_arg conn, b_lean_obj_arg sql,
                                           lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    lean_obj_res bad = ll_tds_check_conn(c, "batch");
    if (bad) return bad;
    dbcancel(c->dbproc);
    if (dbcmd(c->dbproc, lean_string_cstr(sql)) == FAIL)
        return ll_tds_err(c, "dbcmd");
    if (dbsqlexec(c->dbproc) == FAIL) return ll_tds_err(c, "batch exec");
    return lean_io_result_mk_ok(lean_box(0));
}

/* ---------- sp_executesql RPC ---------- */

/* rpcBegin : MsConn → String → IO Unit */
LEAN_EXPORT lean_obj_res ll_tds_rpc_begin(b_lean_obj_arg conn, b_lean_obj_arg proc,
                                          lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    lean_obj_res bad = ll_tds_check_conn(c, "rpc");
    if (bad) return bad;
    dbcancel(c->dbproc);
    /* a throw between a previous rpcBegin and rpcSend leaves a half-built
     * RPC queued (dbcancel does not clear it); reset before building anew */
    dbrpcinit(c->dbproc, (char *)"", DBRPCRESET);
    ll_tds_rpc_vals_clear(c);
    if (dbrpcinit(c->dbproc, (char *)lean_string_cstr(proc), 0) == FAIL)
        return ll_tds_err(c, "rpcinit");
    return lean_io_result_mk_ok(lean_box(0));
}

/* rpcParamText : MsConn → String → Bool(wide) → Bool(isNull) → String → IO Unit
 * dbrpcparam sends most type tokens verbatim (SYBNVARCHAR 0x67 is
 * Sybase-only — SQL Server rejects the stream), so the two wire-legal text
 * forms are selected here: wide = SYBNTEXT for sp_executesql's @stmt/@params
 * (which must be ntext/nchar/nvarchar, at any length), narrow = SYBVARCHAR
 * for the parameter values, which the server implicitly converts to the
 * types the declaration string names (ntext would not convert to int).
 * FreeTDS itself promotes SYBVARCHAR to XSYBNVARCHAR for TDS7+ at ≤ 4000
 * bytes (rpc.c), so values are true nvarchar on the wire, UTF-8 converted.
 * One API limitation is load-bearing: dbrpcparam erases the value pointer
 * when datalen is 0, so an empty string CANNOT be sent as an RPC parameter
 * (it arrives NULL) — the driver falls back to a batch for those. */
LEAN_EXPORT lean_obj_res ll_tds_rpc_param_text(b_lean_obj_arg conn, b_lean_obj_arg name,
                                               uint8_t wide, uint8_t isNull,
                                               b_lean_obj_arg value, lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    lean_obj_res bad = ll_tds_check_conn(c, "rpcparam");
    if (bad) return bad;
    int type = wide ? SYBNTEXT : SYBVARCHAR;
    RETCODE r;
    if (isNull) {
        r = dbrpcparam(c->dbproc, (char *)lean_string_cstr(name), 0,
                       type, -1, 0, NULL);
    } else {
        size_t len = lean_string_size(value) - 1;
        char *copy = ll_tds_rpc_vals_push(c, lean_string_cstr(value), len);
        if (!copy) return ll_tds_err(c, "rpcparam alloc");
        r = dbrpcparam(c->dbproc, (char *)lean_string_cstr(name), 0,
                       type, -1, (DBINT)len, (BYTE *)copy);
    }
    if (r == FAIL) return ll_tds_err(c, "rpcparam");
    return lean_io_result_mk_ok(lean_box(0));
}

/* rpcSend : MsConn → IO Unit */
LEAN_EXPORT lean_obj_res ll_tds_count(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    DBPROCESS *dbproc = tdsconn_of(conn)->dbproc;
    DBINT n = DBCOUNT(dbproc);
    if (n < 0) n = 0;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)n));
}

LEAN_EXPORT lean_obj_res ll_tds_rpc_send(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    lean_obj_res bad = ll_tds_check_conn(c, "rpcsend");
    if (bad) return bad;
    if (dbrpcsend(c->dbproc) == FAIL) {
        ll_tds_rpc_vals_clear(c);
        return ll_tds_err(c, "rpcsend");
    }
    ll_tds_rpc_vals_clear(c); /* serialized into the TDS stream by dbrpcsend */
    if (dbsqlok(c->dbproc) == FAIL) return ll_tds_err(c, "rpc sqlok");
    return lean_io_result_mk_ok(lean_box(0));
}

/* ---------- results ---------- */

/* resultsNext : MsConn → IO UInt32 — 1 = a result set follows, 0 = done */
LEAN_EXPORT lean_obj_res ll_tds_results_next(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    RETCODE r = dbresults(c->dbproc);
    if (r == NO_MORE_RESULTS)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    if (r == FAIL) return ll_tds_err(c, "results");
    return lean_io_result_mk_ok(lean_box_uint32(1));
}

/* rowNext : MsConn → IO UInt32 — 1 = row available, 0 = no more rows */
LEAN_EXPORT lean_obj_res ll_tds_row_next(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    RETCODE r = dbnextrow(c->dbproc);
    if (r == NO_MORE_ROWS)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    if (r == FAIL) return ll_tds_err(c, "nextrow");
    return lean_io_result_mk_ok(lean_box_uint32(1));
}

/* colCount : MsConn → IO UInt32 */
LEAN_EXPORT lean_obj_res ll_tds_col_count(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)dbnumcols(c->dbproc)));
}

/* colIsNull : MsConn → UInt32 → IO Bool (columns are 0-based on the Lean side) */
LEAN_EXPORT lean_obj_res ll_tds_col_is_null(b_lean_obj_arg conn, uint32_t i,
                                            lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    BYTE *data = dbdata(c->dbproc, (int)i + 1);
    return lean_io_result_mk_ok(lean_box(data == NULL ? 1 : 0));
}

/* colText : MsConn → UInt32 → IO String — dbconvert(coltype → SYBCHAR) */
LEAN_EXPORT lean_obj_res ll_tds_col_text(b_lean_obj_arg conn, uint32_t i,
                                         lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    int col = (int)i + 1;
    BYTE *data = dbdata(c->dbproc, col);
    if (!data) return lean_io_result_mk_ok(lean_mk_string(""));
    int type = dbcoltype(c->dbproc, col);
    DBINT len = dbdatlen(c->dbproc, col);
    /* UCS-2 → UTF-8 expands at most 1.5×; fixed-width types (money,
     * datetime, decimal) render well under 256 — 2×len + 64 covers all */
    size_t cap = (size_t)(len > 0 ? (size_t)len * 2 + 64 : 0);
    if (cap < 256) cap = 256;
    char sbuf[4096];
    char *buf = cap <= sizeof(sbuf) ? sbuf : (char *)malloc(cap);
    if (!buf) return ll_tds_err(c, "convert alloc");
    DBINT n = dbconvert(c->dbproc, type, data, len, SYBCHAR,
                        (BYTE *)buf, (DBINT)(cap - 1));
    if (n < 0) {
        if (buf != sbuf) free(buf);
        return ll_tds_err(c, "convert");
    }
    buf[n] = 0;
    lean_obj_res out = lean_io_result_mk_ok(lean_mk_string(buf));
    if (buf != sbuf) free(buf);
    return out;
}
