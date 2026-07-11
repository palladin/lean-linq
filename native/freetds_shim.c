/* FreeTDS DB-Library → Lean ABI shim for the lean-linq native SQL Server
 * driver.
 *
 * dblib requires global error/message handlers — without them it prints to
 * stderr and may abort the process. The handlers stash the latest text in
 * static buffers, and any FAIL raises a Lean IO userError carrying them.
 * (Static buffers: the test drivers are single-threaded; revisit for a
 * concurrent production driver.)
 *
 * The login forces TDS 7.1, so datetime2 columns arrive as nvarchar text
 * on the wire; every result cell is read via dbconvert(coltype → SYBCHAR)
 * and parsed by the shared Lean text decoders. */

#include <lean/lean.h>
#include <sybfront.h>
#include <sybdb.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- global error capture ---------- */

static char g_err[1024] = "";
static char g_msg[1024] = "";

static int ll_tds_err_handler(DBPROCESS *dbproc, int severity, int dberr,
                              int oserr, char *dberrstr, char *oserrstr) {
    (void)dbproc; (void)severity; (void)dberr; (void)oserr; (void)oserrstr;
    if (dberrstr) snprintf(g_err, sizeof(g_err), "%s", dberrstr);
    return INT_CANCEL;
}

static int ll_tds_msg_handler(DBPROCESS *dbproc, DBINT msgno, int msgstate,
                              int severity, char *msgtext, char *srvname,
                              char *procname, int line) {
    (void)dbproc; (void)msgno; (void)msgstate; (void)srvname;
    (void)procname; (void)line;
    if (severity > 0 && msgtext)
        snprintf(g_msg, sizeof(g_msg), "%s", msgtext);
    return 0;
}

static int g_inited = 0;

static int ll_tds_init(void) {
    if (!g_inited) {
        if (dbinit() == FAIL) return 0;
        dberrhandle(ll_tds_err_handler);
        dbmsghandle(ll_tds_msg_handler);
        dbsetlogintime(10);
        g_inited = 1;
    }
    return 1;
}

static lean_obj_res ll_tds_err(const char *what) {
    char buf[2200];
    snprintf(buf, sizeof(buf), "freetds %s: %s%s%s", what, g_err,
             (g_err[0] && g_msg[0]) ? " | " : "", g_msg);
    g_err[0] = 0;
    g_msg[0] = 0;
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

/* ---------- connection external ---------- */

typedef struct {
    DBPROCESS *dbproc;
} ll_tdsconn;

static lean_external_class *g_tdsconn_class = NULL;

static void ll_tdsconn_finalize(void *ptr) {
    ll_tdsconn *c = (ll_tdsconn *)ptr;
    if (c->dbproc) dbclose(c->dbproc);
    free(c);
}

static void ll_tds_noop_foreach(void *ptr, b_lean_obj_arg fn) { (void)ptr; (void)fn; }

static lean_external_class *tdsconn_class(void) {
    if (!g_tdsconn_class)
        g_tdsconn_class = lean_register_external_class(ll_tdsconn_finalize,
                                                       ll_tds_noop_foreach);
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
    if (!ll_tds_init()) return ll_tds_err("init");
    LOGINREC *login = dblogin();
    if (!login) return ll_tds_err("login alloc");
    DBSETLUSER(login, lean_string_cstr(user));
    DBSETLPWD(login, lean_string_cstr(pass));
    DBSETLCHARSET(login, "UTF-8");
    DBSETLVERSION(login, DBVERSION_71); /* datetime2 arrives as nvarchar text */
    DBPROCESS *dbproc = dbopen(login, lean_string_cstr(server));
    dbloginfree(login);
    if (!dbproc) return ll_tds_err("connect");
    if (lean_string_size(db) > 1) { /* non-empty */
        if (dbuse(dbproc, lean_string_cstr(db)) == FAIL) {
            lean_obj_res e = ll_tds_err("use database");
            dbclose(dbproc);
            return e;
        }
    }
    ll_tdsconn *c = (ll_tdsconn *)malloc(sizeof(ll_tdsconn));
    c->dbproc = dbproc;
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
    return NULL;
}

/* drain every pending result set */
static RETCODE drain_results(DBPROCESS *dbproc) {
    RETCODE r;
    while ((r = dbresults(dbproc)) != NO_MORE_RESULTS) {
        if (r == FAIL) return FAIL;
        while (dbnextrow(dbproc) != NO_MORE_ROWS) { }
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
        return ll_tds_err("dbcmd");
    if (dbsqlexec(c->dbproc) == FAIL) return ll_tds_err("exec");
    if (drain_results(c->dbproc) == FAIL) return ll_tds_err("exec results");
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
        return ll_tds_err("dbcmd");
    if (dbsqlexec(c->dbproc) == FAIL) return ll_tds_err("batch exec");
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
    if (dbrpcinit(c->dbproc, (char *)lean_string_cstr(proc), 0) == FAIL)
        return ll_tds_err("rpcinit");
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
        r = dbrpcparam(c->dbproc, (char *)lean_string_cstr(name), 0,
                       type, -1, (DBINT)(lean_string_size(value) - 1),
                       (BYTE *)lean_string_cstr(value));
    }
    if (r == FAIL) return ll_tds_err("rpcparam");
    return lean_io_result_mk_ok(lean_box(0));
}

/* rpcSend : MsConn → IO Unit */
LEAN_EXPORT lean_obj_res ll_tds_rpc_send(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    lean_obj_res bad = ll_tds_check_conn(c, "rpcsend");
    if (bad) return bad;
    if (dbrpcsend(c->dbproc) == FAIL) return ll_tds_err("rpcsend");
    if (dbsqlok(c->dbproc) == FAIL) return ll_tds_err("rpc sqlok");
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
    if (r == FAIL) return ll_tds_err("results");
    return lean_io_result_mk_ok(lean_box_uint32(1));
}

/* rowNext : MsConn → IO UInt32 — 1 = row available, 0 = no more rows */
LEAN_EXPORT lean_obj_res ll_tds_row_next(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_tdsconn *c = tdsconn_of(conn);
    RETCODE r = dbnextrow(c->dbproc);
    if (r == NO_MORE_ROWS)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    if (r == FAIL) return ll_tds_err("nextrow");
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
    char buf[4096];
    DBINT n = dbconvert(c->dbproc, type, data, len, SYBCHAR,
                        (BYTE *)buf, sizeof(buf) - 1);
    if (n < 0) return ll_tds_err("convert");
    buf[n] = 0;
    return lean_io_result_mk_ok(lean_mk_string(buf));
}
