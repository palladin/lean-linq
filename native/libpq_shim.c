/* libpq → Lean ABI shim for the lean-linq native PostgreSQL driver.
 *
 * Connections (PGconn) and results (PGresult) are Lean external objects
 * with finalizers. All values travel in text format both directions;
 * parameters carry explicit OIDs. Pipeline mode is exposed for the
 * DbFetch level-synchronous interpreter (`seq` batching).
 *
 * Errors are raised as Lean IO userError values. */

#include <lean/lean.h>
#include <libpq-fe.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- external classes ---------- */

typedef struct {
    PGconn *conn;
} ll_pgconn;

typedef struct {
    PGresult *res;
} ll_pgres;

static lean_external_class *g_pgconn_class = NULL;
static lean_external_class *g_pgres_class = NULL;

static void ll_pgconn_finalize(void *ptr) {
    ll_pgconn *c = (ll_pgconn *)ptr;
    if (c->conn) PQfinish(c->conn);
    free(c);
}

static void ll_pgres_finalize(void *ptr) {
    ll_pgres *r = (ll_pgres *)ptr;
    if (r->res) PQclear(r->res);
    free(r);
}

static void ll_pg_noop_foreach(void *ptr, b_lean_obj_arg fn) { (void)ptr; (void)fn; }

static pthread_once_t g_class_once = PTHREAD_ONCE_INIT;

static void ll_pg_register_classes(void) {
    g_pgconn_class = lean_register_external_class(ll_pgconn_finalize, ll_pg_noop_foreach);
    g_pgres_class = lean_register_external_class(ll_pgres_finalize, ll_pg_noop_foreach);
}

static lean_external_class *pgconn_class(void) {
    pthread_once(&g_class_once, ll_pg_register_classes);
    return g_pgconn_class;
}

static lean_external_class *pgres_class(void) {
    pthread_once(&g_class_once, ll_pg_register_classes);
    return g_pgres_class;
}

static inline ll_pgconn *pgconn_of(b_lean_obj_arg o) {
    return (ll_pgconn *)lean_get_external_data(o);
}

static inline ll_pgres *pgres_of(b_lean_obj_arg o) {
    return (ll_pgres *)lean_get_external_data(o);
}

static lean_obj_res ll_pg_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res ll_pg_err_conn(PGconn *conn, const char *what) {
    char buf[1024];
    snprintf(buf, sizeof(buf), "libpq %s: %s", what,
             conn ? PQerrorMessage(conn) : "?");
    return ll_pg_err(buf);
}

static lean_obj_res mk_result_obj(PGresult *res) {
    ll_pgres *r = (ll_pgres *)malloc(sizeof(ll_pgres));
    r->res = res;
    return lean_alloc_external(pgres_class(), r);
}

/* ---------- connection ---------- */

/* connect : String → IO PgConn */
LEAN_EXPORT lean_obj_res ll_pq_connect(b_lean_obj_arg conninfo, lean_obj_arg w) {
    (void)w;
    PGconn *conn = PQconnectdb(lean_string_cstr(conninfo));
    if (!conn || PQstatus(conn) != CONNECTION_OK) {
        lean_obj_res e = ll_pg_err_conn(conn, "connect");
        if (conn) PQfinish(conn);
        return e;
    }
    ll_pgconn *c = (ll_pgconn *)malloc(sizeof(ll_pgconn));
    c->conn = conn;
    return lean_io_result_mk_ok(lean_alloc_external(pgconn_class(), c));
}

/* close : PgConn → IO Unit */
LEAN_EXPORT lean_obj_res ll_pq_finish(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    if (c->conn) {
        PQfinish(c->conn);
        c->conn = NULL;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* execRaw : PgConn → String → IO Unit (multi-statement batches) */
LEAN_EXPORT lean_obj_res ll_pq_exec_raw(b_lean_obj_arg conn, b_lean_obj_arg sql,
                                        lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    if (!c->conn) return ll_pg_err("libpq exec: connection is closed");
    PGresult *res = PQexec(c->conn, lean_string_cstr(sql));
    ExecStatusType st = res ? PQresultStatus(res) : PGRES_FATAL_ERROR;
    if (st != PGRES_COMMAND_OK && st != PGRES_TUPLES_OK && st != PGRES_EMPTY_QUERY) {
        lean_obj_res e = ll_pg_err_conn(c->conn, "exec");
        if (res) PQclear(res);
        return e;
    }
    if (res) PQclear(res);
    return lean_io_result_mk_ok(lean_box(0));
}

/* ---------- parameterized execution ---------- */

/* Marshal `oids : Array UInt32` and `vals : Array (Option String)` into C
 * arrays. Caller frees. Values are borrowed for the duration of the call. */
static int marshal_params(b_lean_obj_arg oids, b_lean_obj_arg vals,
                          Oid **outTypes, const char ***outValues, size_t *outN) {
    size_t n = lean_array_size(oids);
    if (lean_array_size(vals) != n) return 0;
    Oid *types = (Oid *)malloc(sizeof(Oid) * (n ? n : 1));
    const char **values = (const char **)malloc(sizeof(char *) * (n ? n : 1));
    for (size_t i = 0; i < n; i++) {
        types[i] = (Oid)lean_unbox_uint32(lean_array_get_core(oids, i));
        lean_object *opt = lean_array_get_core(vals, i);
        values[i] = lean_is_scalar(opt) ? NULL
                                        : lean_string_cstr(lean_ctor_get(opt, 0));
    }
    *outTypes = types;
    *outValues = values;
    *outN = n;
    return 1;
}

/* execParams : PgConn → String → Array UInt32 → Array (Option String) → IO PgResult */
LEAN_EXPORT lean_obj_res ll_pq_exec_params(b_lean_obj_arg conn, b_lean_obj_arg sql,
                                           b_lean_obj_arg oids, b_lean_obj_arg vals,
                                           lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    if (!c->conn) return ll_pg_err("libpq execParams: connection is closed");
    Oid *types; const char **values; size_t n;
    if (!marshal_params(oids, vals, &types, &values, &n))
        return ll_pg_err("libpq execParams: oid/value arrays disagree");
    PGresult *res = PQexecParams(c->conn, lean_string_cstr(sql), (int)n, types,
                                 values, NULL, NULL, 0 /* text results */);
    free(types); free(values);
    ExecStatusType st = res ? PQresultStatus(res) : PGRES_FATAL_ERROR;
    if (st != PGRES_TUPLES_OK && st != PGRES_COMMAND_OK) {
        char buf[1024];
        snprintf(buf, sizeof(buf), "libpq execParams: %s",
                 res ? PQresultErrorMessage(res) : PQerrorMessage(c->conn));
        if (res) PQclear(res);
        return ll_pg_err(buf);
    }
    return lean_io_result_mk_ok(mk_result_obj(res));
}

/* ---------- result accessors ---------- */

/* ntuples : PgResult → IO UInt32 */
LEAN_EXPORT lean_obj_res ll_pq_ntuples(b_lean_obj_arg res, lean_obj_arg w) {
    (void)w;
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)PQntuples(pgres_of(res)->res)));
}

/* getisnull : PgResult → UInt32 → UInt32 → IO Bool */
LEAN_EXPORT lean_obj_res ll_pq_getisnull(b_lean_obj_arg res, uint32_t row,
                                         uint32_t col, lean_obj_arg w) {
    (void)w;
    int b = PQgetisnull(pgres_of(res)->res, (int)row, (int)col);
    return lean_io_result_mk_ok(lean_box(b ? 1 : 0));
}

/* getvalue : PgResult → UInt32 → UInt32 → IO String */
LEAN_EXPORT lean_obj_res ll_pq_getvalue(b_lean_obj_arg res, uint32_t row,
                                        uint32_t col, lean_obj_arg w) {
    (void)w;
    const char *v = PQgetvalue(pgres_of(res)->res, (int)row, (int)col);
    return lean_io_result_mk_ok(lean_mk_string(v ? v : ""));
}

/* ---------- pipeline mode ---------- */

/* enterPipeline : PgConn → IO Unit */
LEAN_EXPORT lean_obj_res ll_pq_enter_pipeline(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    if (PQenterPipelineMode(c->conn) != 1)
        return ll_pg_err_conn(c->conn, "enterPipeline");
    return lean_io_result_mk_ok(lean_box(0));
}

/* sendQueryParams : PgConn → String → Array UInt32 → Array (Option String) → IO Unit */
LEAN_EXPORT lean_obj_res ll_pq_send_query_params(b_lean_obj_arg conn, b_lean_obj_arg sql,
                                                 b_lean_obj_arg oids, b_lean_obj_arg vals,
                                                 lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    Oid *types; const char **values; size_t n;
    if (!marshal_params(oids, vals, &types, &values, &n))
        return ll_pg_err("libpq sendQueryParams: oid/value arrays disagree");
    int ok = PQsendQueryParams(c->conn, lean_string_cstr(sql), (int)n, types,
                               values, NULL, NULL, 0);
    free(types); free(values);
    if (ok != 1) return ll_pg_err_conn(c->conn, "sendQueryParams");
    return lean_io_result_mk_ok(lean_box(0));
}

/* pipelineSync : PgConn → IO Unit */
LEAN_EXPORT lean_obj_res ll_pq_pipeline_sync(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    if (PQpipelineSync(c->conn) != 1)
        return ll_pg_err_conn(c->conn, "pipelineSync");
    return lean_io_result_mk_ok(lean_box(0));
}

/* pipelineReadResult : PgConn → IO PgResult
 * Reads one query's result inside a pipeline: PQgetResult (the tuples),
 * then the NULL separator. */
LEAN_EXPORT lean_obj_res ll_pq_pipeline_read_result(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    PGresult *res = PQgetResult(c->conn);
    ExecStatusType st = res ? PQresultStatus(res) : PGRES_FATAL_ERROR;
    if (st != PGRES_TUPLES_OK && st != PGRES_COMMAND_OK) {
        char buf[1024];
        snprintf(buf, sizeof(buf), "libpq pipeline result: %s",
                 res ? PQresultErrorMessage(res) : PQerrorMessage(c->conn));
        if (res) PQclear(res);
        return ll_pg_err(buf);
    }
    PGresult *sep = PQgetResult(c->conn); /* NULL separator after each query */
    if (sep) {
        PQclear(sep);
        PQclear(res);
        return ll_pg_err("libpq pipeline: expected NULL separator");
    }
    return lean_io_result_mk_ok(mk_result_obj(res));
}

/* pipelineConsumeSync : PgConn → IO Unit — read (and discard) the
 * PGRES_PIPELINE_SYNC result that terminates a batch. */
LEAN_EXPORT lean_obj_res ll_pq_pipeline_consume_sync(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    for (;;) {
        PGresult *res = PQgetResult(c->conn);
        if (!res) continue; /* skip separators */
        ExecStatusType st = PQresultStatus(res);
        PQclear(res);
        if (st == PGRES_PIPELINE_SYNC)
            return lean_io_result_mk_ok(lean_box(0));
        if (st != PGRES_TUPLES_OK && st != PGRES_COMMAND_OK)
            return ll_pg_err_conn(c->conn, "pipeline sync");
    }
}

/* pipelineAbort : PgConn → IO Unit — best-effort recovery after an error
 * mid-round: queue a sync point so the drain terminates, discard every
 * pending result (including PIPELINE_ABORTED ones and NULL separators)
 * up to the sync, then leave pipeline mode. Never raises: the original
 * error is the one worth reporting. */
LEAN_EXPORT lean_obj_res ll_pq_pipeline_abort(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    if (c->conn && PQpipelineStatus(c->conn) != PQ_PIPELINE_OFF) {
        /* results only flush at a sync point: queue one in case the error
         * struck before the round's own sync was sent */
        PQpipelineSync(c->conn);
        /* consume everything pending (results, aborted markers, sync
         * results, NULL separators — possibly across SEVERAL sync points)
         * until libpq agrees to leave pipeline mode */
        for (int guard = 0; guard < 100000; guard++) {
            if (PQstatus(c->conn) == CONNECTION_BAD) break;
            if (PQexitPipelineMode(c->conn) == 1) break;
            PGresult *res = PQgetResult(c->conn);
            if (res) PQclear(res);
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* exitPipeline : PgConn → IO Unit */
LEAN_EXPORT lean_obj_res ll_pq_exit_pipeline(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_pgconn *c = pgconn_of(conn);
    if (PQexitPipelineMode(c->conn) != 1)
        return ll_pg_err_conn(c->conn, "exitPipeline");
    return lean_io_result_mk_ok(lean_box(0));
}
