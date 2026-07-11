/* sqlite3 → Lean ABI shim for the lean-linq native driver.
 *
 * Connections and statements are Lean external objects with finalizers.
 * A statement holds a counted reference to its connection so the connection
 * cannot be finalized (sqlite3_close_v2) while statements are alive —
 * close_v2 defers actual closing until outstanding statements finalize,
 * and the reference makes the common case ordered anyway.
 *
 * Errors are raised as Lean IO userError values carrying sqlite3_errmsg. */

#include <lean/lean.h>
#include <sqlite3.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- external classes ---------- */

typedef struct {
    sqlite3 *db;
} ll_conn;

typedef struct {
    sqlite3_stmt *stmt;
    lean_object *conn; /* counted reference: keeps the connection alive */
} ll_stmt;

static lean_external_class *g_conn_class = NULL;
static lean_external_class *g_stmt_class = NULL;

static void ll_conn_finalize(void *ptr) {
    ll_conn *c = (ll_conn *)ptr;
    if (c->db) sqlite3_close_v2(c->db);
    free(c);
}

static void ll_stmt_finalize(void *ptr) {
    ll_stmt *s = (ll_stmt *)ptr;
    if (s->stmt) sqlite3_finalize(s->stmt);
    if (s->conn) lean_dec(s->conn);
    free(s);
}

static void ll_noop_foreach(void *ptr, b_lean_obj_arg fn) { (void)ptr; (void)fn; }

static pthread_once_t g_class_once = PTHREAD_ONCE_INIT;

static void ll_register_classes(void) {
    g_conn_class = lean_register_external_class(ll_conn_finalize, ll_noop_foreach);
    g_stmt_class = lean_register_external_class(ll_stmt_finalize, ll_noop_foreach);
}

static lean_external_class *conn_class(void) {
    pthread_once(&g_class_once, ll_register_classes);
    return g_conn_class;
}

static lean_external_class *stmt_class(void) {
    pthread_once(&g_class_once, ll_register_classes);
    return g_stmt_class;
}

static inline ll_conn *conn_of(b_lean_obj_arg o) {
    return (ll_conn *)lean_get_external_data(o);
}

static inline ll_stmt *stmt_of(b_lean_obj_arg o) {
    return (ll_stmt *)lean_get_external_data(o);
}

static lean_obj_res ll_io_err(const char *msg) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res ll_io_err_db(sqlite3 *db, const char *what) {
    char buf[512];
    snprintf(buf, sizeof(buf), "sqlite3 %s: %s", what, db ? sqlite3_errmsg(db) : "?");
    return ll_io_err(buf);
}

/* ---------- connection ---------- */

/* open : String → IO Conn */
LEAN_EXPORT lean_obj_res ll_sqlite3_open(b_lean_obj_arg path, lean_obj_arg /* world */ w) {
    (void)w;
    sqlite3 *db = NULL;
    int rc = sqlite3_open_v2(lean_string_cstr(path), &db,
                             SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE, NULL);
    if (rc != SQLITE_OK) {
        lean_obj_res e = ll_io_err_db(db, "open");
        if (db) sqlite3_close_v2(db);
        return e;
    }
    ll_conn *c = (ll_conn *)malloc(sizeof(ll_conn));
    c->db = db;
    return lean_io_result_mk_ok(lean_alloc_external(conn_class(), c));
}

/* close : Conn → IO Unit (idempotent; the finalizer is the safety net) */
LEAN_EXPORT lean_obj_res ll_sqlite3_close(b_lean_obj_arg conn, lean_obj_arg w) {
    (void)w;
    ll_conn *c = conn_of(conn);
    if (c->db) {
        sqlite3_close_v2(c->db);
        c->db = NULL;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* execRaw : Conn → String → IO Unit (DDL / seed / BEGIN / ROLLBACK batches) */
LEAN_EXPORT lean_obj_res ll_sqlite3_exec_raw(b_lean_obj_arg conn, b_lean_obj_arg sql,
                                             lean_obj_arg w) {
    (void)w;
    ll_conn *c = conn_of(conn);
    if (!c->db) return ll_io_err("sqlite3 exec: connection is closed");
    char *errmsg = NULL;
    int rc = sqlite3_exec(c->db, lean_string_cstr(sql), NULL, NULL, &errmsg);
    if (rc != SQLITE_OK) {
        char buf[512];
        snprintf(buf, sizeof(buf), "sqlite3 exec: %s", errmsg ? errmsg : "?");
        sqlite3_free(errmsg);
        return ll_io_err(buf);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* ---------- statements ---------- */

/* prepare : Conn → String → IO Stmt */
LEAN_EXPORT lean_obj_res ll_sqlite3_prepare(lean_obj_arg conn, b_lean_obj_arg sql,
                                            lean_obj_arg w) {
    (void)w;
    ll_conn *c = conn_of(conn);
    if (!c->db) {
        lean_dec(conn);
        return ll_io_err("sqlite3 prepare: connection is closed");
    }
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(c->db, lean_string_cstr(sql), -1, &stmt, NULL);
    if (rc != SQLITE_OK) {
        lean_obj_res e = ll_io_err_db(c->db, "prepare");
        lean_dec(conn);
        return e;
    }
    ll_stmt *s = (ll_stmt *)malloc(sizeof(ll_stmt));
    s->stmt = stmt;
    s->conn = conn; /* consumes the caller's reference */
    return lean_io_result_mk_ok(lean_alloc_external(stmt_class(), s));
}

static sqlite3 *stmt_db(ll_stmt *s) { return conn_of(s->conn)->db; }

/* bindParameterIndex : Stmt → String → IO UInt32 (0 = not found) */
LEAN_EXPORT lean_obj_res ll_sqlite3_bind_parameter_index(b_lean_obj_arg stmt,
                                                         b_lean_obj_arg name,
                                                         lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    int idx = sqlite3_bind_parameter_index(s->stmt, lean_string_cstr(name));
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)idx));
}

#define LL_BIND_CHECK(rc, s)                                            \
    if ((rc) != SQLITE_OK) return ll_io_err_db(stmt_db(s), "bind");     \
    return lean_io_result_mk_ok(lean_box(0));

/* bindInt64 : Stmt → UInt32 → Int64 → IO Unit */
LEAN_EXPORT lean_obj_res ll_sqlite3_bind_int64(b_lean_obj_arg stmt, uint32_t idx,
                                               int64_t v, lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    int rc = sqlite3_bind_int64(s->stmt, (int)idx, (sqlite3_int64)v);
    LL_BIND_CHECK(rc, s)
}

/* bindDouble : Stmt → UInt32 → Float → IO Unit */
LEAN_EXPORT lean_obj_res ll_sqlite3_bind_double(b_lean_obj_arg stmt, uint32_t idx,
                                                double v, lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    int rc = sqlite3_bind_double(s->stmt, (int)idx, v);
    LL_BIND_CHECK(rc, s)
}

/* bindText : Stmt → UInt32 → String → IO Unit */
LEAN_EXPORT lean_obj_res ll_sqlite3_bind_text(b_lean_obj_arg stmt, uint32_t idx,
                                              b_lean_obj_arg v, lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    int rc = sqlite3_bind_text(s->stmt, (int)idx, lean_string_cstr(v),
                               (int)lean_string_size(v) - 1, SQLITE_TRANSIENT);
    LL_BIND_CHECK(rc, s)
}

/* bindNull : Stmt → UInt32 → IO Unit */
LEAN_EXPORT lean_obj_res ll_sqlite3_bind_null(b_lean_obj_arg stmt, uint32_t idx,
                                              lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    int rc = sqlite3_bind_null(s->stmt, (int)idx);
    LL_BIND_CHECK(rc, s)
}

/* step : Stmt → IO UInt32 (100 = ROW, 101 = DONE; anything else raises) */
LEAN_EXPORT lean_obj_res ll_sqlite3_step(b_lean_obj_arg stmt, lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    int rc = sqlite3_step(s->stmt);
    if (rc != SQLITE_ROW && rc != SQLITE_DONE)
        return ll_io_err_db(stmt_db(s), "step");
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)rc));
}

/* ---------- columns ---------- */

/* columnType : Stmt → UInt32 → IO UInt32 (1=INT 2=FLOAT 3=TEXT 4=BLOB 5=NULL) */
LEAN_EXPORT lean_obj_res ll_sqlite3_column_type(b_lean_obj_arg stmt, uint32_t i,
                                                lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)sqlite3_column_type(s->stmt, (int)i)));
}

/* columnInt64 : Stmt → UInt32 → IO Int64 */
LEAN_EXPORT lean_obj_res ll_sqlite3_column_int64(b_lean_obj_arg stmt, uint32_t i,
                                                 lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    int64_t v = (int64_t)sqlite3_column_int64(s->stmt, (int)i);
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)v));
}

/* columnDouble : Stmt → UInt32 → IO Float */
LEAN_EXPORT lean_obj_res ll_sqlite3_column_double(b_lean_obj_arg stmt, uint32_t i,
                                                  lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    return lean_io_result_mk_ok(
        lean_box_float(sqlite3_column_double(s->stmt, (int)i)));
}

/* columnText : Stmt → UInt32 → IO String */
LEAN_EXPORT lean_obj_res ll_sqlite3_column_text(b_lean_obj_arg stmt, uint32_t i,
                                                lean_obj_arg w) {
    (void)w;
    ll_stmt *s = stmt_of(stmt);
    const unsigned char *txt = sqlite3_column_text(s->stmt, (int)i);
    return lean_io_result_mk_ok(lean_mk_string(txt ? (const char *)txt : ""));
}
