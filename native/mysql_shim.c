/* libmysqlclient → Lean ABI shim for the lean-linq native MySQL driver.
 *
 * Connections (MYSQL*) are Lean external objects with finalizers. Both
 * directions travel as text through PREPARED STATEMENTS: parameters are
 * bound as MYSQL_TYPE_STRING (MySQL coerces text in typed contexts — the
 * same philosophy as the PostgreSQL driver's text format), results are
 * bound as string out-buffers and decoded by the Lean side's parseCell.
 * The FFI surface is deliberately small: one query function returning the
 * whole result as nested arrays of optional strings, one exec function
 * returning the affected-row count, and a raw multi-statement runner for
 * DDL/seeds.
 *
 * Errors are raised as Lean IO userError values. */

#include <lean/lean.h>
#include <mysql.h>
#include <stdbool.h>

/* libmysqlclient 8+ removed my_bool (MariaDB kept it) */
#if defined(MYSQL_VERSION_ID) && MYSQL_VERSION_ID >= 80000 && !defined(MARIADB_BASE_VERSION)
typedef bool my_bool;
#endif
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- external class ---------- */

typedef struct {
    MYSQL *conn;
} ll_myconn;

static lean_external_class *g_myconn_class = NULL;

static void ll_myconn_finalize(void *ptr) {
    ll_myconn *c = (ll_myconn *)ptr;
    if (c->conn) mysql_close(c->conn);
    free(c);
}

static void ll_my_noop_foreach(void *ptr, b_lean_obj_arg fn) { (void)ptr; (void)fn; }

static pthread_once_t g_class_once = PTHREAD_ONCE_INIT;

static void ll_my_register_classes(void) {
    g_myconn_class = lean_register_external_class(ll_myconn_finalize, ll_my_noop_foreach);
}

static lean_external_class *myconn_class(void) {
    pthread_once(&g_class_once, ll_my_register_classes);
    return g_myconn_class;
}

static inline ll_myconn *myconn_of(b_lean_obj_arg o) {
    return (ll_myconn *)lean_get_external_data(o);
}

static lean_obj_res ll_my_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res ll_my_err_conn(MYSQL *conn, const char *what) {
    char buf[1024];
    snprintf(buf, sizeof buf, "mysql %s: %s", what, mysql_error(conn));
    return ll_my_err(buf);
}

static lean_obj_res ll_my_err_stmt(MYSQL_STMT *stmt, const char *what) {
    char buf[1024];
    snprintf(buf, sizeof buf, "mysql %s: %s", what, mysql_stmt_error(stmt));
    return ll_my_err(buf);
}

/* connect : host → UInt32 port → user → pass → db → IO MyConn */
LEAN_EXPORT lean_obj_res ll_my_connect(b_lean_obj_arg host, uint32_t port,
        b_lean_obj_arg user, b_lean_obj_arg pass, b_lean_obj_arg db,
        lean_obj_arg w) {
    (void)w;
    MYSQL *conn = mysql_init(NULL);
    if (!conn) return ll_my_err("mysql_init failed");
    if (!mysql_real_connect(conn, lean_string_cstr(host), lean_string_cstr(user),
            lean_string_cstr(pass), lean_string_cstr(db), port, NULL,
            CLIENT_MULTI_STATEMENTS)) {
        char buf[1024];
        snprintf(buf, sizeof buf, "mysql connect: %s", mysql_error(conn));
        mysql_close(conn);
        return ll_my_err(buf);
    }
    ll_myconn *c = (ll_myconn *)malloc(sizeof(ll_myconn));
    if (!c) { mysql_close(conn); return ll_my_err("mysql connect: out of memory"); }
    c->conn = conn;
    return lean_io_result_mk_ok(lean_alloc_external(myconn_class(), c));
}

LEAN_EXPORT lean_obj_res ll_my_close(b_lean_obj_arg connO, lean_obj_arg w) {
    (void)w;
    ll_myconn *c = myconn_of(connO);
    if (c->conn) { mysql_close(c->conn); c->conn = NULL; }
    return lean_io_result_mk_ok(lean_box(0));
}

/* execRaw : MyConn → String → IO Unit — multi-statement batches, drained. */
LEAN_EXPORT lean_obj_res ll_my_exec_raw(b_lean_obj_arg connO, b_lean_obj_arg sql,
        lean_obj_arg w) {
    (void)w;
    MYSQL *conn = myconn_of(connO)->conn;
    if (mysql_real_query(conn, lean_string_cstr(sql),
            (unsigned long)lean_string_size(sql) - 1))
        return ll_my_err_conn(conn, "execRaw");
    /* drain every pending result set of the batch */
    do {
        MYSQL_RES *res = mysql_store_result(conn);
        if (res) mysql_free_result(res);
        else if (mysql_errno(conn)) return ll_my_err_conn(conn, "execRaw drain");
    } while (mysql_next_result(conn) == 0);
    if (mysql_errno(conn)) return ll_my_err_conn(conn, "execRaw next");
    return lean_io_result_mk_ok(lean_box(0));
}

/* Bind an Array (Option String) as all-text parameters. Buffers borrow the
 * Lean strings — valid for the whole statement lifetime because the array
 * is borrowed for the whole call. */
static int bind_params(MYSQL_STMT *stmt, b_lean_obj_arg vals, MYSQL_BIND **out,
        unsigned long **lens) {
    size_t n = lean_array_size(vals);
    if (n == 0) { *out = NULL; *lens = NULL; return 0; }
    MYSQL_BIND *binds = (MYSQL_BIND *)calloc(n, sizeof(MYSQL_BIND));
    unsigned long *ls = (unsigned long *)calloc(n, sizeof(unsigned long));
    if (!binds || !ls) { free(binds); free(ls); return 1; }
    for (size_t i = 0; i < n; i++) {
        lean_object *opt = lean_array_get_core(vals, i);
        if (lean_is_scalar(opt)) {           /* none ⇒ NULL */
            binds[i].buffer_type = MYSQL_TYPE_NULL;
        } else {
            lean_object *s = lean_ctor_get(opt, 0);
            binds[i].buffer_type = MYSQL_TYPE_STRING;
            binds[i].buffer = (void *)lean_string_cstr(s);
            ls[i] = (unsigned long)lean_string_size(s) - 1;
            binds[i].buffer_length = ls[i];
            binds[i].length = &ls[i];
        }
    }
    if (mysql_stmt_bind_param(stmt, binds)) { free(binds); free(ls); return 2; }
    *out = binds; *lens = ls;
    return 0;
}

#define LL_MY_CELL_CAP 262144

/* query : MyConn → String → Array (Option String)
         → IO (Array (Array (Option String))) */
LEAN_EXPORT lean_obj_res ll_my_query(b_lean_obj_arg connO, b_lean_obj_arg sql,
        b_lean_obj_arg vals, lean_obj_arg w) {
    (void)w;
    MYSQL *conn = myconn_of(connO)->conn;
    MYSQL_STMT *stmt = mysql_stmt_init(conn);
    if (!stmt) return ll_my_err_conn(conn, "stmt_init");
    lean_obj_res err = NULL;
    MYSQL_BIND *pbinds = NULL; unsigned long *plens = NULL;
    MYSQL_BIND *rbinds = NULL; unsigned long *rlens = NULL;
    my_bool *rnulls = NULL; char **rbufs = NULL;
    MYSQL_RES *meta = NULL;
    unsigned int nf = 0;
    lean_object *rows = NULL;

    if (mysql_stmt_prepare(stmt, lean_string_cstr(sql),
            (unsigned long)lean_string_size(sql) - 1)) {
        err = ll_my_err_stmt(stmt, "prepare"); goto done;
    }
    if (bind_params(stmt, vals, &pbinds, &plens)) {
        err = ll_my_err_stmt(stmt, "bind_param"); goto done;
    }
    if (mysql_stmt_execute(stmt)) {
        err = ll_my_err_stmt(stmt, "execute"); goto done;
    }
    meta = mysql_stmt_result_metadata(stmt);
    if (!meta) { err = ll_my_err_stmt(stmt, "result_metadata"); goto done; }
    nf = mysql_num_fields(meta);
    rbinds = (MYSQL_BIND *)calloc(nf, sizeof(MYSQL_BIND));
    rlens = (unsigned long *)calloc(nf, sizeof(unsigned long));
    rnulls = (my_bool *)calloc(nf, sizeof(my_bool));
    rbufs = (char **)calloc(nf, sizeof(char *));
    if (!rbinds || !rlens || !rnulls || !rbufs) { err = ll_my_err("mysql query: oom"); goto done; }
    for (unsigned int i = 0; i < nf; i++) {
        rbufs[i] = (char *)malloc(LL_MY_CELL_CAP);
        if (!rbufs[i]) { err = ll_my_err("mysql query: oom"); goto done; }
        rbinds[i].buffer_type = MYSQL_TYPE_STRING;
        rbinds[i].buffer = rbufs[i];
        rbinds[i].buffer_length = LL_MY_CELL_CAP;
        rbinds[i].length = &rlens[i];
        rbinds[i].is_null = &rnulls[i];
    }
    if (mysql_stmt_bind_result(stmt, rbinds)) {
        err = ll_my_err_stmt(stmt, "bind_result"); goto done;
    }
    if (mysql_stmt_store_result(stmt)) {
        err = ll_my_err_stmt(stmt, "store_result"); goto done;
    }
    rows = lean_mk_empty_array();
    for (;;) {
        int rc = mysql_stmt_fetch(stmt);
        if (rc == MYSQL_NO_DATA) break;
        if (rc == 1) { err = ll_my_err_stmt(stmt, "fetch"); goto done; }
        /* rc == 0 or MYSQL_DATA_TRUNCATED; cap is generous, truncation is a bug */
        if (rc == MYSQL_DATA_TRUNCATED) { err = ll_my_err("mysql fetch: cell truncated"); goto done; }
        lean_object *row = lean_mk_empty_array();
        for (unsigned int i = 0; i < nf; i++) {
            lean_object *cell;
            if (rnulls[i]) cell = lean_box(0); /* none */
            else {
                lean_object *s = lean_mk_string_from_bytes(rbufs[i], rlens[i]);
                cell = lean_alloc_ctor(1, 1, 0);
                lean_ctor_set(cell, 0, s);
            }
            row = lean_array_push(row, cell);
        }
        rows = lean_array_push(rows, row);
    }
    err = NULL;
done:
    if (meta) mysql_free_result(meta);
    if (rbufs) { for (unsigned int i = 0; i < nf; i++) free(rbufs[i]); free(rbufs); }
    free(rbinds); free(rlens); free(rnulls);
    free(pbinds); free(plens);
    mysql_stmt_close(stmt);
    if (err) { if (rows) lean_dec(rows); return err; }
    return lean_io_result_mk_ok(rows);
}

/* execParams : MyConn → String → Array (Option String) → IO UInt32
   (prepared execute, affected-row count — DML only) */
LEAN_EXPORT lean_obj_res ll_my_exec_params(b_lean_obj_arg connO, b_lean_obj_arg sql,
        b_lean_obj_arg vals, lean_obj_arg w) {
    (void)w;
    MYSQL *conn = myconn_of(connO)->conn;
    MYSQL_STMT *stmt = mysql_stmt_init(conn);
    if (!stmt) return ll_my_err_conn(conn, "stmt_init");
    lean_obj_res err = NULL;
    MYSQL_BIND *pbinds = NULL; unsigned long *plens = NULL;
    uint32_t affected = 0;
    if (mysql_stmt_prepare(stmt, lean_string_cstr(sql),
            (unsigned long)lean_string_size(sql) - 1)) {
        err = ll_my_err_stmt(stmt, "prepare"); goto done;
    }
    if (bind_params(stmt, vals, &pbinds, &plens)) {
        err = ll_my_err_stmt(stmt, "bind_param"); goto done;
    }
    if (mysql_stmt_execute(stmt)) {
        err = ll_my_err_stmt(stmt, "execute"); goto done;
    }
    {
        my_ulonglong n = mysql_stmt_affected_rows(stmt);
        affected = (n == (my_ulonglong)-1) ? 0 : (uint32_t)n;
    }
done:
    free(pbinds); free(plens);
    mysql_stmt_close(stmt);
    if (err) return err;
    return lean_io_result_mk_ok(lean_box_uint32(affected));
}
