// SPDX-License-Identifier: BSD-2-Clause
// Exercise the actual private RPQ types, including their generated JIT typedefs.
#include "../algorithm/LAGraph_2RpqPath.c"
#include <LAGraph_test.h>

static char msg [LAGRAPH_MSG_LEN] ;

static void check_type (GrB_Type type)
{
    size_t size = 0, name_size = 0, defn_size = 0 ;
    OK (GrB_get (type, &size, GrB_SIZE)) ;
    OK (GrB_get (type, &name_size, GxB_JIT_C_NAME)) ;
    OK (GrB_get (type, &defn_size, GxB_JIT_C_DEFINITION)) ;
    char *name = malloc (name_size), *defn = malloc (defn_size) ;
    TEST_ASSERT (name != NULL && defn != NULL) ;
    OK (GrB_get (type, name, GxB_JIT_C_NAME)) ;
    OK (GrB_get (type, defn, GxB_JIT_C_DEFINITION)) ;
    // Size zero asks the JIT compiler to evaluate sizeof(the supplied C type).
    GrB_Type compiled = NULL ;
    OK (GxB_Type_new (&compiled, 0, name, defn)) ;
    size_t compiled_size = 0 ;
    OK (GrB_get (compiled, &compiled_size, GrB_SIZE)) ;
    TEST_CHECK (size == compiled_size) ;
    free (name) ; free (defn) ;
    OK (GrB_free (&compiled)) ;

    GrB_Matrix A = NULL ;
    OK (GrB_Matrix_new (&A, type, 8, 8)) ;
    OK (GrB_set (A, GxB_SPARSE, GxB_SPARSITY_CONTROL)) ;
    unsigned char *value = calloc (size, 1), *actual = malloc (size) ;
    TEST_ASSERT (value != NULL && actual != NULL) ;
    for (GrB_Index k = 0 ; k < 8 ; k++)
    {
        memset (value, (int) k + 1, size) ;
        OK (GrB_Matrix_setElement_UDT (A, value, k, k)) ;
    }
    OK (GrB_Matrix_wait (A, GrB_MATERIALIZE)) ;
    // NONZOMBIE select must copy a non-iso UDT while removing deleted entries.
    OK (GrB_Matrix_removeElement (A, 3, 3)) ;
    OK (GrB_Matrix_wait (A, GrB_MATERIALIZE)) ;
    GrB_Index count = 0 ;
    OK (GrB_Matrix_nvals (&count, A)) ;
    TEST_CHECK (count == 7) ;
    for (GrB_Index k = 0 ; k < 8 ; k++)
    {
        if (k == 3) continue ;
        memset (value, (int) k + 1, size) ;
        OK (GrB_Matrix_extractElement_UDT (actual, A, k, k)) ;
        TEST_CHECK (memcmp (value, actual, size) == 0) ;
    }
    int32_t jit = 0 ;
    OK (GxB_Global_Option_get_INT32 (GxB_JIT_C_CONTROL, &jit)) ;
    TEST_CHECK (jit == GxB_JIT_ON) ;
    free (value) ; free (actual) ;
    OK (GrB_free (&A)) ;
}

static void test_jit_types (void)
{
    OK (LAGraph_Init (msg)) ;
    const char *cache = getenv ("LAGRAPH_TEST_JIT_CACHE") ;
    if (cache != NULL)
        OK (GxB_Global_Option_set_CHAR (GxB_JIT_CACHE_PATH, cache)) ;
    OK (GxB_Global_Option_set_INT32 (GxB_JIT_C_CONTROL, GxB_JIT_ON)) ;
    // Different automaton sizes in one process exercise changing H definitions.
    for (GrB_Index states = 2 ; states <= 9 ; states += 7)
    {
        LAGraph_Graph R = NULL, G = NULL ;
        GrB_Matrix N = NULL, A = NULL ;
        OK (GrB_Matrix_new (&N, GrB_BOOL, states, states)) ;
        OK (GrB_Matrix_new (&A, GrB_BOOL, 4, 4)) ;
        OK (LAGraph_New (&R, &N, LAGraph_ADJACENCY_DIRECTED, msg)) ;
        OK (LAGraph_New (&G, &A, LAGraph_ADJACENCY_DIRECTED, msg)) ;
        LG_RpqPath_Workspace *work = NULL ;
        OK (LG_RpqPath_Init (&work, &R, 1, &G, msg)) ;
        check_type (work->state_set_type) ;
        check_type (work->temporary_set_type) ;
        check_type (work->stored_set_type) ;
        LG_RpqPath_BlockPool pool = { 0 } ;
        LG_RpqPath_Operators ops = { 0 } ;
        OK (LG_RpqPath_CreatePredecessorOperators (&ops, work, &pool)) ;
        OK (LG_RpqPath_CreateAccumulationOperators (&ops, work, &pool)) ;
        check_type (ops.predecessor_context_type) ;
        check_type (ops.stored_context_type) ;
        LG_RpqPath_FreeOperators (&ops) ;
        LG_RpqPath_Free (&work) ;
        OK (LAGraph_Delete (&R, msg)) ;
        OK (LAGraph_Delete (&G, msg)) ;
    }
    OK (LAGraph_Finalize (msg)) ;
}

TEST_LIST = { { "RPQ JIT types and zombie removal", test_jit_types }, { NULL, NULL } } ;
