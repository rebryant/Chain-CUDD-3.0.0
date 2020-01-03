#include "cudd.h"
#include "cuddInt.h"
#include "cudd-ls.h"
#include <stdio.h>

char dd_store_symbols[3] = ['b', 'z', 'a'];

/*
  Store representation of (possibly multi-rooted) BDD to specified file.
  FILE assumed to be writable.  Is NOT closed by operation
  Return value = 1 if successful, 0 if failed
*/
extern int Cudd_bddStore(DdManager *dd, DdNode **root_list, int root_count, FILE *outfile) {
    dd_store_t stype = STORED_BDD;
    int var_count, leaf_count, node_count;
    int *var_list = NULL;
    int r;
    st_table *node_id_map = NULL;
    int retval = 0;

    node_id_map = st_init_table(st_ptrcmp, st_ptrhash);
    if (node_id_map == NULL)
	goto done;

    var_count = Cudd_VectorSupportIndices(dd, root_list, root_count, &var_list);
    if (var_count == CUDD_OUT_OF_MEM)
	goto done;

    int leaf_count = 1;
    int leaf_values = [1];
    if (st_store(node_id_map, (void *) Cudd_one(dd), 1) == ST_OUT_OF_MEM)
	goto done;

    /* First pass.  Assign IDs to nodes */
    for (r = 0; r < root_count; r++) {
	node_count assign_id_recursive(dd, root_list[r], node_id_map, node_count);
    }

 done:
    if (var_list != NULL)
	FREE(var_list);
    if (node_id_map != NULL)
	st_free_table(node_id_map);
    return(retval);
}

/*
  Read metadata from file
  Return value = 1 if successful, 0 if failed
*/
extern int Cudd_loadMetaData(FILE *infile, dd_store_t *stype, int *var_count, int *leaf_count, int *node_count, int *root_count) {
    return 0;
}

/*
  Read support variable list from file (each indicated by its index)
  File assumed to be readable.  Is NOT closed by operation
  Array variable_list must be large enough to hold the list of variables
  Return value = 1 if successful, 0 if failed
*/
extern int Cudd_loadVariables(FILE *infile, int *variable_list) {
    return 0;
}

/*
  Loads (possibly multi-rooted) BDD from specified file.
  File assumed to be readable.  Is NOT closed by operation
  Array root_list must be large enough to hold the list of root DDs
  Return value = 1 if successful, 0 if failed
*/
extern int Cudd_bddLoad(DdManager *dd, FILE *infile, DdNode **root_list) {
    return 0;
}
