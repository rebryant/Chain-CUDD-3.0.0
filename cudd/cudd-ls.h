/* Prototypes for new functions */

/* Supported DD types */
typedef enum {STORED_BDD, STORED_ZDD, STORED_ADD} dd_store_t;

/*
  Store representation of (possibly multi-rooted) BDD to specified file.
  FILE assumed to be writable.  Is NOT closed by operation
  Return value = 1 if successful, 0 if failed
*/
extern int Cudd_bddStore(DdManager *dd, DdNode **root_list, int root_count, FILE *outfile);

/*
  Read metadata from file
  Return value = 1 if successful, 0 if failed
*/
extern int Cudd_loadMetaData(FILE *infile, dd_store_t *stype, int *var_count, int *leaf_count, int *node_count, int *root_count);

/*
  Read support variable list from file (each indicated by its index)
  File assumed to be readable.  Is NOT closed by operation
  Array variable_list must be large enough to hold the list of variables
  Return value = 1 if successful, 0 if failed
*/
extern int Cudd_loadVariables(FILE *infile, int *variable_list);

/*
  Loads (possibly multi-rooted) BDD from specified file.
  File assumed to be readable.  Is NOT closed by operation
  Array root_list must be large enough to hold the list of root DDs
  Return value = 1 if successful, 0 if failed
*/
extern int Cudd_bddLoad(DdManager *dd, FILE *infile, DdNode **root_list);
