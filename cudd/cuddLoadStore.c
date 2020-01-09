/**
  @file 

  @ingroup cudd

  @brief %DD storing to and loading from files

  @author Randy Bryant

  @copyright@parblock
  Copyright (c) 1995-2015, Regents of the University of Colorado

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  Neither the name of the University of Colorado nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.
  @endparblock

*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "cudd.h"
#include "cuddInt.h"
#include "util.h"

/*********************** FILE FORMAT **************************

PRINCIPLES

* Line-oriented, ASCII format
* Any line with '#' in first column ignored
* Includes metainformation that can be read without loading entire DD
* Format extends to ADDs and ZDDs
* Nodes referred to with integer IDs.
* +i means positive pointer -i means negative pointer
* Designed for environment where collection of DDs all use common set
  of variables and common variable ordering.
* Given DD may depend on only a subset of these variables (its support)

SECTIONS

* Header: Overall info
* Variables: Variables in support set
* Leaves: Leaf values
* Nodes: Non-leaf nodes

HEADER

  TYPE VARCOUNT LEAFCOUNT NODECOUNT ROOTID

* TYPE       B/Z/A (BDD, ZDD, ADD)
* VARCOUNT   Number of variables in support
* LEAFCOUNT  Number of leaves
* NODECOUNT  Number of leaf + non-leaf nodes
* ROOTID     Integer ID of root

VARIABLES

  V[1] ... V[VARCOUNT]

  * Ordered list of variables in support
  * Each on separate line

LEAVES

  L[1] ... L[LEAFCOUNT]

  * Each has format:
    ID VALUE
    - ID.  Own ID
    - VALUE.  Leaf value
  * Each on separate line

NODES
  
  N[LEAFCOUNT+1] ... N[NODECOUNT]

  * Each has format
    ID INDEX/INDICES TChild EChild
    - ID.  Own ID.
    - INDEX.  Without chaining, or with chaining when index == bindex
    - INDICES: of form t:b where t is index and b is bindex
    - TChild + or - the ID of the T child.  |Tchild| < ID, 
    - EChild + or - the ID of the E child.  |Echild| < ID, 
  * Ordered so that each of TChild and EChild will be leaf or occur in list before node
  * Each node on separate line

******************* End FILE FORMAT **************************/


/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define MAXLINE 1024

static char dd_store_symbols[4] = {'B', 'Z', 'A', '\0'};

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static int assign_id_recursive(DdNode *f, st_table *forward_map, st_table *reverse_map, int *counter);
static DdNode *idToNode(int, st_table *reverse_map);
static int nodeToId(DdNode *f, st_table *forward_map);

static int show_node(DdNode *f, int id, st_table *forward_map, FILE *outfile);
static char *getLine(FILE *infile, char *buf);

/**
  @brief Stores representation of BDD to specified file.

  @return 1 if successful, 0 if failed

  @details   FILE assumed to be writable.  It is not closed by operation

  @sideeffect File written

  @see Cudd_bddLoad
**/
int Cudd_bddStore(DdManager *dd, DdNode *root, FILE *outfile) {
    dd_store_t stype = CUDD_STORED_BDD;
    int var_count, leaf_count, node_count;
    int *var_list = NULL;
    int i, rid;
    st_table *forward_map = NULL;
    st_table *reverse_map = NULL;
    int retval = 0;
    int leaf_values[1] = {1};
    int ok = 1;

    forward_map = st_init_table(st_ptrcmp, st_ptrhash);
    if (forward_map == NULL)
	goto done;
    
    reverse_map = st_init_table(st_numcmp, st_numhash);
    if (reverse_map == NULL)
	goto done;

    var_count = Cudd_SupportIndices(dd, root, &var_list);
    if (var_count == CUDD_OUT_OF_MEM)
	goto done;

    leaf_count = 1;
    node_count = 0;

    if (st_insert(forward_map, (void *) DD_ONE(dd), (void *) (uintptr_t) ++node_count) == ST_OUT_OF_MEM)
	goto done;

    /* Recursively assign IDs to nodes */
    if (!assign_id_recursive(root, forward_map, reverse_map, &node_count))
	goto done;

    /* Get root ID */
    rid = nodeToId(root, forward_map);
    if (rid == 0)
	goto done;

    /* Generate output file */
    ok = ok && fprintf(outfile, "# TYPE VARCOUNT LEAFCOUNT NODECOUNT ROOTID\n") > 0;
    ok = ok && fprintf(outfile, "%c %d %d %d %d\n",
		       dd_store_symbols[stype], var_count, leaf_count, node_count, rid) > 0;
    ok = ok && fprintf(outfile, "# Variable list\n") > 0;
    for (i = 0; ok && i < var_count; i++) {
	ok = ok && fprintf(outfile, "%d\n", var_list[i]) > 0;
    }
    ok = ok && fprintf(outfile, "# Leaves: ID VALUE\n") > 0;
    for (i = 0; ok && i < leaf_count; i++) {
	ok = ok && fprintf(outfile, "%d %d\n", i+1, leaf_values[i]) > 0;
    }
    ok = ok && fprintf(outfile, "# Nodes: ID INDICES TCHILD ECHILD\n") > 0;
    for (i = leaf_count+1; ok && i <= node_count; i++) {
	DdNode *F = idToNode(i, reverse_map);
	if (F == NULL)
	    goto done;
	if (!show_node(F, i, forward_map, outfile))
	    goto done;
    }
    retval = ok;

 done:
    if (var_list != NULL)
	FREE(var_list);
    if (forward_map != NULL)
	st_free_table(forward_map);
    if (reverse_map != NULL)
	st_free_table(reverse_map);
    return(retval);
}

/**
  @brief Reads metadata for a DD from specified file.

  @return 1 if successful, 0 if failed

  @details  File assumed to be readable and positioned at start of file.  
  File is not closed by operation

  @sideeffect Locations designated by pointer arguments are updated

  @see Cudd_bddLoad
**/
extern int Cudd_loadMetadata(FILE *infile, dd_store_t *stype, int *var_count, int *leaf_count, int *node_count, int *root_id) {
    char buf[MAXLINE];
    char *line = getLine(infile, buf);
    char ctype;
    int retval = 0;
    if (line == NULL) {
	fprintf(stderr, "ERROR.  DD Load: Unexpected EOF reading metadata\n");
	return retval;
    }
    if (sscanf(line, "%c %d %d %d %d", &ctype, var_count, leaf_count, node_count, root_id) != 5) {
	fprintf(stderr, "ERROR.  DD Load: Couldn't extract header information from '%s'\n", line);
	return retval;
    }
    int idx;
    for (idx = 0; dd_store_symbols[idx] != '\0'; idx++) {
	if (dd_store_symbols[idx] == ctype) {
	    *stype = idx;
	    retval = 1;
	    break;
	}
    }
    return retval;
}


/**
  @brief Reads support variable list for a DD from specified file.

  @return 1 if successful, 0 if failed

  @details File assumed to be readable and positioned at start of
  file.  File is not closed by operation.  Array variable_list must be
  large enough to hold the list of variables

  @sideeffect Indices of variables written to array variable_list

  @see Cudd_bddLoad
**/
extern int Cudd_loadVariables(FILE *infile, int *variable_list) {
    dd_store_t stype;
    int var_count, leaf_count, node_count, root_id;
    int i;
    if (!Cudd_loadMetadata(infile, &stype, &var_count, &leaf_count, &node_count, &root_id))
	return 0;
    for (i = 0; i < var_count; i++) {
	int idx;
	char buf[MAXLINE];
	char *line = getLine(infile, buf);
	if (!line) {
	    fprintf(stderr, "ERROR.  DD Load: Unexpected EOF reading variables\n");
	    return 0;
	}
	if (sscanf(line, "%d", &idx) != 1) {
	    fprintf(stderr, "ERROR.  DD Load: Couldn't read variable index from line '%s'\n", line);
	    return 0;
	}
	variable_list[i] = idx;
    }
    return 1;
}

/**
  @brief Reads BDD from specified file.

  @return 1 if successful, 0 if failed

  @details File assumed to be readable and positioned at start of
  file.  File is not closed by operation.  Must have declared
  sufficient number of variables already in DD.

  @sideeffect Nodes from file are added to DD.

  @see Cudd_bddStore
**/
extern DdNode *Cudd_bddLoad(DdManager *dd, FILE *infile) {
    dd_store_t stype;
    int var_count, leaf_count, node_count, root_id;
    st_table *reverse_map = NULL;
    DdNode *retval = NULL;

    if (!Cudd_loadMetadata(infile, &stype, &var_count, &leaf_count, &node_count, &root_id))
	goto done;

    int i;
    for (i = 0; i < var_count; i++) {
	int idx;
	char buf[MAXLINE];
	char *line = getLine(infile, buf);
	if (!line) {
	    fprintf(stderr, "ERROR.  DD Load: Unexpected EOF reading variables\n");
	    goto done;
	}
	if (sscanf(line, "%d", &idx) != 1) {
	    fprintf(stderr, "ERROR.  DD Load: Couldn't read variable index from line '%s'\n", line);
	    goto done;
	}
	/* Don't record variable */
    }

    reverse_map = st_init_table(st_numcmp, st_numhash);
    if (reverse_map == NULL)
	goto done;


    for (i = 0; i < leaf_count; i++) {
	int id, value;
	DdNode *f = NULL;
	char buf[MAXLINE];
	char *line = getLine(infile, buf);
	if (!line) {
	    fprintf(stderr, "ERROR.  DD Load: Unexpected EOF reading leaves\n");
	    goto done;
	}
	if (sscanf(line, "%d %d", &id, &value) != 2) {
	    fprintf(stderr, "ERROR.  DD Load: Couldn't read leaf data from line '%s'\n", line);
	    goto done;
	}
	if (value == 1)
	    f = DD_ONE(dd);
	else {
	    fprintf(stderr, "ERROR.  DD Load: Invalid leaf value %d for BDD\n", value);
	    goto done;
	}
	if (st_insert(reverse_map, (void *) (long) id, (void *) f) == ST_OUT_OF_MEM) {
	    goto done;
	}
	cuddRef(f);
    }

    for (; i < node_count; i++) {
	int index, bindex, id, tid, eid;
	DdNode *f, *fv, *fnv;
	char buf[MAXLINE];
	char *line = getLine(infile, buf);
	char istring[MAXLINE];
	char sistring[MAXLINE];
	if (!line) {
	    fprintf(stderr, "ERROR.  DD Load: Unexpected EOF reading nodes\n");
	    goto done;
	}
	if (sscanf(line, "%d %s %d %d", &id, istring, &tid, &eid) != 4) {
	    fprintf(stderr, "ERROR.  DD Load: Couldn't read node data from line '%s'\n", line);
	    goto done;
	}
	strcpy(sistring, istring);
	char *bpos = strstr(istring, ":");
	if (bpos == NULL) {
	    if (sscanf(istring, "%d", &index) != 1) {
		fprintf(stderr, "ERROR.  DD Load: Couldn't read node index from line '%s' (substring '%s')\n", line, sistring);
		goto done;
	    }
	    bindex = index;
	} else {
	    *bpos = '\0';
	    if (sscanf(istring, "%d", &index) != 1) {
		fprintf(stderr, "ERROR.  DD Load: Couldn't read node index from line '%s' (substring '%s')\n", line, sistring);
		goto done;
	    }
	    if (sscanf(bpos+1, "%d", &bindex) != 1) {
		fprintf(stderr, "ERROR.  DD Load: Couldn't read node bindex from line '%s' (substring '%s')\n", line, sistring);
		goto done;
	    }
	}
	fv = idToNode(tid, reverse_map);
	if (!fv) {
	    fprintf(stderr, "ERROR.  DD Load: Couldn't find node with ID %d\n", tid);
	    goto done;
	}
	fnv = idToNode(eid, reverse_map);
	if (!fnv) {
	    fprintf(stderr, "ERROR.  DD Load: Couldn't find node with ID %d\n", eid);
	    Cudd_RecursiveDeref(dd, fv);
	    goto done;
	}
	f = cuddBddGenerateNode(dd, index, bindex, fv, fnv, NULL);
	if (f == NULL) {
	    fprintf(stderr, "ERROR.  DD Load: Couldn't generate node %d:%d --> %p, %p\n", index, bindex, fv, fnv);
	    Cudd_RecursiveDeref(dd, fv);
	    Cudd_RecursiveDeref(dd, fnv);
	    goto done;
	}
	cuddRef(f);
	if (st_insert(reverse_map, (void *) (long) id, (void *) f) == ST_OUT_OF_MEM) {
	    goto done;
	}
    }
    retval = idToNode(root_id, reverse_map);
    
 done:
    /* Complete by dereferencing all nodes */
    if (reverse_map != NULL) {
	st_generator *gen;
	void *key, *value;
	st_foreach_item(reverse_map, gen, &key, &value) {
	    DdNode *f = (DdNode *) value;
	    if (retval == NULL)
		Cudd_RecursiveDeref(dd, f);
	    else
		Cudd_Deref(f);
	}
	st_free_table(reverse_map);
    }
    return(retval);
}

/* Helper function for cuddBddStore.  Performs traversal of DD, assigning node IDs in post order */
static int assign_id_recursive(DdNode *f, st_table *forward_map, st_table *reverse_map, int *counter) {
    DdNode *F = Cudd_Regular(f);
    DdNode *Fv, *Fnv;
    uintptr_t long_counter = 0;
    if (st_is_member(forward_map, F))
	return 1;

    /* Mark node with ID 0 to indicate that it's being visited */
    if (st_insert(forward_map, (void *) F, (void *) long_counter) == ST_OUT_OF_MEM)
	return 0;

    /* Visit children */
    Fv = Cudd_T(F);
    if (!assign_id_recursive(Fv, forward_map, reverse_map, counter))
	return 0;
    Fnv = Cudd_E(F);
    if (!assign_id_recursive(Fnv, forward_map, reverse_map, counter))
	return 0;

    /* Now assign node the next ID */
    long_counter = ++ *counter;
    if (st_insert(forward_map, (void *) F, (void *) long_counter) == ST_OUT_OF_MEM)
	return 0;
    if (st_insert(reverse_map, (void *) long_counter, (void *) F) == ST_OUT_OF_MEM)
	return 0;

    return 1;
}

/*
  Given ID, return node.
  If not found, print error message and return 0
*/
static DdNode *idToNode(int id, st_table *reverse_map) {
    DdNode *f;
    int comp = id < 0;
    if (comp)
	id = -id;
    if (!st_lookup(reverse_map, (void *) (uintptr_t) id, (void *) &f)) {
	fprintf(stderr, "Internal error.  Couldn't find node with ID %d\n", id);
	return NULL;
    }
    if (comp)
	f = Cudd_Not(f);
    return f;
}

/*
  Given Node, return ID.
  If not found, print error message and return 0
 */
static int nodeToId(DdNode *f, st_table *forward_map) {
    DdNode *F = Cudd_Regular(f);
    int id;
    if (!st_lookup_int(forward_map, (void *) F, &id)) {
	fprintf(stderr, "Internal error.  Couldn't find ID for node %p\n", f);
	return 0;
    }
    if (f != F)
	id = -id;
    return id;
}

/* Get non-comment line from file.  Return NULL of EOF */
static char *getLine(FILE *infile, char *buf) {
    char *line = NULL;
    do {
	line = fgets(buf, MAXLINE, infile);
    } while (line && (line[0] == '\0' || line[0] == '#'));

    if (!line) {
	return line;
    }

    int idx;
    for (idx = strlen(line)-1; idx > 0; idx--) {
	if (line[idx] == '\r' || line[idx] == '\n')
	    line[idx] = '\0';
	else
	    break;
    }
    return line;
}

static int show_node(DdNode *f, int id, st_table *forward_map, FILE *outfile) {
    DdNode *F = Cudd_Regular(f);
    int t = F->index;
    int b = F->bindex;
    int tid = nodeToId(Cudd_T(F), forward_map);
    int ok = 1;
    if (tid == 0)
	return 0;
    int eid = nodeToId(Cudd_E(F), forward_map);
    if (eid == 0)
	return 0;
    if (t == b)
	ok = ok && fprintf(outfile, "%d %d %d %d\n", id, t, tid, eid) > 0;
    else
	ok = ok && fprintf(outfile, "%d %d:%d %d %d\n", id, t, b, tid, eid) > 0;	
    return ok;
}
