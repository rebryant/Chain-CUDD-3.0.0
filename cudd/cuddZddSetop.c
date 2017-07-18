/**
  @file

  @ingroup cudd

  @brief Set operations on ZDDs.

  @author Hyong-Kyoon Shin, In-Ho Moon

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

#include "util.h"
#include "cuddInt.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/


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

/** \cond */

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static DdNode * zdd_subset1_aux (DdManager *zdd, DdNode *P, DdNode *zvar);
static DdNode * zdd_subset0_aux (DdManager *zdd, DdNode *P, DdNode *zvar);
static void zddVarToConst (DdNode *f, DdNode **gp, DdNode **hp, DdNode *base, DdNode *empty);

static unsigned int zddTop(DdManager *dd, int n, DdNode * nodes[], unsigned int levels[]);
static unsigned int zddBottom(DdManager *dd, int n, DdNode *nodes[], unsigned int levels[], unsigned int top);
static void zddSimpleCofactor(DdManager *dd, DdNode *f, unsigned int level, DdNode **fvp, DdNode **fvnp);

/*
  Type declarations for component functions
 */

typedef DdNode *(*DdNodeCaseFun) (DdManager *dd, DdNode *P, DdNode *Q, DdNode *base);
typedef DdNode *(*DdNodeFun) (DdManager *dd, DdNode *P, DdNode *Q);
 
/* Component functions for set operations */
static DdNode *cuddZddSetop2(DdManager *dd, DdNode *P, DdNode *Q, DdNodeCaseFun cfun, DdNodeFun fun);
static DdNode *cuddZddUnionCases(DdManager *dd, DdNode *P, DdNode *Q, DdNode *base);
static DdNode *cuddZddIntersectCases(DdManager *dd, DdNode *P, DdNode *Q, DdNode *base);
static DdNode *cuddZddDiffCases(DdManager *dd, DdNode *P, DdNode *Q, DdNode *base);
static DdNode *cuddZddSymmetricDiffCases(DdManager *dd, DdNode *P, DdNode *Q, DdNode *base);


/** \endcond */

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Computes the ITE of three ZDDs.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
Cudd_zddIte(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * h)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddZddIte(dd, f, g, h);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_zddIte */


/**
  @brief Computes the union of two ZDDs.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
Cudd_zddUnion(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddZddUnion(dd, P, Q);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_zddUnion */


/**
  @brief Computes the intersection of two ZDDs.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
Cudd_zddIntersect(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddZddIntersect(dd, P, Q);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_zddIntersect */


/**
  @brief Computes the difference of two ZDDs.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
Cudd_zddDiff(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddZddDiff(dd, P, Q);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_zddDiff */

/**
  @brief Computes the symmetric difference (xor) of two ZDDs.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
Cudd_zddSymmetricDiff(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddZddSymmetricDiff(dd, P, Q);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_zddSymmetricDiff */


/**
  @brief Performs the inclusion test for ZDDs (P implies Q).

  @details No new nodes are generated by this procedure.

  @return empty if true; a valid pointer different from empty or
  DD_NON_CONSTANT otherwise.

  @sideeffect None

  @see Cudd_zddDiff

*/
DdNode *
Cudd_zddDiffConst(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    unsigned int p_top, q_top, level, levels[2];
    DdNode	*t, *r, *nodes[2];
    DdNode *empty = DD_ZERO(dd);
    DdNode *tautology;

    statLine(zdd);

    nodes[0] = P; nodes[1] = Q;
    level = zddTop(dd, 2, nodes, levels);
    
    tautology = (level == CUDD_MAXINDEX) ? DD_ONE(dd) : dd->univ[level];


    r = cuddZddDiffCases(dd, P, Q, tautology);

    if (r != NULL)
	return r;

    /* Check cache.  The cache is shared by cuddZddDiff(). */
    r = cuddCacheLookup2Zdd(dd, cuddZddDiff, P, Q);
    if (r != NULL)
	return(r);

    p_top = levels[0];
    q_top = levels[1];

    if (p_top < q_top) {
	r = DD_NON_CONSTANT;
    } else if (p_top > q_top) {
	r = Cudd_zddDiffConst(dd, P, cuddE(Q));
    } else {
	t = Cudd_zddDiffConst(dd, cuddT(P), cuddT(Q));
	if (t != empty)
	    r = DD_NON_CONSTANT;
	else
	    r = Cudd_zddDiffConst(dd, cuddE(P), cuddE(Q));
    }
    if (r != DD_NON_CONSTANT)
	cuddCacheInsert2(dd, cuddZddDiff, P, Q, r);

    return(r);

} /* end of Cudd_zddDiffConst */


/**
  @brief Computes the positive cofactor of a %ZDD w.r.t. a variable.

  @details In terms of combinations, the result is the set of all
  combinations in which the variable is asserted.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_zddSubset0

*/
DdNode *
Cudd_zddSubset1(
  DdManager * dd,
  DdNode * P,
  int  var)
{
    DdNode	*r;

    do {
	dd->reordered = 0;
	r = cuddZddSubset1(dd, P, var);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }

    return(r);

} /* end of Cudd_zddSubset1 */


/**
  @brief Computes the negative cofactor of a %ZDD w.r.t. a variable.

  @details In terms of combinations, the result is the set of all
  combinations in which the variable is negated.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_zddSubset1

*/
DdNode *
Cudd_zddSubset0(
  DdManager * dd,
  DdNode * P,
  int  var)
{
    DdNode	*r;

    do {
	dd->reordered = 0;
	r = cuddZddSubset0(dd, P, var);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }

    return(r);

} /* end of Cudd_zddSubset0 */


/**
  @brief Substitutes a variable with its complement in a %ZDD.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
Cudd_zddChange(
  DdManager * dd,
  DdNode * P,
  int  var)
{
    DdNode	*res;

    if ((unsigned int) var >= CUDD_MAXINDEX - 1) return(NULL);
    
    do {
	dd->reordered = 0;
	res = cuddZddChange(dd, P, var);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_zddChange */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Performs the recursive step of Cudd_zddIte.

  @sideeffect None

*/
DdNode *
cuddZddIte(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * h)
{
    DdNode *tautology, *empty;
    DdNode *r, *Fv, *Fvn, *Gv,*Gvn,*Hv,*Hvn,*t,*e;
    DdNode *nodes[3];
    unsigned int level, levels[3];
    unsigned int index;
    DdNode       *deref_set[2];
    int          i, deref_cnt = 0;


    statLine(dd);
    /* Trivial cases. */
    /* One variable cases. */
    if (f == (empty = DD_ZERO(dd))) {	/* ITE(0,G,H) = H */
	return(h);
    }

    nodes[0] = f; nodes[1] = g; nodes[2] = h;
    level = zddTop(dd, 3, nodes, NULL);
    index = cuddIIZ(dd, level);

    tautology = (level == CUDD_MAXINDEX) ? DD_ONE(dd) : dd->univ[level];
    if (f == tautology) {			/* ITE(1,G,H) = G */
    	return(g);
    }

    /* From now on, f is known to not be a constant. */
    zddVarToConst(f,&g,&h,tautology,empty);

    /* Check remaining one variable cases. */
    if (g == h) {			/* ITE(F,G,G) = G */
	return(g);
    }

    if (g == tautology) {			/* ITE(F,1,0) = F */
	if (h == empty) return(f);
    }

    /* Check cache. */
    r = cuddCacheLookupZdd(dd,DD_ZDD_ITE_TAG,f,g,h);
    if (r != NULL)
	return(r);

    /* Assured that r == NULL */

    /* Compute individual levels.  They may have changed in zddVarToConst. */
    level = zddTop(dd, 3, nodes, levels);

    /* Refactored */
    zddSimpleCofactor(dd, f, level, &Fv, &Fvn);
    zddSimpleCofactor(dd, g, level, &Gv, &Gvn);
    zddSimpleCofactor(dd, h, level, &Hv, &Hvn);
    
    t = cuddZddIte(dd, Fv, Gv, Hv);
    if (t == NULL)
	goto cleanup;
    cuddRef(t);
    deref_set[deref_cnt++] = t;

    e = cuddZddIte(dd, Fvn, Gvn, Hvn);
    if (e == NULL)
	goto cleanup;
    cuddRef(e);
    deref_set[deref_cnt++] = e;

    r = cuddZddGetNode(dd,index,t,e);

 cleanup:
    if (r == NULL) {
	for (i = 0; i < deref_cnt; i++)
	    Cudd_RecursiveDerefZdd(dd, deref_set[i]);
    } else {
	for (i = 0; i < deref_cnt; i++)
	    cuddDeref(deref_set[i]);
	cuddCacheInsert(dd,DD_ZDD_ITE_TAG,f,g,h,r);
    }

    return(r);

} /* end of cuddZddIte */


/**
  @brief Performs the recursive step of Cudd_zddUnion.

  @sideeffect None

*/
DdNode *
cuddZddUnion(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    return cuddZddSetop2(dd, P, Q, cuddZddUnionCases, cuddZddUnion);

} /* end of cuddZddUnion */


/**
  @brief Performs the recursive step of Cudd_zddIntersect.

  @sideeffect None

*/
DdNode *
cuddZddIntersect(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    return cuddZddSetop2(dd, P, Q, cuddZddIntersectCases, cuddZddIntersect);

} /* end of cuddZddIntersect */


/**
  @brief Performs the recursive step of Cudd_zddDiff.

  @sideeffect None

*/
DdNode *
cuddZddDiff(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    return cuddZddSetop2(dd, P, Q, cuddZddDiffCases, cuddZddDiff);
} /* end of cuddZddDiff */

/**
  @brief Performs the recursive step of Cudd_zddSymmetricDiff.

  @sideeffect None

*/
DdNode *
cuddZddSymmetricDiff(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    return cuddZddSetop2(dd, P, Q, cuddZddSymmetricDiffCases, cuddZddSymmetricDiff);
} /* end of cuddZddSymmetricDiff */


/**
  @brief Performs the recursive step of Cudd_zddChange.

  @sideeffect None

*/
DdNode *
cuddZddChangeAux(
  DdManager * zdd,
  DdNode * P,
  DdNode * zvar)
{
    int		top_var, level;
    DdNode	*res, *t, *e;
    DdNode	*base = DD_ONE(zdd);
    DdNode	*empty = DD_ZERO(zdd);

    statLine(zdd);
    if (P == empty)
	return(empty);
    if (P == base)
	return(zvar);

    /* Check cache. */
    res = cuddCacheLookup2Zdd(zdd, cuddZddChangeAux, P, zvar);
    if (res != NULL)
	return(res);

    top_var = zdd->permZ[P->index];
    level = zdd->permZ[zvar->index];

    if (top_var > level) {
	res = cuddZddGetNode(zdd, zvar->index, P, DD_ZERO(zdd));
	if (res == NULL) return(NULL);
    } else if (top_var == level) {
	res = cuddZddGetNode(zdd, zvar->index, cuddE(P), cuddT(P));
	if (res == NULL) return(NULL);
    } else {
	t = cuddZddChangeAux(zdd, cuddT(P), zvar);
	if (t == NULL) return(NULL);
	cuddRef(t);
	e = cuddZddChangeAux(zdd, cuddE(P), zvar);
	if (e == NULL) {
	    Cudd_RecursiveDerefZdd(zdd, t);
	    return(NULL);
	}
	cuddRef(e);
	res = cuddZddGetNode(zdd, P->index, t, e);
	if (res == NULL) {
	    Cudd_RecursiveDerefZdd(zdd, t);
	    Cudd_RecursiveDerefZdd(zdd, e);
	    return(NULL);
	}
	cuddDeref(t);
	cuddDeref(e);
    }

    cuddCacheInsert2(zdd, cuddZddChangeAux, P, zvar, res);

    return(res);

} /* end of cuddZddChangeAux */


/**
  @brief Computes the positive cofactor of a %ZDD w.r.t. a variable.

  @details In terms of combinations, the result is the set of all
  combinations in which the variable is asserted.  cuddZddSubset1
  performs the same function as Cudd_zddSubset1, but does not restart
  if reordering has taken place. Therefore it can be called from
  within a recursive procedure.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

  @see cuddZddSubset0 Cudd_zddSubset1

*/
DdNode *
cuddZddSubset1(
  DdManager * dd,
  DdNode * P,
  int  var)
{
    DdNode	*zvar, *r;
    DdNode	*base, *empty;

    base = DD_ONE(dd);
    empty = DD_ZERO(dd);

    zvar = cuddUniqueInterZdd(dd, var, base, empty);
    if (zvar == NULL) {
	return(NULL);
    } else {
	cuddRef(zvar);
	r = zdd_subset1_aux(dd, P, zvar);
	if (r == NULL) {
	    Cudd_RecursiveDerefZdd(dd, zvar);
	    return(NULL);
	}
	cuddRef(r);
	Cudd_RecursiveDerefZdd(dd, zvar);
    }

    cuddDeref(r);
    return(r);

} /* end of cuddZddSubset1 */


/**
  @brief Computes the negative cofactor of a %ZDD w.r.t. a variable.

  @details In terms of combinations, the result is the set of all
  combinations in which the variable is negated.  cuddZddSubset0
  performs the same function as Cudd_zddSubset0, but does not restart
  if reordering has taken place. Therefore it can be called from
  within a recursive procedure.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

  @see cuddZddSubset1 Cudd_zddSubset0

*/
DdNode *
cuddZddSubset0(
  DdManager * dd,
  DdNode * P,
  int  var)
{
    DdNode	*zvar, *r;
    DdNode	*base, *empty;

    base = DD_ONE(dd);
    empty = DD_ZERO(dd);

    zvar = cuddUniqueInterZdd(dd, var, base, empty);
    if (zvar == NULL) {
	return(NULL);
    } else {
	cuddRef(zvar);
	r = zdd_subset0_aux(dd, P, zvar);
	if (r == NULL) {
	    Cudd_RecursiveDerefZdd(dd, zvar);
	    return(NULL);
	}
	cuddRef(r);
	Cudd_RecursiveDerefZdd(dd, zvar);
    }

    cuddDeref(r);
    return(r);

} /* end of cuddZddSubset0 */


/**
  @brief Substitutes a variable with its complement in a %ZDD.

  @details cuddZddChange performs the same function as Cudd_zddChange,
  but does not restart if reordering has taken place. Therefore it can
  be called from within a recursive procedure.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_zddChange

*/
DdNode *
cuddZddChange(
  DdManager * dd,
  DdNode * P,
  int  var)
{
    DdNode	*zvar, *res;

    zvar = cuddUniqueInterZdd(dd, var, DD_ONE(dd), DD_ZERO(dd));
    if (zvar == NULL) return(NULL);
    cuddRef(zvar);

    res = cuddZddChangeAux(dd, P, zvar);
    if (res == NULL) {
	Cudd_RecursiveDerefZdd(dd,zvar);
	return(NULL);
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd,zvar);
    cuddDeref(res);
    return(res);

} /* end of cuddZddChange */


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**
  @brief Performs the recursive step of Cudd_zddSubset1.

  @sideeffect None

*/
static DdNode *
zdd_subset1_aux(
  DdManager * zdd,
  DdNode * P,
  DdNode * zvar)
{
    int		top_var, level;
    DdNode	*res, *t, *e;
    DdNode	*empty;

    statLine(zdd);
    empty = DD_ZERO(zdd);

    /* Check cache. */
    res = cuddCacheLookup2Zdd(zdd, zdd_subset1_aux, P, zvar);
    if (res != NULL)
	return(res);

    if (cuddIsConstant(P)) {
	res = empty;
	cuddCacheInsert2(zdd, zdd_subset1_aux, P, zvar, res);
	return(res);
    }

    top_var = zdd->permZ[P->index];
    level = zdd->permZ[zvar->index];

    if (top_var > level) {
        res = empty;
    } else if (top_var == level) {
	res = cuddT(P);
    } else {
        t = zdd_subset1_aux(zdd, cuddT(P), zvar);
	if (t == NULL) return(NULL);
	cuddRef(t);
        e = zdd_subset1_aux(zdd, cuddE(P), zvar);
	if (e == NULL) {
	    Cudd_RecursiveDerefZdd(zdd, t);
	    return(NULL);
	}
	cuddRef(e);
        res = cuddZddGetNode(zdd, P->index, t, e);
	if (res == NULL) {
	    Cudd_RecursiveDerefZdd(zdd, t);
	    Cudd_RecursiveDerefZdd(zdd, e);
	    return(NULL);
	}
	cuddDeref(t);
	cuddDeref(e);
    }

    cuddCacheInsert2(zdd, zdd_subset1_aux, P, zvar, res);

    return(res);

} /* end of zdd_subset1_aux */


/**
  @brief Performs the recursive step of Cudd_zddSubset0.

  @sideeffect None

*/
static DdNode *
zdd_subset0_aux(
  DdManager * zdd,
  DdNode * P,
  DdNode * zvar)
{
    int		top_var, level;
    DdNode	*res, *t, *e;

    statLine(zdd);

    /* Check cache. */
    res = cuddCacheLookup2Zdd(zdd, zdd_subset0_aux, P, zvar);
    if (res != NULL)
	return(res);

    if (cuddIsConstant(P)) {
	res = P;
	cuddCacheInsert2(zdd, zdd_subset0_aux, P, zvar, res);
	return(res);
    }

    top_var = zdd->permZ[P->index];
    level = zdd->permZ[zvar->index];

    if (top_var > level) {
        res = P;
    }
    else if (top_var == level) {
        res = cuddE(P);
    }
    else {
        t = zdd_subset0_aux(zdd, cuddT(P), zvar);
	if (t == NULL) return(NULL);
	cuddRef(t);
        e = zdd_subset0_aux(zdd, cuddE(P), zvar);
	if (e == NULL) {
	    Cudd_RecursiveDerefZdd(zdd, t);
	    return(NULL);
	}
	cuddRef(e);
        res = cuddZddGetNode(zdd, P->index, t, e);
	if (res == NULL) {
	    Cudd_RecursiveDerefZdd(zdd, t);
	    Cudd_RecursiveDerefZdd(zdd, e);
	    return(NULL);
	}
	cuddDeref(t);
	cuddDeref(e);
    }

    cuddCacheInsert2(zdd, zdd_subset0_aux, P, zvar, res);

    return(res);

} /* end of zdd_subset0_aux */


/**
  @brief Replaces variables with constants if possible (part of
  canonical form).

  @sideeffect None

*/
static void
zddVarToConst(
  DdNode * f,
  DdNode ** gp,
  DdNode ** hp,
  DdNode * base,
  DdNode * empty)
{
    DdNode *g = *gp;
    DdNode *h = *hp;

    if (f == g) { /* ITE(F,F,H) = ITE(F,1,H) = F + H */
	*gp = base;
    }

    if (f == h) { /* ITE(F,G,F) = ITE(F,G,0) = F * G */
	*hp = empty;
    }

} /* end of zddVarToConst */

/**
  @brief General framework for 2-argument set operations

  @return Result of apply set operation fun to P & Q, with cfun handling special cases

  @sideeffect Adds intermediate results to cache

  @see

*/
static DdNode *
cuddZddSetop2(
	      DdManager *dd,
	      DdNode *P,
	      DdNode *Q,
	      DdNodeCaseFun cfun,
	      DdNodeFun     fun
)
{
    DdNode      *tautology, *t, *e, *r;
    unsigned int level, levels[2];
    unsigned int index;
    DdNode *Pv, *Pvn, *Qv, *Qvn, *nodes[2];
    DdNode *deref_set[2];
    int i, deref_cnt = 0;

    statLine(dd);
    
#if 0
    /* DEBUG */
    if (P == NULL || Q == NULL) {
	printf("Oops.  Setop2: Invalid arguments P=%p, Q=%p\n", P, Q);
    } else {
	printf("Setop2: Arguments P=%p, Q=%p\n", P, Q);
    }
#endif


    nodes[0] = P; nodes[1] = Q;
    level = zddTop(dd, 2, nodes, levels);
    index = cuddIIZ(dd, level);
    
    tautology = (level == CUDD_MAXINDEX) ? DD_ONE(dd) : dd->univ[level];

    r = cfun(dd, P, Q, tautology);

    if (r != NULL)
	return r;

    /* Check cache */
    r = cuddCacheLookup2Zdd(dd, fun, P, Q);
    if (r != NULL)
	return(r);

    /* Guaranteed that r == NULL */

    /* Refactored */
    zddSimpleCofactor(dd, P, level, &Pv, &Pvn);
    zddSimpleCofactor(dd, Q, level, &Qv, &Qvn);

    t = cuddZddSetop2(dd, Pv, Qv, cfun, fun);
    if (t == NULL)
	goto cleanup;
    cuddRef(t);
    deref_set[deref_cnt++] = t;

    e = cuddZddSetop2(dd, Pvn, Qvn, cfun, fun);
    if (e == NULL)
	goto cleanup;
    cuddRef(e);
    deref_set[deref_cnt++] = e;

    r = cuddZddGetNode(dd,index,t,e);

 cleanup:
    if (r == NULL) {
	for (i = 0; i < deref_cnt; i++)
	    Cudd_RecursiveDerefZdd(dd, deref_set[i]);
    } else {
	for (i = 0; i < deref_cnt; i++)
	    cuddDeref(deref_set[i]);
	cuddCacheInsert2(dd, fun, P, Q, r);
    }
    return(r);
}


/**
  @brief Handles special cases for Union

  @return result if special case holds, NULL otherwise

  @sideeffect None

  @see zddZddUnion

*/
static DdNode *
cuddZddUnionCases(
		  DdManager *dd,
		  DdNode *P,
		  DdNode *Q,
		  DdNode *base)
{
    DdNode	*empty = DD_ZERO(dd);
    if (P == empty)
	return(Q);
    if (Q == empty)
	return(P);
    if (P == Q)
	return(P);
    if (P == base)
	return(P);
    if (Q == base)
	return(Q);
    return NULL;
} /* end of cuddZddUnionCases */


/**
  @brief Handles special cases for Intersection

  @return result if special case holds, NULL otherwise

  @sideeffect None

  @see zddZddUnion

*/
static DdNode *
cuddZddIntersectCases(
		  DdManager *dd,
		  DdNode *P,
		  DdNode *Q,
		  DdNode *base)
{
    DdNode	*empty = DD_ZERO(dd);
    if (P == empty)
	return(P);
    if (Q == empty)
	return(Q);
    if (P == Q)
	return(P);
    if (P == base)
	return(Q);
    if (Q == base)
	return(P);
    return NULL;
} /* end of cuddZddIntersectCases */

static DdNode *
cuddZddDiffCases(
		  DdManager *dd,
		  DdNode *P,
		  DdNode *Q,
		  DdNode *base)
{
    DdNode	*empty = DD_ZERO(dd);
    if (P == empty)
	return(P);
    if (Q == empty)
	return(P);
    if (P == Q)
	return(empty);
    if (Q == base)
	return(empty);
    return NULL;
} /* end of cuddZddDiffCases */

static DdNode *
cuddZddSymmetricDiffCases(
		  DdManager *dd,
		  DdNode *P,
		  DdNode *Q,
		  DdNode *base)
{
    DdNode	*empty = DD_ZERO(dd);
    if (P == empty)
	return(Q);
    if (Q == empty)
	return(P);
    if (P == Q)
	return(empty);
    return NULL;
} /* end of cuddZddSymmetricDiffCases */





/**
  @brief Finds top levels for a set of nodes.

  @return Minimum level found

  @sideeffect If levels non-null, sets elements of levels to the top levels of the corresponding nodes

  @see zddBottom

*/
static unsigned int
zddTop(
  DdManager  * dd,
  int n,
  DdNode * nodes[],
  unsigned int levels[])
{
    int         i, flevel, level;
    DdNode      *f;
    level = CUDD_MAXINDEX;
    for (i = 0; i < n; i++) {
	f = nodes[i];
	flevel = cuddIZ(dd,f->index);
	level = ddMin(level, flevel);
	if (levels)
	    levels[i] = flevel;
    }
    return (level);
} /* end of zddTop */


/**
  @brief Finds bottom levels for a set of nodes.

  @return New bottom level for splitting a set of nodes

  @sideeffect None

  @see zddTop
*/
static unsigned int
zddBottom(
  DdManager  * dd,
  int n,
  DdNode * nodes[],
  unsigned int levels[],
  unsigned int top)
{
    int         i, fblevel, blevel;
    DdNode      *f;
    blevel = CUDD_MAXINDEX;
    for (i = 0; i < n; i++) {
	f = nodes[i];
	if (Cudd_IsConstant(f))
	    fblevel = CUDD_CONST_INDEX;
	else if (levels[i] == top)
	    fblevel = cuddIZ(dd,f->bindex);
	else
	    fblevel = levels[i]-1;
	blevel = ddMin(blevel, fblevel);
    }
    return (blevel);
} /* end of zddBottom */


/**
  @brief Get cofactors with respect to variable (given its level)
         for case where result is either node or its child

  @return None

  @sideeffect Sets *fvp & *fvnp to the two cofactors.
  If indexp non-NULL, sets *indexp to node index if it is at this level.

  @see zddSimpleCofactorChained

*/
static void
zddSimpleCofactor(
  DdManager * dd,
  DdNode * f,
  unsigned int level,
  DdNode ** fvp,
  DdNode ** fvnp)
{
    unsigned int flevel;
    DdNode *fv, *fvn;

    flevel = cuddIZ(dd,f->index);

    if (flevel == level) {
	fv = cuddT(f);
	fvn = cuddE(f);
    } else {
	fv = DD_ZERO(dd);
	fvn = f;
    }
    *fvp = fv;
    *fvnp = fvn;
#if 0
    /* DEBUG */
    printf("Cofactoring %p (level = %u) at level %u.  Got T=%p, E=%p\n", f, flevel, level, fv, fvn);
#endif

}  /* End of zddSimpleCofactor */
