/**
  @file 

  @ingroup cudd

  @brief %BDD ITE function and satellites.

  @author Fabio Somenzi

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

/* Refactored some of the original functions into simpler ones requiring multiple calls */
static void bddVarToConst (DdNode *f, DdNode **gp, DdNode **hp, DdNode *one);
static int bddVarToCanonical (DdManager *dd, DdNode **fp, DdNode **gp, DdNode **hp);
static int bddVarToCanonicalSimple (DdNode **fp, DdNode **gp, DdNode **hp);

static unsigned int bddTop(DdManager *dd, int n, DdNode * nodes[], unsigned int levels[]);
static unsigned int bddBottom(DdManager *dd, int n, DdNode *nodes[], unsigned int levels[], unsigned int top);
static void bddSimpleCofactor(DdManager * dd, DdNode * f, unsigned int level, DdNode ** fvp, DdNode ** fnvp, unsigned int *indexp);
static int bddSimpleCofactorChained(DdManager *dd, DdNode *f, unsigned int blevel, DdNode **fvp, DdNode **fnvp);

static DdNode *bddGenerateNode(DdManager * dd,  unsigned int index, unsigned int bindex, DdNode *t,  DdNode *e, int *use_idrp);
/** \endcond */


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Implements ITE(f,g,h).

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_addIte Cudd_bddIteConstant Cudd_bddIntersect

*/
DdNode *
Cudd_bddIte(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DdNode * h /**< third operand */)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddBddIteRecur(dd,f,g,h);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_bddIte */


/**
  @brief Implements ITE(f,g,h) unless too many nodes are required.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up or more new nodes than `limit` are
  required.

  @sideeffect None

  @see Cudd_bddIte

*/
DdNode *
Cudd_bddIteLimit(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DdNode * h /**< third operand */,
  unsigned int limit /**< maximum number of new nodes */)
{
    DdNode *res;
    unsigned int saveLimit = dd->maxLive;

    dd->maxLive = (dd->keys - dd->dead) + (dd->keysZ - dd->deadZ) + limit;
    do {
	dd->reordered = 0;
	res = cuddBddIteRecur(dd,f,g,h);
    } while (dd->reordered == 1);
    dd->maxLive = saveLimit;
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_bddIteLimit */


/**
  @brief Implements ITEconstant(f,g,h).

  @return a pointer to the resulting %BDD (which may or may not be
  constant) or DD_NON_CONSTANT.

  @details No new nodes are created.

  @sideeffect None

  @see Cudd_bddIte Cudd_bddIntersect Cudd_bddLeq Cudd_addIteConstant

*/
DdNode *
Cudd_bddIteConstant(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DdNode * h /**< third operand */)
{
    DdNode	 *r, *Fv, *Fnv, *Gv, *Gnv, *Hv, *Hnv, *t, *e, *nodes[3];
    DdNode	 *one = DD_ONE(dd);
    DdNode	 *zero = Cudd_Not(one);
    int		 comple;
    unsigned int topf, topg, toph, v, tops[3];

    statLine(dd);
    /* Trivial cases. */
    if (f == one) 			/* ITE(1,G,H) => G */
	return(g);
    
    if (f == zero)			/* ITE(0,G,H) => H */
	return(h);
    
    /* f now not a constant. */
    bddVarToConst(f, &g, &h, one);	/* possibly convert g or h */
					/* to constants */

    if (g == h) 			/* ITE(F,G,G) => G */
	return(g);

    if (Cudd_IsConstantInt(g) && Cudd_IsConstantInt(h)) 
	return(DD_NON_CONSTANT);	/* ITE(F,1,0) or ITE(F,0,1) */
					/* => DD_NON_CONSTANT */
    
    if (g == Cudd_Not(h))
	return(DD_NON_CONSTANT);	/* ITE(F,G,G') => DD_NON_CONSTANT */
					/* if F != G and F != G' */
    
    /* Refactored */
    comple = bddVarToCanonical(dd, &f, &g, &h);

    nodes[0] = f; nodes[1] = g; nodes[2] = h;
    v = bddTop(dd,3,nodes,tops);
    topf = tops[0]; topg = tops[1]; toph = tops[2];


    /* Cache lookup. */
    r = cuddConstantLookup(dd, DD_BDD_ITE_CONSTANT_TAG, f, g, h);
    if (r != NULL) {
	return(Cudd_NotCond(r,comple && r != DD_NON_CONSTANT));
    }

    /* ITE(F,G,H) = (v,G,H) (non constant) if F = (v,1,0), v < top(G,H). */
    if (topf < topg && topf < toph && cuddT(f) == one && cuddE(f) == zero) {
	return(DD_NON_CONSTANT);
    }

    /* Refactored */
    /* Compute cofactors. */
    bddSimpleCofactor(dd,f,v,&Fv,&Fnv,NULL);
    bddSimpleCofactor(dd,g,v,&Gv,&Gnv,NULL);    
    bddSimpleCofactor(dd,h,v,&Hv,&Hnv,NULL);    

    /* Recursion. */
    t = Cudd_bddIteConstant(dd, Fv, Gv, Hv);
    if (t == DD_NON_CONSTANT || !Cudd_IsConstantInt(t)) {
	cuddCacheInsert(dd, DD_BDD_ITE_CONSTANT_TAG, f, g, h, DD_NON_CONSTANT);
	return(DD_NON_CONSTANT);
    }
    e = Cudd_bddIteConstant(dd, Fnv, Gnv, Hnv);
    if (e == DD_NON_CONSTANT || !Cudd_IsConstantInt(e) || t != e) {
	cuddCacheInsert(dd, DD_BDD_ITE_CONSTANT_TAG, f, g, h, DD_NON_CONSTANT);
	return(DD_NON_CONSTANT);
    }
    cuddCacheInsert(dd, DD_BDD_ITE_CONSTANT_TAG, f, g, h, t);
    return(Cudd_NotCond(t,comple));

} /* end of Cudd_bddIteConstant */


/**
  @brief Returns a function included in the intersection of f and g.

  @details The function computed (if not zero) is a witness that the
  intersection is not empty.  Cudd_bddIntersect tries to build as few
  new nodes as possible. If the only result of interest is whether f
  and g intersect, Cudd_bddLeq should be used instead.

  @sideeffect None

  @see Cudd_bddLeq Cudd_bddIteConstant

*/
DdNode *
Cudd_bddIntersect(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddBddIntersectRecur(dd,f,g);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }

    return(res);

} /* end of Cudd_bddIntersect */


/**
  @brief Computes the conjunction of two BDDs f and g.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddIte Cudd_addApply Cudd_bddAndAbstract Cudd_bddIntersect
  Cudd_bddOr Cudd_bddNand Cudd_bddNor Cudd_bddXor Cudd_bddXnor

*/
DdNode *
Cudd_bddAnd(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddBddAndRecur(dd,f,g);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_bddAnd */


/**
  @brief Computes the conjunction of two BDDs f and g unless too many
  nodes are required.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up or more new nodes than `limit` are
  required.

  @sideeffect None

  @see Cudd_bddAnd

*/
DdNode *
Cudd_bddAndLimit(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  unsigned int limit /**< maximum number of new nodes */)
{
    DdNode *res;
    unsigned int saveLimit = dd->maxLive;

    dd->maxLive = (dd->keys - dd->dead) + (dd->keysZ - dd->deadZ) + limit;
    do {
	dd->reordered = 0;
	res = cuddBddAndRecur(dd,f,g);
    } while (dd->reordered == 1);
    dd->maxLive = saveLimit;
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_bddAndLimit */


/**
  @brief Computes the disjunction of two BDDs f and g.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddIte Cudd_addApply Cudd_bddAnd Cudd_bddNand Cudd_bddNor
  Cudd_bddXor Cudd_bddXnor

*/
DdNode *
Cudd_bddOr(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddBddAndRecur(dd,Cudd_Not(f),Cudd_Not(g));
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    res = Cudd_NotCond(res,res != NULL);
    return(res);

} /* end of Cudd_bddOr */


/**
  @brief Computes the disjunction of two BDDs f and g unless too many
  nodes are required.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up or more new nodes than `limit` are
  required.

  @sideeffect None

  @see Cudd_bddOr

*/
DdNode *
Cudd_bddOrLimit(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  unsigned int limit /**< maximum number of new nodes */)
{
    DdNode *res;
    unsigned int saveLimit = dd->maxLive;

    dd->maxLive = (dd->keys - dd->dead) + (dd->keysZ - dd->deadZ) + limit;
    do {
	dd->reordered = 0;
	res = cuddBddAndRecur(dd,Cudd_Not(f),Cudd_Not(g));
    } while (dd->reordered == 1);
    dd->maxLive = saveLimit;
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    res = Cudd_NotCond(res,res != NULL);
    return(res);

} /* end of Cudd_bddOrLimit */


/**
  @brief Computes the NAND of two BDDs f and g.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddIte Cudd_addApply Cudd_bddAnd Cudd_bddOr Cudd_bddNor
  Cudd_bddXor Cudd_bddXnor

*/
DdNode *
Cudd_bddNand(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /** second operand */)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddBddAndRecur(dd,f,g);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    res = Cudd_NotCond(res,res != NULL);
    return(res);

} /* end of Cudd_bddNand */


/**
  @brief Computes the NOR of two BDDs f and g.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddIte Cudd_addApply Cudd_bddAnd Cudd_bddOr Cudd_bddNand
  Cudd_bddXor Cudd_bddXnor

*/
DdNode *
Cudd_bddNor(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddBddAndRecur(dd,Cudd_Not(f),Cudd_Not(g));
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_bddNor */


/**
  @brief Computes the exclusive OR of two BDDs f and g.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddIte Cudd_addApply Cudd_bddAnd Cudd_bddOr
  Cudd_bddNand Cudd_bddNor Cudd_bddXnor

*/
DdNode *
Cudd_bddXor(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddBddXorRecur(dd,f,g);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_bddXor */


/**
  @brief Computes the exclusive NOR of two BDDs f and g.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddIte Cudd_addApply Cudd_bddAnd Cudd_bddOr
  Cudd_bddNand Cudd_bddNor Cudd_bddXor

*/
DdNode *
Cudd_bddXnor(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddBddXorRecur(dd,f,Cudd_Not(g));
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_bddXnor */


/**
  @brief Computes the exclusive NOR of two BDDs f and g unless too
  many nodes are required.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up or more new nodes than `limit` are
  required.

  @sideeffect None

  @see Cudd_bddXnor

*/
DdNode *
Cudd_bddXnorLimit(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  unsigned int limit /**< maximum number of new nodes */)
{
    DdNode *res;
    unsigned int saveLimit = dd->maxLive;

    dd->maxLive = (dd->keys - dd->dead) + (dd->keysZ - dd->deadZ) + limit;
    do {
	dd->reordered = 0;
	res = cuddBddXorRecur(dd,f,Cudd_Not(g));
    } while (dd->reordered == 1);
    dd->maxLive = saveLimit;
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_bddXnorLimit */


/**
  @brief Checks whether f is less than or equal to g.

  @return 1 if f is less than or equal to g; 0 otherwise.

  @details No new nodes are created.

  @sideeffect None

  @see Cudd_bddIteConstant Cudd_addEvalConst

*/
int
Cudd_bddLeq(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
    DdNode *one, *zero, *tmp, *fv, *F, *fnv, *gv, *gnv, *nodes[2];
    unsigned int res, v, tops[2];

    statLine(dd);
    /* Terminal cases and normalization. */
    if (f == g) return(1);

    if (Cudd_IsComplement(g)) {
	/* Special case: if f is regular and g is complemented,
	** f(1,...,1) = 1 > 0 = g(1,...,1).
	*/
	if (!Cudd_IsComplement(f)) return(0);
	/* Both are complemented: Swap and complement because
	** f <= g <=> g' <= f' and we want the second argument to be regular.
	*/
	tmp = g;
	g = Cudd_Not(f);
	f = Cudd_Not(tmp);
    } else if (Cudd_IsComplement(f) && g < f) {
	tmp = g;
	g = Cudd_Not(f);
	f = Cudd_Not(tmp);
    }

    /* Now g is regular. */
    one = DD_ONE(dd);
    if (g == one) return(1);	/* no need to test against zero */
    if (f == one) return(0);	/* since at this point g != one */
    if (Cudd_Not(f) == g) return(0); /* because neither is constant */
    zero = Cudd_Not(one);
    if (f == zero) return(1);

    /* Here neither f nor g is constant. */

    /* Check cache. */
    F = Cudd_Regular(f);
    if (F->ref > 1 || g->ref > 1) {
        tmp = cuddCacheLookup2(dd,(DD_CTFP)Cudd_bddLeq,f,g);
        if (tmp != NULL) {
            return(tmp == one);
        }
    }

    /* Refactored */
    nodes[0] = f; nodes[1] = g;
    v = bddTop(dd,2,nodes,tops);

    /* Compute cofactors. */
    bddSimpleCofactor(dd,f,v,&fv,&fnv,NULL);
    bddSimpleCofactor(dd,g,v,&gv,&gnv,NULL);    

    /* Recursive calls. Since we want to maximize the probability of
    ** the special case f(1,...,1) > g(1,...,1), we consider the negative
    ** cofactors first. Indeed, the complementation parity of the positive
    ** cofactors is the same as the one of the parent functions.
    */
    res = Cudd_bddLeq(dd,fnv,gnv) && Cudd_bddLeq(dd,fv,gv);

    /* Store result in cache and return. */
    if (F->ref > 1 || g->ref > 1)
        cuddCacheInsert2(dd,(DD_CTFP)Cudd_bddLeq,f,g,(res ? one : zero));
    return(res);

} /* end of Cudd_bddLeq */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Implements the recursive step of Cudd_bddIte.

  @return a pointer to the resulting %BDD. NULL if the intermediate
  result blows up or if reordering occurs.

  @sideeffect None

*/
DdNode *
cuddBddIteRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * h)
{
    DdNode	 *one, *zero, *res;
    DdNode	 *r, *Fv, *Fnv, *Gv, *Gnv, *Hv, *Hnv, *t, *e, *nodes[3];
    unsigned int topg, toph;
    unsigned int botf;
    unsigned int index, bindex;
    unsigned int levels[3], level, blevel;
    int		 comple;
    DdNode       *deref_set[6];
    int          use_idr[6];
    int          i, deref_cnt = 0;

    statLine(dd);
    /* Terminal cases. */

    /* One variable cases. */
    if (f == (one = DD_ONE(dd))) 	/* ITE(1,G,H) = G */
	return(g);
    
    if (f == (zero = Cudd_Not(one))) 	/* ITE(0,G,H) = H */
	return(h);
    
    /* From now on, f is known not to be a constant. */
    if (g == one || f == g) {	/* ITE(F,F,H) = ITE(F,1,H) = F + H */
	if (h == zero) {	/* ITE(F,1,0) = F */
	    return(f);
	} else {
	    res = cuddBddAndRecur(dd,Cudd_Not(f),Cudd_Not(h));
	    return(Cudd_NotCond(res,res != NULL));
	}
    } else if (g == zero || f == Cudd_Not(g)) { /* ITE(F,!F,H) = ITE(F,0,H) = !F * H */
	if (h == one) {		/* ITE(F,0,1) = !F */
	    return(Cudd_Not(f));
	} else {
	    res = cuddBddAndRecur(dd,Cudd_Not(f),h);
	    return(res);
	}
    }
    if (h == zero || f == h) {    /* ITE(F,G,F) = ITE(F,G,0) = F * G */
	res = cuddBddAndRecur(dd,f,g);
	return(res);
    } else if (h == one || f == Cudd_Not(h)) { /* ITE(F,G,!F) = ITE(F,G,1) = !F + G */
	res = cuddBddAndRecur(dd,f,Cudd_Not(g));
	return(Cudd_NotCond(res,res != NULL));
    }

    /* Check remaining one variable case. */
    if (g == h) { 		/* ITE(F,G,G) = G */
	return(g);
    } else if (g == Cudd_Not(h)) { /* ITE(F,G,!G) = F <-> G */
	res = cuddBddXorRecur(dd,f,h);
	return(res);
    }
    
    /* Refactored */
    /* From here, there are no constants. */
    comple = bddVarToCanonicalSimple(&f, &g, &h);

    nodes[0] = f; nodes[1] = g; nodes[2] = h;
    level = bddTop(dd, 3, nodes, levels);
    index = cuddII(dd,level);
    topg = levels[1]; toph = levels[2];

    /* Chaining support */
    blevel = bddBottom(dd, 3, nodes, levels, level);
    bindex = cuddII(dd,blevel);
    botf = levels[0];

    /* A shortcut: ITE(F,G,H) = (t:b,G,H) if F = (t:b,1,0), b < top(G,H). */
    if (botf < topg && botf < toph && cuddT(f) == one && cuddE(f) == zero) {
	r = cuddUniqueInterChained(dd, (int) f->index, (int) f->bindex, g, h);
	if (r == NULL)
	    goto cleanup;
	return(Cudd_NotCond(r,comple));
    }

    /* Check cache. */
    r = cuddCacheLookup(dd, DD_BDD_ITE_TAG, f, g, h);
    if (r != NULL) {
	return(Cudd_NotCond(r,comple));
    }

    checkWhetherToGiveUp(dd);

    /* r is now NULL */

    /* Compute cofactors. */
    if (bddSimpleCofactorChained(dd,f,blevel,&Fv,&Fnv)) {
	use_idr[deref_cnt] = 1;
	deref_set[deref_cnt++] = Fnv;
    }
    if (Fnv == NULL)
	goto cleanup;

    if (bddSimpleCofactorChained(dd,g,blevel,&Gv,&Gnv)) {
	use_idr[deref_cnt] = 1;
	deref_set[deref_cnt++] = Gnv;
    }
    if (Gnv == NULL)
	goto cleanup;

    if (bddSimpleCofactorChained(dd,h,blevel,&Hv,&Hnv)) {
	use_idr[deref_cnt] = 1;
	deref_set[deref_cnt++] = Hnv;
    }
    if (Hnv == NULL)
	goto cleanup;

    /* Recursive step. */
    t = cuddBddIteRecur(dd,Fv,Gv,Hv);
    if (t == NULL)
	goto cleanup;
    cuddRef(t);
    use_idr[deref_cnt] = 0;
    deref_set[deref_cnt++] = t;

    e = cuddBddIteRecur(dd,Fnv,Gnv,Hnv);
    if (e == NULL)
	goto cleanup;
    cuddRef(e);
    
    r = bddGenerateNode(dd,index,bindex,t,e, &use_idr[deref_cnt]);
    deref_set[deref_cnt++] = e;

 cleanup:
    /* Dereference intermediate nodes */
    if (r == NULL) {
	for (i = 0; i < deref_cnt; i++)
	    Cudd_IterDerefBdd(dd, deref_set[i]);
	return r;
    } else {
	cuddRef(r);
	for (i = 0; i < deref_cnt; i++) {
	    if (use_idr[i])
		Cudd_IterDerefBdd(dd, deref_set[i]);
	    else
		cuddDeref(deref_set[i]);
	}
	cuddCacheInsert(dd, DD_BDD_ITE_TAG, f, g, h, r);
	cuddDeref(r);
	return(Cudd_NotCond(r,comple));
    }

} /* end of cuddBddIteRecur */


/**
  @brief Implements the recursive step of Cudd_bddIntersect.

  @sideeffect None

  @see Cudd_bddIntersect

*/
DdNode *
cuddBddIntersectRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * g)
{
    DdNode *res;
    DdNode *t, *e;
    DdNode *fv, *fnv, *gv, *gnv;
    DdNode *one, *zero;
    DdNode *nodes[2];
    unsigned int index, v, tops[2];

    statLine(dd);
    one = DD_ONE(dd);
    zero = Cudd_Not(one);

    /* Terminal cases. */
    if (f == zero || g == zero || f == Cudd_Not(g)) return(zero);
    if (f == g || g == one) return(f);
    if (f == one) return(g);

    /* At this point f and g are not constant. */
    if (f > g) { DdNode *tmp = f; f = g; g = tmp; }
    res = cuddCacheLookup2(dd,Cudd_bddIntersect,f,g);
    if (res != NULL) return(res);

    checkWhetherToGiveUp(dd);

    /* Find splitting variable. */
    nodes[0] = f; nodes[1] = g;
    v = bddTop(dd,2,nodes,tops);

    /* Compute cofactors. */
    index = 0; /* Suppresses compiler warning */
    bddSimpleCofactor(dd,f,v,&fv,&fnv,&index);
    bddSimpleCofactor(dd,g,v,&gv,&gnv,&index);    

    /* Compute partial results. */
    t = cuddBddIntersectRecur(dd,fv,gv);
    if (t == NULL) return(NULL);
    cuddRef(t);
    if (t != zero) {
	e = zero;
    } else {
	e = cuddBddIntersectRecur(dd,fnv,gnv);
	if (e == NULL) {
	    Cudd_IterDerefBdd(dd, t);
	    return(NULL);
	}
    }
    cuddRef(e);

    res = bddGenerateNode(dd,index,index,t,e,NULL);

    if (res == NULL) return (NULL);

    cuddDeref(e);
    cuddDeref(t);

    cuddCacheInsert2(dd,Cudd_bddIntersect,f,g,res);

    return(res);

} /* end of cuddBddIntersectRecur */


/**
  @brief Implements the recursive step of Cudd_bddAnd.

  @details Takes the conjunction of two BDDs.

  @return a pointer to the result is successful; NULL otherwise.

  @sideeffect None

  @see Cudd_bddAnd

*/
DdNode *
cuddBddAndRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * g)
{
    DdNode *F, *fv, *fnv, *G, *gv, *gnv, *nodes[2];
    DdNode *one, *zero, *r, *t, *e;
    unsigned int levels[2], level, blevel;
    unsigned int index, bindex;
    DdNode       *deref_set[4];
    int          use_idr[4];
    int          i, deref_cnt = 0;

    statLine(manager);
    one = DD_ONE(manager);
    zero = Cudd_Not(one);

    /* Terminal cases. */
    F = Cudd_Regular(f);
    G = Cudd_Regular(g);
    if (F == G) {
	if (f == g) return(f);
	else return(zero);
    }
    if (F == one) {
	if (f == one) return(g);
	else return(f);
    }
    if (G == one) {
	if (g == one) return(f);
	else return(g);
    }

    /* At this point f and g are not constant. */
    if (f > g) { /* Try to increase cache efficiency. */
	DdNode *tmp = f;
	f = g;
	g = tmp;
	F = Cudd_Regular(f);
	G = Cudd_Regular(g);
    }

    /* Check cache. */
    if (F->ref != 1 || G->ref != 1) {
	r = cuddCacheLookup2(manager, Cudd_bddAnd, f, g);
	if (r != NULL) return(r);
    }

    checkWhetherToGiveUp(manager);

    /* r == NULL */

    nodes[0] = f; nodes[1] = g;
    level = bddTop(manager,2,nodes,levels);
    index = cuddII(manager,level);
    blevel = bddBottom(manager,2,nodes,levels,level);
    bindex = cuddII(manager,blevel);

    /* Compute cofactors. */
    if (bddSimpleCofactorChained(manager,f,blevel,&fv,&fnv)) {
	use_idr[deref_cnt] = 1;
	deref_set[deref_cnt++] = fnv;
    }
    if (fnv == NULL)
	goto cleanup;

    if (bddSimpleCofactorChained(manager,g,blevel,&gv,&gnv)) {
	use_idr[deref_cnt] = 1;
	deref_set[deref_cnt++] = gnv;
    }
    if (gnv == NULL)
	goto cleanup;

    t = cuddBddAndRecur(manager, fv, gv);
    if (t == NULL)
	goto cleanup;
    cuddRef(t);
    use_idr[deref_cnt] = 0;
    deref_set[deref_cnt++] = t;

    e = cuddBddAndRecur(manager, fnv, gnv);
    if (e == NULL) {
	goto cleanup;
    }
    cuddRef(e);

    r = bddGenerateNode(manager,index,bindex,t,e, &use_idr[deref_cnt]);
    deref_set[deref_cnt++] = e;

 cleanup:
    if (r == NULL) {
	for (i = 0; i < deref_cnt; i++)
	    Cudd_IterDerefBdd(manager, deref_set[i]);
    } else {
	cuddRef(r);
	for (i = 0; i < deref_cnt; i++) {
	    if (use_idr[i])
		Cudd_IterDerefBdd(manager, deref_set[i]);
	    else
		cuddDeref(deref_set[i]);
	}
	if (F->ref != 1 || G->ref != 1)
	    cuddCacheInsert2(manager, Cudd_bddAnd, f, g, r);
	cuddDeref(r);
    }

    return(r);

} /* end of cuddBddAndRecur */


/**
  @brief Implements the recursive step of Cudd_bddXor.

  @details Takes the exclusive OR of two BDDs.

  @return a pointer to the result is successful; NULL otherwise.

  @sideeffect None

  @see Cudd_bddXor

*/
DdNode *
cuddBddXorRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * g)
{
    DdNode *fv, *fnv, *gv, *gnv, *nodes[2];
    DdNode *one, *zero, *r, *t, *e, *F, *G;
    unsigned int levels[2], level, blevel;
    unsigned int index, bindex;
    DdNode       *deref_set[4];
    int          use_idr[4];
    int          i, deref_cnt = 0;

    statLine(manager);
    one = DD_ONE(manager);
    zero = Cudd_Not(one);

    /* Terminal cases. */
    if (f == g) return(zero);
    if (f == Cudd_Not(g)) return(one);
    if (f > g) { /* Try to increase cache efficiency and simplify tests. */
	DdNode *tmp = f;
	f = g;
	g = tmp;
    }
    if (g == zero) return(f);
    if (g == one) return(Cudd_Not(f));
    if (Cudd_IsComplement(f)) {
	f = Cudd_Not(f);
	g = Cudd_Not(g);
    }
    /* Now the first argument is regular. */
    if (f == one) return(Cudd_Not(g));

    /* At this point f and g are not constant. */

    /* Check cache. */
    r = cuddCacheLookup2(manager, Cudd_bddXor, f, g);
    if (r != NULL) return(r);

    checkWhetherToGiveUp(manager);

    /* r == NULL */

    nodes[0] = f; nodes[1] = g;
    level = bddTop(manager,2,nodes,levels);
    index = cuddII(manager,level);
    blevel = bddBottom(manager,2,nodes,levels,level);
    bindex = cuddII(manager,blevel);

    /* Compute cofactors. */
    if (bddSimpleCofactorChained(manager,f,blevel,&fv,&fnv)) {
	use_idr[deref_cnt] = 1;
	deref_set[deref_cnt++] = fnv;
    }
    if (fnv == NULL)
	goto cleanup;

    if (bddSimpleCofactorChained(manager,g,blevel,&gv,&gnv)) {
	use_idr[deref_cnt] = 1;
	deref_set[deref_cnt++] = gnv;
    }
    if (gnv == NULL)
	goto cleanup;

    t = cuddBddXorRecur(manager, fv, gv);
    if (t == NULL)
	goto cleanup;
    cuddRef(t);
    use_idr[deref_cnt] = 0;
    deref_set[deref_cnt++] = t;

    e = cuddBddXorRecur(manager, fnv, gnv);
    if (e == NULL)
	goto cleanup;
    cuddRef(e);

    r = bddGenerateNode(manager,index,bindex,t,e, &use_idr[deref_cnt]);
    deref_set[deref_cnt++] = e;

 cleanup:
    if (r == NULL) {
	for (i = 0; i < deref_cnt; i++)
	    Cudd_IterDerefBdd(manager, deref_set[i]);
    } else {
	cuddRef(r);
	for (i = 0; i < deref_cnt; i++) {
	    if (use_idr[i]) 
		Cudd_IterDerefBdd(manager, deref_set[i]);
	    else
		cuddDeref(deref_set[i]);
	}
	F = Cudd_Regular(f);
	G = Cudd_Regular(g);
	if (F->ref != 1 || G->ref != 1)
	    cuddCacheInsert2(manager, Cudd_bddXor, f, g, r);
	cuddDeref(r);
    }
    return(r);

} /* end of cuddBddXorRecur */


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**
  @brief Replaces variables with constants if possible.

  @details This function performs part of the transformation to
  standard form by replacing variables with constants if possible.

  @sideeffect None

  @see bddVarToCanonical bddVarToCanonicalSimple

*/
static void
bddVarToConst(
  DdNode * f,
  DdNode ** gp,
  DdNode ** hp,
  DdNode * one)
{
    DdNode *g = *gp;
    DdNode *h = *hp;

    if (f == g) {    /* ITE(F,F,H) = ITE(F,1,H) = F + H */
	*gp = one;
    } else if (f == Cudd_Not(g)) {    /* ITE(F,!F,H) = ITE(F,0,H) = !F * H */
	*gp = Cudd_Not(one);
    }
    if (f == h) {    /* ITE(F,G,F) = ITE(F,G,0) = F * G */
	*hp = Cudd_Not(one);
    } else if (f == Cudd_Not(h)) {    /* ITE(F,G,!F) = ITE(F,G,1) = !F + G */
	*hp = one;
    }

} /* end of bddVarToConst */


/**
  @brief Picks unique member from equiv expressions.

  @details Reduces 2 variable expressions to canonical form.

  @sideeffect None

  @see bddVarToConst bddVarToCanonicalSimple

*/
static int
bddVarToCanonical(
  DdManager * dd,
  DdNode ** fp,
  DdNode ** gp,
  DdNode ** hp)
{
    DdNode	*F, *G, *H, *r, *f, *g, *h;
    DdNode	*one = dd->one;
    unsigned int topf, topg, toph;
    int		comple, change;

    f = *fp;
    g = *gp;
    h = *hp;
    F = Cudd_Regular(f);
    G = Cudd_Regular(g);
    H = Cudd_Regular(h);
    topf = cuddI(dd,F->index);
    topg = cuddI(dd,G->index);
    toph = cuddI(dd,H->index);

    change = 0;

    if (G == one) {			/* ITE(F,c,H) */
	if ((topf > toph) || (topf == toph && f > h)) {
	    r = h;
	    h = f;
	    f = r;			/* ITE(F,1,H) = ITE(H,1,F) */
	    if (g != one) {	/* g == zero */
		f = Cudd_Not(f);		/* ITE(F,0,H) = ITE(!H,0,!F) */
		h = Cudd_Not(h);
	    }
	    change = 1;
	}
    } else if (H == one) {		/* ITE(F,G,c) */
	if ((topf > topg) || (topf == topg && f > g)) {
	    r = g;
	    g = f;
	    f = r;			/* ITE(F,G,0) = ITE(G,F,0) */
	    if (h == one) {
		f = Cudd_Not(f);		/* ITE(F,G,1) = ITE(!G,!F,1) */
		g = Cudd_Not(g);
	    }
	    change = 1;
	}
    } else if (g == Cudd_Not(h)) {	/* ITE(F,G,!G) = ITE(G,F,!F) */
	if ((topf > topg) || (topf == topg && f > g)) {
	    r = f;
	    f = g;
	    g = r;
	    h = Cudd_Not(r);
	    change = 1;
	}
    }
    /* adjust pointers so that the first 2 arguments to ITE are regular */
    if (Cudd_IsComplement(f) != 0) {	/* ITE(!F,G,H) = ITE(F,H,G) */
	f = Cudd_Not(f);
	r = g;
	g = h;
	h = r;
	change = 1;
    }
    comple = 0;
    if (Cudd_IsComplement(g) != 0) {	/* ITE(F,!G,H) = !ITE(F,G,!H) */
	g = Cudd_Not(g);
	h = Cudd_Not(h);
	change = 1;
	comple = 1;
    }
    if (change != 0) {
	*fp = f;
	*gp = g;
	*hp = h;
    }

    return(comple);

} /* end of bddVarToCanonical */


/**
  @brief Picks unique member from equiv expressions.

  @details Makes sure the first two pointers are regular.  This
  mat require the complementation of the result, which is signaled by
  returning 1 instead of 0.  This function is simpler than the general
  case because it assumes that no two arguments are the same or
  complementary, and no argument is constant.

  @sideeffect None

  @see bddVarToConst bddVarToCanonical

*/
static int
bddVarToCanonicalSimple(
  DdNode ** fp,
  DdNode ** gp,
  DdNode ** hp)
{
    DdNode	*r, *f, *g, *h;
    int		comple, change;

    f = *fp;
    g = *gp;
    h = *hp;

    change = 0;

    /* adjust pointers so that the first 2 arguments to ITE are regular */
    if (Cudd_IsComplement(f)) {	/* ITE(!F,G,H) = ITE(F,H,G) */
	f = Cudd_Not(f);
	r = g;
	g = h;
	h = r;
	change = 1;
    }
    comple = 0;
    if (Cudd_IsComplement(g)) {	/* ITE(F,!G,H) = !ITE(F,G,!H) */
	g = Cudd_Not(g);
	h = Cudd_Not(h);
	change = 1;
	comple = 1;
    }
    if (change) {
	*fp = f;
	*gp = g;
	*hp = h;
    }

    return(comple);

} /* end of bddVarToCanonicalSimple */


/**
  @brief Finds top levels for a set of nodes.

  @return Minimum level found

  @sideeffect Sets elements of levels to the top levels of the corresponding nodes

  @see bddBottom

*/
static unsigned int
bddTop(
  DdManager  * dd,
  int n,
  DdNode * nodes[],
  unsigned int levels[])
{
    int         i, flevel, level;
    DdNode      *f, *F;
    level = CUDD_MAXINDEX;
    for (i = 0; i < n; i++) {
	f = nodes[i];
	F = Cudd_Regular(f);
	flevel = cuddI(dd,F->index);
	level = ddMin(level, flevel);
	levels[i] = flevel;
    }
    return (level);
} /* end of bddTop */


/**
  @brief Finds bottom levels for a set of nodes.

  @return New bottom level for splitting a set of nodes

  @sideeffect None

  @see bddTop
*/
static unsigned int
bddBottom(
  DdManager  * dd,
  int n,
  DdNode * nodes[],
  unsigned int levels[],
  unsigned int top)
{
    int         i, fblevel, blevel;
    DdNode      *F;
    blevel = CUDD_CONST_INDEX;
    for (i = 0; i < n; i++) {
	F = Cudd_Regular(nodes[i]);
	if (Cudd_IsConstant(F))
	    fblevel = CUDD_CONST_INDEX;
	else if (levels[i] == top)
	    fblevel = cuddI(dd,F->bindex);
	else
	    fblevel = levels[i]-1;
	blevel = ddMin(blevel, fblevel);
    }
    return (blevel);
} /* end of bddBottom */

/**
  @brief Get cofactors with respect to variable (given its level)
         for case where result is either node or its child

  @return None

  @sideeffect Sets *fvp & *fnvp to the two cofactors.
  If indexp non-NULL, sets *indexp to node index if it is at this level.

  @see bddSimpleCofactorChained

*/
static void
bddSimpleCofactor(
  DdManager * dd,
  DdNode * f,
  unsigned int level,
  DdNode ** fvp,
  DdNode ** fnvp,
  unsigned int * indexp)
{
    DdNode *F, *Fv, *Fnv;
    unsigned int flevel;
    int comple;
    F = Cudd_Regular(f);
    comple = Cudd_IsComplement(f);
    flevel = cuddI(dd,F->index);

    if (flevel == level) {
	if (indexp) {
	    *indexp = F->index;
	}
	Fv = cuddT(F);
	Fnv = cuddE(F);
    } else {
	Fv = Fnv = F;
    }
    *fvp = Cudd_NotCond(Fv,comple);
    *fnvp = Cudd_NotCond(Fnv, comple);

}  /* End of bddSimpleCofactor */


/**
  @brief Get cofactors of chain node so that top levels >= blevel+1

  @return 1 if cofactoring generated new else node

  @sideeffect Sets *fvp & *fnvp to the two cofactors.

  @see bddSimpleCofactor

*/
static int
bddSimpleCofactorChained(
  DdManager * dd,
  DdNode * f,
  unsigned int blevel,
  DdNode ** fvp,
  DdNode ** fnvp)
{
    DdNode *F, *Fv, *Fnv, *fnvt, *fnve;
    unsigned int findex, flevel, fbindex, fblevel, nindex;
    int comple;
    int new_ref = 0;

    F = Cudd_Regular(f);
    comple = Cudd_IsComplement(f);
    findex = F->index;
    flevel = cuddI(dd,findex);
    fbindex = F->bindex;
    fblevel = cuddI(dd,fbindex);

    if (blevel < flevel) {
	/* No splitting required */
	Fv = Fnv = F;	
    } else if (blevel == fblevel) {
	/* Splitting parameters match this node */
	Fv = cuddT(F);
	Fnv = cuddE(F);
    } else {
	/* blevel < fblevel */
	/* Must construct new node for E child */
	Fv = fnvt = cuddT(F);
	fnve = cuddE(F);
	nindex = cuddII(dd, blevel + 1);
	Fnv = cuddUniqueInterChained(dd,(int)nindex,(int)fbindex,fnvt,fnve);
	if (Fnv == NULL) 
	    return 0;
	//	printf("Cofactored node %p with indices %d:%d into one %p with indices %d:%d\n",
	//	       f, findex, fbindex, Fnv, nindex, fbindex);
	/* Create reference for it */
	cuddRef(Fnv);
	new_ref = 1;
    }
    *fvp = Cudd_NotCond(Fv,comple);
    *fnvp = Cudd_NotCond(Fnv,comple);

    return new_ref;
}

/**
  @brief Find or generate node with specified index, bindex, and children

` @returns pointer to appropriate node

  @sideeffect Stores any newly generated node in unique table
  
  @see cuddUniqueInter

*/

static DdNode *
bddGenerateNode(
  DdManager * dd,
  unsigned int index,
  unsigned int bindex,
  DdNode *t,
  DdNode *e,
  int    *use_idrp)
{
    DdNode *r = NULL;
    int comple;
    DdNode *et, *ee;
    unsigned int blevel, elevel, ebindex;
    int use_idr = 0;

    if (t == e)
	return (t);   /* Don't care reduction rule */
    comple = Cudd_IsComplement(t);
    if (comple) {
	t = Cudd_Not(t);
	e = Cudd_Not(e);
    }

    /* See if can do chain compression */
    if (!Cudd_IsConstant(e) && !Cudd_IsComplement(e)) {
	et = Cudd_T(e);
	if (et == t &&
	    (dd->chaining == CUDD_CHAIN_ALL ||
	     (dd->chaining == CUDD_CHAIN_CONSTANT && Cudd_IsConstant(t)))) {
	    blevel = cuddI(dd,bindex);
	    elevel = cuddI(dd,e->index);
	    if (elevel == blevel+1) {
		ebindex = e->bindex;
		ee = Cudd_E(e);
		cuddRef(ee);
		r = cuddUniqueInterChained(dd,(int)index,(int)ebindex,t,ee);
		cuddDeref(ee);
		use_idr = 1;
		//		printf("Chained %u:%u+%u:%u.  Replace %p by %p\n",
		//		cuddI(dd,index), blevel, elevel, cuddI(dd,ebindex),
		//		       e, ee);
	    }
	}
    }

    if (r == NULL) {
	r = cuddUniqueInterChained(dd,(int)index,(int)bindex,t,e);
	if (r == NULL) {
	    Cudd_IterDerefBdd(dd, t);
	    Cudd_IterDerefBdd(dd, e);
	    if (use_idrp)
		*use_idrp = 0;
	    return(NULL);
	}
    }
    if (comple)
	r = Cudd_Not(r);

    if (use_idrp)
	*use_idrp = use_idr;

    return(r);
} /* End of bddGenerateNode */
