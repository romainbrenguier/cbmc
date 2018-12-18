/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "guard.h"

#include <ostream>

#include "namespace.h"
#include "expr_util.h"
#include "invariant.h"
#include "simplify_utils.h"
#include "std_expr.h"
#include "symbol_table.h"
#include "make_unique.h"
#include <cudd/cudd.h>
#include <cplusplus/cuddObj.hh>

guardt::guardt(guard_managert &manager)
  : bdd(manager.bdd_manager.bddOne()),
    manager(manager)
{
}

void guardt::guard_expr(exprt &dest) const
{
  if(is_true(*this))
  {
    // do nothing
  }
  else
  {
    if(dest.is_false())
    {
      dest = boolean_negate(as_expr());
    }
    else
    {
      implies_exprt tmp;
      tmp.op0()=as_expr();
      tmp.op1().swap(dest);
      dest.swap(tmp);
    }
  }
}

void guardt::add(const exprt &expr, const namespacet &ns)
{
  PRECONDITION(expr.type().id() == ID_bool);
  bdd = bdd.And(from_expr(expr));
}

guardt &operator -= (guardt &g1, const guardt &g2)
{
  return g1;
  // TODO there should be an operation on BDDs corresponding to that
#if 0
  if(g1.as_expr().id()!=ID_and || g2.as_expr().id()!=ID_and)
    return g1;

  sort_and_join(g1.expr);
  exprt g2_sorted = g2.as_expr();
  sort_and_join(g2_sorted);

  exprt::operandst &op1=g1.expr.operands();
  const exprt::operandst &op2=g2_sorted.operands();

  exprt::operandst::iterator it1=op1.begin();
  for(exprt::operandst::const_iterator
      it2=op2.begin();
      it2!=op2.end();
      ++it2)
  {
    while(it1!=op1.end() && *it1<*it2)
      ++it1;
    if(it1!=op1.end() && *it1==*it2)
      it1=op1.erase(it1);
  }

  g1.expr=conjunction(op1);

  return g1;
#endif
}

guardt &operator |= (guardt &g1, const guardt &g2)
{
  g1.bdd = g1.bdd.Or(g2.bdd);
  return g1;
}
