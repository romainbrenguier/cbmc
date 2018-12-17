/*******************************************************************\

Module: Conversion between exprt and CUDD BDDs

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Conversion between exprt and CUDD BDDS

#ifndef CPROVER_SOLVERS_PROP_BDD_EXPR_H
#define CPROVER_SOLVERS_PROP_BDD_EXPR_H

#include <util/expr.h>

#include <memory>
#include <unordered_map>
#include <cudd/cudd.h>
#include <cplusplus/cuddObj.hh>

/// Converter between exprt and BDDs
class bdd_expr_convertert final
{
public:
  bdd_expr_convertert();

  BDD from_expr(const exprt &expr);
  exprt as_expr(BDD bdd) const;

private:
  // Map expressions to variable indices of the BDD
  std::unordered_map<exprt, unsigned int, irep_hash> expr_map;
  std::map<unsigned int, exprt> node_map;

  exprt as_expr(DdNode * root) const;
};

#endif // CPROVER_SOLVERS_PROP_BDD_EXPR_H
