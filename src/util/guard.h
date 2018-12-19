/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Guard Data Structure

#ifndef CPROVER_UTIL_GUARD_H
#define CPROVER_UTIL_GUARD_H

#include <iosfwd>

#include <memory>

#include "std_expr.h"
#include "cudd/cudd.h"
#include "cplusplus/cuddObj.hh"
#include "make_unique.h"

struct guard_managert
{
  Cudd bdd_manager;
  std::unordered_map<exprt, std::size_t, irep_hash> expr_to_var;
  std::vector<exprt> var_to_expr;
};

class guardt
{
public:
  explicit guardt(guard_managert &manager);
  guardt(const guardt &other) : bdd(other.bdd), manager(other.manager)
  {
  }

  void add(const exprt &expr, const namespacet &ns);

  void append(const guardt &guard, const namespacet &ns)
  {
    add(guard.as_expr(), ns);
  }

  exprt as_expr() const;
  static BDD from_expr(const exprt &);

  void guard_expr(exprt &dest) const;

  friend guardt &operator -= (guardt &g1, const guardt &g2);
  friend guardt &operator |= (guardt &g1, const guardt &g2);

private:
  BDD bdd;
  guard_managert &manager;
};

inline bool is_false(const guardt &g)
{
  return g.as_expr().is_false();
}

#endif // CPROVER_UTIL_GUARD_H
