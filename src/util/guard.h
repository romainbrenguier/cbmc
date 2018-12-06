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
#include "bdd_expr.h"
#include "make_unique.h"

class guardt
{
public:
  explicit guardt() {};
  guardt(const guardt &other)
  {
    if(other.bdd != nullptr)
    {
      bdd = util_make_unique<bdd_exprt>(*other.bdd);
    }
  }

  guardt& operator=(guardt &&other)
  {
    bdd = std::move(other.bdd);
    return *this;
  }

  guardt& operator=(const guardt &other)
  {
    if(other.bdd != nullptr)
      bdd = util_make_unique<bdd_exprt>(*other.bdd);
    else
      bdd = nullptr;
    return *this;
  }

  void add(const exprt &expr, const namespacet &ns);

  void append(const guardt &guard, const namespacet &ns)
  {
    add(guard.as_expr(), ns);
  }

  exprt as_expr() const
  {
    if(bdd)
      return bdd->as_expr();
    return true_exprt();
  }

  void guard_expr(exprt &dest) const;

  friend guardt &operator -= (guardt &g1, const guardt &g2);
  friend guardt &operator |= (guardt &g1, const guardt &g2);

private:
  std::unique_ptr<bdd_exprt> bdd = nullptr;
};

inline bool is_true(const guardt &g)
{
  return g.as_expr().is_true();
}

inline bool is_false(const guardt &g)
{
  return g.as_expr().is_false();
}

#endif // CPROVER_UTIL_GUARD_H
