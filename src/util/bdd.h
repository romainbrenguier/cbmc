/*******************************************************************\

Module: Binary Decision Diagrams

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Interface to Cudd BDD functions that are used in CBMC
/// To ensure we can easily switch from Cudd to other BDD libraries if needed,
/// the BDD functions should only be accessed from this header file.

#ifndef CPROVER_UTIL_BDD_H
#define CPROVER_UTIL_BDD_H

#include <cplusplus/cuddObj.hh>

class bdd_managert;
class bddt;
class bdd_nodet;

/// Low level access to the structure of the BDD, read-only.
class bdd_nodet
{
public:
  bool is_constant() const
  {
    return Cudd_IsConstant(node) != 0;
  }

  bool is_complement() const
  {
    return Cudd_IsComplement(node) != 0;
  }

  unsigned int index() const
  {
    return Cudd_NodeReadIndex(node);
  }

  bdd_nodet then_branch() const
  {
    return bdd_nodet(Cudd_T(node));
  }

  bdd_nodet else_branch() const
  {
    return bdd_nodet(Cudd_E(node));
  }

  long id() const
  {
    return (long)node;
  }

private:
  DdNode *node;
  explicit bdd_nodet(DdNode *node) : node(node)
  {
  }
  friend class bddt;
};

/// Logical operations on BDDs
class bddt : private BDD
{
public:
  bdd_nodet node() const
  {
    return bdd_nodet(getNode());
  }

  bool equals(const bddt &other) const
  {
    return *this == other;
  }

  bool is_true() const
  {
    return IsOne();
  }

  bool is_false() const
  {
    return IsZero();
  }

  bddt bdd_not() const
  {
    return bddt(!(*this));
  }

  bddt bdd_or(const bddt &other) const
  {
    return bddt(Or(other));
  }

  bddt bdd_and(const bddt &other) const
  {
    return bddt(And(other));
  }

  bddt bdd_xor(const bddt &other) const
  {
    return bddt(Xor(other));
  }

  static bddt bdd_ite(const bddt &i, const bddt &t, const bddt &e)
  {
    return bddt(i.Ite(t, e));
  }

  bddt constrain(const bddt &other)
  {
    return bddt(Constrain(other));
  }

private:
  friend class bdd_managert;
  explicit bddt(const BDD &bdd) : BDD(bdd)
  {
  }
};

/// Manager for BDD creation
class bdd_managert : private Cudd
{
public:
  bddt bdd_true()
  {
    return bddt(bddOne());
  }

  bddt bdd_false()
  {
    return bddt(bddZero());
  }

  bddt bdd_variable(unsigned int index)
  {
    return bddt(bddVar(index));
  }
};

#endif // CPROVER_UTIL_BDD_H
