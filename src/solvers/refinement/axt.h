/*******************************************************************\

 Module: Expression Building Utility

 Author: Diffblue Limited. All rights reserved.

\*******************************************************************/
#ifndef CPROVER_SOLVERS_REFINEMENT_AXT_H
#define CPROVER_SOLVERS_REFINEMENT_AXT_H

#include <util/expr.h>
#include <util/string_expr.h>

/// Thin wrapper for exprt class assigning different meaning to operators
/// Performing logical expression on axt will not yield usual results
/// results (with exception of assignment operator), but rather new axt
/// instances containing trees of logical expressions expressed as exprt
/// hierarchies
class axt final
{
public:
  axt(const exprt& expr) // NOLINT Use implicit conversions for best results
    :expr_(expr) { }
  axt operator>(const axt& rhs) const
  { return axt(binary_relation_exprt(expr_, ID_gt, rhs.expr_)); }
  axt operator<(const axt& rhs) const
  { return axt(binary_relation_exprt(expr_, ID_lt, rhs.expr_)); }
  axt operator>=(const axt& rhs) const
  { return axt(binary_relation_exprt(expr_, ID_ge, rhs.expr_)); }
  axt operator<=(const axt& rhs) const
  { return axt(binary_relation_exprt(expr_, ID_le, rhs.expr_)); }
  axt operator==(const axt& rhs) const
  { return axt(equal_exprt(expr_, rhs.expr_)); }
  axt operator!=(const axt& rhs) const
  { return axt(notequal_exprt(expr_, rhs.expr_)); }
  // Implication
  axt operator>>=(const axt& rhs) const
  { return axt(implies_exprt(expr_, rhs.expr_)); }
  axt operator+(const axt& rhs) const
  { return axt(plus_exprt(expr_, rhs.expr_)); }
  axt operator-(const axt& rhs) const
  { return axt(minus_exprt(expr_, rhs.expr_)); }
  axt operator&&(const axt& rhs) const
  { return axt(and_exprt(expr_, rhs.expr_)); }
  axt operator||(const axt& rhs) const
  { return axt(or_exprt(expr_, rhs.expr_)); }
  axt operator[](const axt& index) const
  { return axt(to_string_expr(expr_)[index.expr_]); }
  axt operator!()
  { return axt(not_exprt(expr_)); }
  operator exprt() const
  { return expr_; }
private:
  exprt expr_;
};

#endif // CPROVER_SOLVERS_REFINEMENT_AXT_H
