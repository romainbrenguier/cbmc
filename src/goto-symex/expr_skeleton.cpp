/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Expression skeleton

#include "expr_skeleton.h"

#include <util/std_expr.h>

expr_skeletont::expr_skeletont(typet missing_type)
  : skeleton(nil_exprt{}), type_of_missing_part(std::move(missing_type))
{
}

expr_skeletont expr_skeletont::remove_op0(exprt e)
{
  PRECONDITION(e.id() != ID_symbol);
  PRECONDITION(e.operands().size() >= 1);
  typet missing = std::move(e.op0().type());
  e.op0().make_nil();
  return expr_skeletont{std::move(e), std::move(missing)};
}

exprt expr_skeletont::apply(exprt expr) const
{
  PRECONDITION(skeleton.id() != ID_symbol);
  PRECONDITION(expr.type() == type_of_missing_part);
  exprt result = skeleton;
  exprt *p = &result;

  while(p->is_not_nil())
  {
    INVARIANT(
      p->id() != ID_symbol,
      "expected pointed-to expression not to be a symbol");
    INVARIANT(
      p->operands().size() >= 1,
      "expected pointed-to expression to have at least one operand");
    p = &p->op0();
  }

  INVARIANT(p->is_nil(), "expected pointed-to expression to be nil");

  *p = std::move(expr);
  return result;
}

expr_skeletont expr_skeletont::compose(expr_skeletont other) const
{
  typet missing_type = other.type_of_missing_part;
  return expr_skeletont{apply(std::move(other.skeleton)),
                        std::move(missing_type)};
}

/// In the expression corresponding to a skeleton returns a pointer to the
/// deepest subexpression before we encounter nil.
/// Returns nullptr if \p e is nil
static exprt *deepest_not_nil(exprt &e)
{
  if(e.is_nil())
    return nullptr;
  exprt *ptr = &e;
  while(!ptr->op0().is_nil())
    ptr = &ptr->op0();
  return ptr;
}

optionalt<expr_skeletont>
expr_skeletont::clear_innermost_index_expr(expr_skeletont skeleton)
{
  exprt *to_update = deepest_not_nil(skeleton.skeleton);
  if(to_update == nullptr)
    return {};
  if(index_exprt *index_expr = expr_try_dynamic_cast<index_exprt>(*to_update))
  {
    typet new_missing_type = index_expr->type();
    index_expr->make_nil();
    return expr_skeletont{std::move(skeleton.skeleton),
                          std::move(new_missing_type)};
  }
  return {};
}

optionalt<expr_skeletont>
expr_skeletont::clear_innermost_member_expr(expr_skeletont skeleton)
{
  exprt *to_update = deepest_not_nil(skeleton.skeleton);
  if(to_update == nullptr)
    return {};
  if(member_exprt *member = expr_try_dynamic_cast<member_exprt>(*to_update))
  {
    typet new_missing_type = member->type();
    member->make_nil();
    return expr_skeletont{std::move(skeleton.skeleton),
                          std::move(new_missing_type)};
  }
  return {};
}

optionalt<expr_skeletont>
expr_skeletont::clear_innermost_byte_extract_expr(expr_skeletont skeleton)
{
  exprt *to_update = deepest_not_nil(skeleton.skeleton);
  if(to_update == nullptr)
    return {};
  if(
    to_update->id() != ID_byte_extract_big_endian &&
    to_update->id() != ID_byte_extract_little_endian)
  {
    return {};
  }
  typet new_missing_type = to_update->type();
  to_update->make_nil();
  return expr_skeletont{std::move(skeleton.skeleton),
                        std::move(new_missing_type)};
}
