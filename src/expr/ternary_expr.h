//
// Created by romain on 08/03/19.
//

#ifndef TEST_GEN_SUPERBUILD_TERNARY_EXPR_H
#define TEST_GEN_SUPERBUILD_TERNARY_EXPR_H

/// An expression with three operands
class ternary_exprt : public expr_protectedt
{
public:
  // constructors
  DEPRECATED("use ternary_exprt(id, op0, op1, op2, type) instead")
  explicit ternary_exprt(const irep_idt &_id) : expr_protectedt(_id, type())
  {
    operands().resize(3);
  }

  DEPRECATED("use ternary_exprt(id, op0, op1, op2, type) instead")
  explicit ternary_exprt(const irep_idt &_id, const typet &_type)
    : expr_protectedt(_id, _type)
  {
    operands().resize(3);
  }

  ternary_exprt(
    const irep_idt &_id,
    const exprt &_op0,
    const exprt &_op1,
    const exprt &_op2,
    const typet &_type)
    : expr_protectedt(_id, _type)
  {
    add_to_operands(_op0, _op1, _op2);
  }

  // make op0 to op2 public
  using exprt::op0;
  using exprt::op1;
  using exprt::op2;

  const exprt &op3() const = delete;
  exprt &op3() = delete;
};

#endif //TEST_GEN_SUPERBUILD_TERNARY_EXPR_H
