//
// Created by romain on 08/03/19.
//

#ifndef TEST_GEN_SUPERBUILD_NULLARY_EXPR_H
#define TEST_GEN_SUPERBUILD_NULLARY_EXPR_H

/// An expression without operands
class nullary_exprt : public expr_protectedt
{
public:
  // constructors
  DEPRECATED("use nullary_exprt(id, type) instead")
  explicit nullary_exprt(const irep_idt &_id) : expr_protectedt(_id, typet())
  {
  }

  nullary_exprt(const irep_idt &_id, const typet &_type)
    : expr_protectedt(_id, _type)
  {
  }

  /// remove all operand methods
  operandst &operands() = delete;
  const operandst &operands() const = delete;

  const exprt &op0() const = delete;
  exprt &op0() = delete;
  const exprt &op1() const = delete;
  exprt &op1() = delete;
  const exprt &op2() const = delete;
  exprt &op2() = delete;
  const exprt &op3() const = delete;
  exprt &op3() = delete;

  void move_to_operands(exprt &) = delete;
  void move_to_operands(exprt &, exprt &) = delete;
  void move_to_operands(exprt &, exprt &, exprt &) = delete;

  void copy_to_operands(const exprt &expr) = delete;
  void copy_to_operands(const exprt &, const exprt &) = delete;
  void copy_to_operands(const exprt &, const exprt &, const exprt &) = delete;
};

#endif //TEST_GEN_SUPERBUILD_NULLARY_EXPR_H
