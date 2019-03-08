//
// Created by romain on 08/03/19.
//

#ifndef TEST_GEN_SUPERBUILD_NONDET_SYMBOL_EXPR_H
#define TEST_GEN_SUPERBUILD_NONDET_SYMBOL_EXPR_H
/// \brief Expression to hold a nondeterministic choice
class nondet_symbol_exprt : public nullary_exprt
{
public:
  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  nondet_symbol_exprt(const irep_idt &identifier, const typet &type)
    : nullary_exprt(ID_nondet_symbol, type)
  {
    set_identifier(identifier);
  }

  void set_identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }
};

template <>
inline bool can_cast_expr<nondet_symbol_exprt>(const exprt &base)
{
  return base.id() == ID_nondet_symbol;
}

inline void validate_expr(const nondet_symbol_exprt &value)
{
  validate_operands(value, 0, "Symbols must not have operands");
}

/// \brief Cast an exprt to a \ref nondet_symbol_exprt
///
/// \a expr must be known to be \ref nondet_symbol_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref nondet_symbol_exprt
inline const nondet_symbol_exprt &to_nondet_symbol_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_nondet_symbol);
  const nondet_symbol_exprt &ret =
    static_cast<const nondet_symbol_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_nondet_symbol_expr(const exprt &)
inline nondet_symbol_exprt &to_nondet_symbol_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_symbol);
  nondet_symbol_exprt &ret = static_cast<nondet_symbol_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif //TEST_GEN_SUPERBUILD_NONDET_SYMBOL_EXPR_H
