//
// Created by romain on 08/03/19.
//

#ifndef TEST_GEN_SUPERBUILD_SYMBOL_EXPR_H
#define TEST_GEN_SUPERBUILD_SYMBOL_EXPR_H

/// Expression to hold a symbol (variable)
class symbol_exprt : public nullary_exprt
{
public:
  DEPRECATED("use symbol_exprt(identifier, type) instead")
  symbol_exprt() : nullary_exprt(ID_symbol)
  {
  }

  /// \param identifier: Name of symbol
  DEPRECATED("use symbol_exprt(identifier, type) instead")
  explicit symbol_exprt(const irep_idt &identifier) : nullary_exprt(ID_symbol)
  {
    set_identifier(identifier);
  }

  /// \param type: Type of symbol
  explicit symbol_exprt(const typet &type) : nullary_exprt(ID_symbol, type)
  {
  }

  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  symbol_exprt(const irep_idt &identifier, const typet &type)
    : nullary_exprt(ID_symbol, type)
  {
    set_identifier(identifier);
  }

  /// Generate a symbol_exprt without a proper type. Use if, and only if, the
  /// type either cannot be determined just yet (such as during type checking)
  /// or when the type truly is immaterial. The latter case may better be dealt
  /// with by using just an irep_idt, and not a symbol_exprt.
  static symbol_exprt typeless(const irep_idt &id)
  {
    return symbol_exprt(id, typet());
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

#endif //TEST_GEN_SUPERBUILD_SYMBOL_EXPR_H
