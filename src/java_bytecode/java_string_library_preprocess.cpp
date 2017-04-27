/*******************************************************************\

Module: Java_string_libraries_preprocess, gives code for methods on
        strings of the java standard library. In particular methods
        from java.lang.String, java.lang.StringBuilder,
        java.lang.StringBuffer.

Author: Romain Brenguier

Date:   April 2017

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/fresh_symbol.h>
#include <util/refined_string_type.h>
#include <util/string_expr.h>
#include <util/ieee_float.h>
#include "java_types.h"
#include "java_object_factory.h"


#include "java_string_library_preprocess.h"

/*******************************************************************\

Function: java_string_library_preprocesst::check_java_type

  Inputs: a type and a string

 Outputs: Boolean telling whether the type is a struct with the given
          tag or a symbolic type with the tag prefixed by "java::"

\*******************************************************************/

bool java_string_library_preprocesst::check_java_type(
  const typet &type, const std::string &tag)
{
  if(type.id()==ID_symbol)
  {
    irep_idt tag_id=to_symbol_type(type).get_identifier();
    return tag_id=="java::"+tag;
  }
  else if(type.id()==ID_struct)
  {
    irep_idt tag_id=to_struct_type(type).get_tag();
    return tag_id==tag;
  }
  return false;
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string pointers

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_string_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.String");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_builder_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string builder

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_builder_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.StringBuilder");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_builder_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java StringBuilder
          pointers

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_builder_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_string_builder_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_buffer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string buffer

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_buffer_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.StringBuffer");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_buffer_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java StringBuffer
          pointers

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_buffer_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_string_buffer_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_char_sequence_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char sequence

\*******************************************************************/

bool java_string_library_preprocesst::is_java_char_sequence_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.CharSequence");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_char_sequence_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of a pointer
          to a java char sequence

\*******************************************************************/

bool java_string_library_preprocesst::is_java_char_sequence_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_char_sequence_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_char_array_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char array

\*******************************************************************/

bool java_string_library_preprocesst::is_java_char_array_type(
  const typet &type)
{
  return check_java_type(type, "array[char]");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_char_array_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of a pointer
          to a java char array

\*******************************************************************/

bool java_string_library_preprocesst::is_java_char_array_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_char_array_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_library_preprocesst::string_data_type

  Inputs:
    symbol_table - a symbol_table containing an entry for java Strings

 Outputs: the type of data fields in java Strings.

\*******************************************************************/

typet string_data_type(symbol_tablet symbol_table)
{
  symbolt sym=symbol_table.lookup("java::java.lang.String");
  typet concrete_type=sym.type;
  // TODO: we should look at the name of the field
  typet data_type=to_struct_type(concrete_type).components()[2].type();
  return data_type;
}

/*******************************************************************\

Function: java_string_library_preprocesst::string_length_type

  Inputs:
    symbol_table - a symbol_table containing an entry for java Strings

 Outputs: the type of lenngth fields in java Strings.

\*******************************************************************/

typet string_length_type(symbol_tablet symbol_table)
{
  symbolt sym=symbol_table.lookup("java::java.lang.String");
  typet concrete_type=sym.type;
  // TODO: we should look at the name of the field
  typet length_type=to_struct_type(concrete_type).components()[1].type();
  return length_type;
}

/*******************************************************************\

Function: java_string_library_preprocesst::add_string_type

  Inputs: a name for the class such as "java.lang.String"

 Purpose: Implements the java.lang.String type in the case that
          we provide an internal implementation.

\*******************************************************************/

void java_string_library_preprocesst::add_string_type(
  const irep_idt &class_name, symbol_tablet &symbol_table)
{
  class_typet string_type;
  string_type.set_tag(class_name);
  string_type.components().resize(3);
  string_type.components()[0].set_name("@java.lang.Object");
  string_type.components()[0].set_pretty_name("@java.lang.Object");
  string_type.components()[0].type()=symbol_typet("java::java.lang.Object");
  string_type.components()[1].set_name("length");
  string_type.components()[1].set_pretty_name("length");
  string_type.components()[1].type()=java_int_type();
  string_type.components()[2].set_name("data");
  string_type.components()[2].set_pretty_name("data");
  // Use a pointer-to-unbounded-array instead of a pointer-to-char.
  // Saves some casting in the string refinement algorithm but may
  // be unnecessary.
  string_type.components()[2].type()=pointer_typet(
    array_typet(java_char_type(), infinity_exprt(java_int_type())));
  string_type.add_base(symbol_typet("java::java.lang.Object"));

  symbolt string_symbol;
  string_symbol.name="java::"+id2string(class_name);
  string_symbol.base_name=id2string(class_name);
  string_symbol.type=string_type;
  string_symbol.is_type=true;

  symbol_table.add(string_symbol);

  // Also add a stub of `String.equals` so that remove-virtual-functions
  // generates a check for Object.equals vs. String.equals.
  // No need to fill it in, as pass_preprocess will replace the calls again.
  symbolt string_equals_symbol;
  string_equals_symbol.name=
    "java::java.lang.String.equals:(Ljava/lang/Object;)Z";
  string_equals_symbol.base_name=id2string(class_name)+".equals";
  string_equals_symbol.pretty_name=id2string(class_name)+".equals";
  string_equals_symbol.mode=ID_java;

  code_typet string_equals_type;
  string_equals_type.return_type()=java_boolean_type();
  code_typet::parametert thisparam;
  thisparam.set_this();
  thisparam.type()=pointer_typet(symbol_typet(string_symbol.name));
  code_typet::parametert otherparam;
  otherparam.type()=pointer_typet(symbol_typet("java::java.lang.Object"));
  string_equals_type.parameters().push_back(thisparam);
  string_equals_type.parameters().push_back(otherparam);
  string_equals_symbol.type=std::move(string_equals_type);

  symbol_table.add(string_equals_symbol);
}

/*******************************************************************\

Function: fresh_array

  Inputs:
    type - an array type
    location - a location in the program

 Outputs: a new symbol

 Purpose: add a symbol in the table with static lifetime and name
          containing `cprover_string_array` and given type

\*******************************************************************/

symbol_exprt java_string_library_preprocesst::fresh_array(
  const typet &type,
  const source_locationt &location,
  symbol_tablet &symbol_table)
{
  symbolt array_symbol=get_fresh_aux_symbol(
    type,
    "java::cprover_string_array",
    "java::cprover_string_array",
    location,
    ID_java,
    symbol_table);
  array_symbol.is_static_lifetime=true;
  return array_symbol.symbol_expr();
}

/*******************************************************************\

Function: java_string_library_preprocesst::declare_function

  Inputs: a name and a type

 Purpose: declare a function with the given name and type

 TODO: duplicates goto_programs/string_refine_preprocess function

\*******************************************************************/

void java_string_library_preprocesst::declare_function(
  irep_idt function_name, const typet &type, symbol_tablet &symbol_table)
{
  auxiliary_symbolt func_symbol;
  func_symbol.base_name=function_name;
  func_symbol.is_static_lifetime=false;
  func_symbol.mode=ID_java;
  func_symbol.name=function_name;
  func_symbol.type=type;
  symbol_table.add(func_symbol);
}

/*******************************************************************\

Function: string_refine_preprocesst::process_arguments

  Inputs:
    params - a list of function parameters
    symbol_table - symbol table
    init_code - code block, in which declaration of some arguments
                may be added

 Outputs: a list of expressions

 Purpose: calls string_refine_preprocesst::process_operands with a
          list of parameters.

\*******************************************************************/

exprt::operandst java_string_library_preprocesst::process_parameters(
  const code_typet::parameterst &params,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  exprt::operandst ops;
  for(const auto &p : params)
  {
    symbol_exprt sym(p.get_identifier(), p.type());
    ops.push_back(sym);
  }
  return process_operands(ops, loc, symbol_table, init_code);
}

/*******************************************************************\

Function: java_string_library_preprocesst::process_operands

  Inputs:
    operands - a list of expressions
    loc - location in the source
    symbol_table - symbol table
    init_code - code block, in which declaration of some arguments
                may be added

 Outputs: a list of expressions

 Purpose: for each expression that is of a type implementing strings,
          we declare a new `cprover_string` whose contents is deduced
          from the expression and replace the
          expression by this cprover_string in the output list;
          in the other case the expression is kept as is for the output list.
          Also does the same thing for char array references.

\*******************************************************************/

exprt::operandst java_string_library_preprocesst::process_operands(
  const exprt::operandst &operands,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  exprt::operandst ops;
  for(const auto &p : operands)
  {
    if(implements_java_char_sequence(p.type()))
    {
      refined_string_typet ref_type(
        string_length_type(symbol_table),
        string_data_type(symbol_table).subtype().subtype());
      dereference_exprt deref(p, to_pointer_type(p.type()).subtype());
      member_exprt length(deref, "length", string_length_type(symbol_table));
      member_exprt data(deref, "data", string_data_type(symbol_table));
      dereference_exprt deref_data(data, data.type().subtype());
      string_exprt string_expr=fresh_string_expr(loc, symbol_table);
      exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table);
      init_code.copy_to_operands(code_declt(string_expr.length()));
      init_code.copy_to_operands(code_declt(string_expr.content()));
      init_code.copy_to_operands(code_declt(string_expr_sym));
      init_code.copy_to_operands(code_assignt(string_expr.length(), length));
      init_code.copy_to_operands(
        code_assignt(string_expr.content(), deref_data));
      init_code.copy_to_operands(code_assignt(string_expr_sym, string_expr));
      ops.push_back(string_expr);
    }
    else if(is_java_char_array_pointer_type(p.type()))
    {
      ops.push_back(process_char_array(p, loc, symbol_table, init_code));
    }
    else
    {
      ops.push_back(p);
    }
  }
  return ops;
}

/*******************************************************************\

Function: java_string_library_preprocesst::refined_string_type

  Inputs: a type containing a "data" component

  Outputs: type of the "data" component

 Purpose: Finds the type of the data component

\*******************************************************************/

refined_string_typet java_string_library_preprocesst::refined_string_type()
{
  return refined_string_typet(java_int_type(), java_char_type());
}

/*******************************************************************\

Function: java_string_library_preprocesst::get_data_type

  Inputs: a type containing a "data" component

  Outputs: type of the "data" component

 Purpose: Finds the type of the data component

\*******************************************************************/

typet java_string_library_preprocesst::get_data_type(
  const typet &type, const symbol_tablet &symbol_table)
{
  if(type.id()==ID_symbol)
  {
    symbolt sym=symbol_table.lookup(to_symbol_type(type).get_identifier());
    assert(sym.type.id()!=ID_symbol);
    return get_data_type(sym.type, symbol_table);
  }
  else
  {
    assert(type.id()==ID_struct);
    const struct_typet &struct_type=to_struct_type(type);
    for(auto component : struct_type.components())
      if(component.get_name()=="data")
        return component.type();
    assert(false && "type does not contain data component");
  }
}

/*******************************************************************\

Function: java_string_library_preprocesst::get_length_type

  Inputs: a type containing a "length" component

  Outputs: type of the "length" component

 Purpose: Finds the type of the length component

\*******************************************************************/

typet java_string_library_preprocesst::get_length_type(
  const typet &type, const symbol_tablet &symbol_table)
{
  if(type.id()==ID_symbol)
  {
    symbolt sym=symbol_table.lookup(to_symbol_type(type).get_identifier());
    assert(sym.type.id()!=ID_symbol);
    return get_data_type(sym.type, symbol_table);
  }
  else
  {
    assert(type.id()==ID_struct);
    const struct_typet &struct_type=to_struct_type(type);
    for(auto component : struct_type.components())
      if(component.get_name()=="length")
        return component.type();
    assert(false && "type does not contain length component");
  }
}

/*******************************************************************\

Function: java_string_library_preprocesst::get_length

  Inputs: an expression of structured type with length component

  Outputs: expression representing the "length" member

 Purpose: access length member

\*******************************************************************/

exprt java_string_library_preprocesst::get_length(
  const exprt &expr, const symbol_tablet &symbol_table)
{
  return member_exprt(
    expr, "length", get_length_type(expr.type(), symbol_table));
}

/*******************************************************************\

Function: java_string_library_preprocesst::get_data

  Inputs: an expression of structured type with length component

  Outputs: expression representing the "data" member

 Purpose: access data member

\*******************************************************************/

exprt java_string_library_preprocesst::get_data(
  const exprt &expr, const symbol_tablet &symbol_table)
{
  return member_exprt(expr, "data", get_data_type(expr.type(), symbol_table));
}

/*******************************************************************\

Function: string_refine_preprocesst::process_char_array

  Inputs:
    array_pointer - an expression of type char array pointer
    loc - location in the source
    symbol_table - symbol table
    init_code - code block, in which some assignements will be added

 Outputs: a string expression

 Purpose: we declare a new `cprover_string` whose contents is deduced
          from the char array.

\*******************************************************************/

string_exprt java_string_library_preprocesst::process_char_array(
  const exprt &array_pointer,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &code)
{
  // TODO : this is used often and we should have a static function for that
  refined_string_typet ref_type(java_int_type(), java_char_type());
  string_exprt string_expr=fresh_string_expr(loc, symbol_table);

  // deref=*(rhs->data)
  dereference_exprt array(array_pointer, array_pointer.type().subtype());
  typet data_type=get_data_type(array.type(), symbol_table);
  member_exprt array_data(array, "data", data_type);
  dereference_exprt deref_array(array_data, data_type.subtype());
  symbolt sym_lhs_deref=get_fresh_aux_symbol(
    data_type.subtype(),
    "char_array_assign$deref",
    "char_array_assign$deref",
    loc,
    ID_java,
    symbol_table);
  symbol_exprt lhs_deref=sym_lhs_deref.symbol_expr();
  code.copy_to_operands(code_assignt(lhs_deref, deref_array));

  // array=convert_pointer_to_char_array(*rhs->data)
  code.copy_to_operands(code_assign_function_application(
    array,
    ID_cprover_string_array_of_char_pointer_func,
    {deref_array},
    symbol_table));

  // string={ rhs->length; string_array }
  string_exprt new_rhs(get_length(array, symbol_table), array, ref_type);
  symbol_exprt lhs=fresh_string(ref_type, loc, symbol_table);
  code.copy_to_operands(code_assignt(lhs, new_rhs));

  return new_rhs;
}

/*******************************************************************\

Function: java_string_library_preprocesst::fresh_string

  Inputs:
    type - a type for refined strings
    location - a location in the program

 Outputs: a new symbol

 Purpose: add a symbol with static lifetime and name containing
          `cprover_string` and given type

\*******************************************************************/

symbol_exprt java_string_library_preprocesst::fresh_string(
  const typet &type, const source_locationt &loc, symbol_tablet &symbol_table)
{
  symbolt string_symbol=get_fresh_aux_symbol(
    type, "java::cprover_string", "cprover_string", loc, ID_java, symbol_table);
  string_symbol.is_static_lifetime=true;
  return string_symbol.symbol_expr();
}

/*******************************************************************\

Function: java_string_library_preprocesst::fresh_string_expr

  Inputs:
    type - a type for refined strings
    location - a location in the program

 Outputs: a new string_expr

 Purpose: add symbols with prefixe cprover_string_length and
          cprover_string_data and construct a string_expr from them.

\*******************************************************************/

string_exprt java_string_library_preprocesst::fresh_string_expr(
  const source_locationt &loc, symbol_tablet &symbol_table)
{
  refined_string_typet type=refined_string_type();
  symbolt sym_length=get_fresh_aux_symbol(
    type.get_index_type(),
    "java::cprover_string_length",
    "cprover_string_length",
    loc,
    ID_java,
    symbol_table);
  symbol_exprt length_field=sym_length.symbol_expr();
  symbol_exprt content_field=fresh_array(
    type.get_content_type(), loc, symbol_table);
  string_exprt str(length_field, content_field, type);
  return str;
}

/*******************************************************************\

Function: java_string_library_preprocesst::fresh_string_expr_symbol

  Inputs:
    type - a type for refined strings
    location - a location in the program

 Outputs: a new expression of refined string type

 Purpose: add symbols with prefixe cprover_string_length and
          cprover_string_data and construct a string_expr from them.

\*******************************************************************/

exprt java_string_library_preprocesst::fresh_string_expr_symbol(
  const source_locationt &loc, symbol_tablet &symbol_table)
{
  symbolt sym=get_fresh_aux_symbol(
    refined_string_type(),
    "java::cprover_string",
    "cprover_string",
    loc,
    ID_java,
    symbol_table);
  return sym.symbol_expr();
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_function_application

  Inputs:
    function_name - the name of the function
    arguments - a list of arguments
    type - return type of the function
    symbol_table - a symbol table

  Output: a function application representing: function_name(arguments)

\*******************************************************************/

exprt java_string_library_preprocesst::make_function_application(
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const typet &type,
  symbol_tablet &symbol_table)
{
  // Names of function to call
  std::string fun_name="java::"+id2string(function_name);

  // Declaring the function
  declare_function(fun_name, type, symbol_table);

  // Function application
  function_application_exprt call(symbol_exprt(fun_name), type);
  call.arguments()=arguments;
  return call;
}

/*******************************************************************\

Function: java_string_library_preprocesst::code_assign_function_application

  Inputs:
    lhs - an expression
    function_name - the name of the function
    arguments - a list of arguments
    symbol_table - a symbol table

  Output: the following code:
          > lhs=function_name_length(arguments)

  Purpose: assign the result of a function call

\*******************************************************************/

codet java_string_library_preprocesst::code_assign_function_application(
  const exprt &lhs,
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  symbol_tablet &symbol_table)
{
  exprt fun_app=make_function_application(
    function_name, arguments, lhs.type(), symbol_table);
  return code_assignt(lhs, fun_app);
}

/*******************************************************************\

Function: java_string_library_preprocesst::code_return_function_application

  Inputs:
    function_name - the name of the function
    arguments - a list of arguments
    type - the return type
    symbol_table - a symbol table

  Output: the following code:
          > return function_name_length(arguments)

  Purpose: return the result of a function call

\*******************************************************************/

codet java_string_library_preprocesst::code_return_function_application(
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const typet &type,
  symbol_tablet &symbol_table)
{
  exprt fun_app=make_function_application(
    function_name, arguments, type, symbol_table);
  return code_returnt(fun_app);
}

/*******************************************************************\

Function: java_string_library_preprocesst::code_assign_function_to_string_expr

  Inputs:
    str - a string expression
    function_type - a function type
    function_name - the name of the function

  Output: return the following code:
          > str.length=function_name_length(arguments)
          > str.data=function_name_data(arguments)

\*******************************************************************/

codet java_string_library_preprocesst::code_assign_function_to_string_expr(
  const string_exprt &string_expr,
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  symbol_tablet &symbol_table)
{
  // Getting types
  typet length_type=string_length_type(symbol_table);
  typet data_type=string_data_type(symbol_table);
  refined_string_typet ref_type(length_type, data_type.subtype());

  // Names of function to call
  std::string fun_name_length="java::"+id2string(function_name)+"_length";
  std::string fun_name_data="java::"+id2string(function_name)+"_data";

  // Assignments
  codet assign_fun_length=code_assign_function_application(
        string_expr.length(), fun_name_length, arguments, symbol_table);
  codet assign_fun_data=code_assign_function_application(
        string_expr.content(), fun_name_data, arguments, symbol_table);

  return code_blockt({ assign_fun_length, assign_fun_data});
}

/*******************************************************************\

Function: java_string_library_preprocesst::
            code_assign_string_expr_to_java_string

  Inputs:
    lhs - an expression representing a java string
    rhs - a string expression
    location - a location in the program

  Output: return the following code:
          > lhs->length=rhs.length
          > lhs->data=&rhs.data

\*******************************************************************/

codet java_string_library_preprocesst::code_assign_string_expr_to_java_string(
  const exprt &lhs,
  const string_exprt &rhs,
  symbol_tablet &symbol_table)
{
  assert(implements_java_char_sequence(lhs.type()));
  dereference_exprt deref(lhs, lhs.type().subtype());

  // Getting types
  // TODO: should get types from lhs.type()
  typet length_type=string_length_type(symbol_table);
  typet data_type=string_data_type(symbol_table);

  // Fields of the string object
  member_exprt lhs_length(deref, "length", length_type);
  member_exprt lhs_data(deref, "data", data_type);

  // Assignments
  std::list<codet> assigns;
  assigns.push_back(code_assignt(lhs_length,rhs.length()));
  assigns.push_back(code_assignt(lhs_data, address_of_exprt(rhs.content())));
  return code_blockt(assigns);
}

/*******************************************************************\

Function: java_string_library_preprocesst::
            code_assign_java_string_to_string_expr

  Inputs:
    lhs - a string expression
    rhs - an expression representing a java string
    location - a location in the program

  Output: return the following code:
          > lhs.length=rhs->length
          > lhs.data=*(rhs->data)

\*******************************************************************/

codet java_string_library_preprocesst::code_assign_java_string_to_string_expr(
  const string_exprt &lhs, const exprt &rhs, symbol_tablet &symbol_table)
{
  assert(implements_java_char_sequence(rhs.type()));

  typet deref_type;
  if(rhs.type().subtype().id()==ID_symbol)
    deref_type=symbol_table.lookup(
      to_symbol_type(rhs.type().subtype()).get_identifier()).type;
  else
    deref_type=rhs.type().subtype();

  dereference_exprt deref(rhs, deref_type);

  // Getting types
  // TODO: should get types from rhs.type()
  typet length_type=string_length_type(symbol_table);
  typet data_type=string_data_type(symbol_table);

  // Fields of the string object
  member_exprt rhs_length(deref, "length", length_type);
  member_exprt member_data(deref, "data", data_type);
  dereference_exprt rhs_data(member_data, member_data.type().subtype());

  // Assignments
  std::list<codet> assigns;
  assigns.push_back(code_assignt(lhs.length(), rhs_length));
  assigns.push_back(code_assignt(lhs.content(), rhs_data));
  return code_blockt(assigns);
}

/*******************************************************************\

Function: java_string_library_preprocesst::
            code_assign_string_literal_to_string_expr

  Inputs:
    lhs - an expression representing a java string
    tmp_string - a temporary string to hold the literal
    s - the literal to be assigned
    location - a location in the program

  Output: return the following code:
          > tmp_string = "s"
          > lhs = (string_expr) tmp_string

\*******************************************************************/

codet java_string_library_preprocesst::
  code_assign_string_literal_to_string_expr(
    const string_exprt &lhs,
    const exprt &tmp_string,
    const std::string &s,
    symbol_tablet &symbol_table)
{
  code_blockt code;
  code.copy_to_operands(code_assignt(tmp_string, string_literal(s)));
  code.copy_to_operands(code_assign_java_string_to_string_expr(
    lhs, tmp_string, symbol_table));
  return code;

}

/*******************************************************************\

Function: java_string_library_preprocesst::
    make_string_builder_append_object_code

  Inputs:
    type - type of the function called

 Outputs: code for the StringBuilder.append(Object) function:
          > string1 = arguments[1].toString()
          > string_expr1 = string_to_string_expr(string1)
          > string_expr2 = concat(this, string_expr1)
          > this = string_expr_to_string(string_expr2)
          > return this

\*******************************************************************/

codet java_string_library_preprocesst::make_string_builder_append_object_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  code_typet::parameterst params=type.parameters();
  exprt this_obj=symbol_exprt(params[0].get_identifier(), params[0].type());

  // String expression that will hold the result
  string_exprt string_expr1=fresh_string_expr(loc, symbol_table);
  string_exprt string_expr2=fresh_string_expr(loc, symbol_table);

  // Code to be returned
  code_blockt code;

  exprt::operandst arguments=process_parameters(
    type.parameters(), loc, symbol_table, code);
  assert(arguments.size()==2);

  // > string1 = arguments[1].toString()
  exprt string1=fresh_string(this_obj.type(), loc, symbol_table);
  code_function_callt fun_call;
  fun_call.lhs()=string1;
  // TODO: we should look in the symbol table for such a symbol
  fun_call.function()=symbol_exprt(
    "java::java.lang.Object.toString:()Ljava/lang/String;");
  fun_call.arguments().push_back(arguments[1]);
  code_typet fun_type;
  fun_type.return_type()=string1.type();
  fun_call.function().type()=fun_type;
  code.copy_to_operands(fun_call);

  // > string_expr1 = string_to_string_expr(string1)
  code.copy_to_operands(code_assign_java_string_to_string_expr(
    string_expr1, string1, symbol_table));

  // > string_expr2 = concat(this, string1)
  exprt::operandst concat_arguments(arguments);
  concat_arguments[1]=string_expr1;
  code.copy_to_operands(code_assign_function_to_string_expr(
    string_expr2,
    ID_cprover_string_concat_func,
    concat_arguments,
    symbol_table));

  // > this = string_expr
  code.copy_to_operands(code_assign_string_expr_to_java_string(
    this_obj, string_expr2, symbol_table));

  // > return this
  code.copy_to_operands(code_returnt(this_obj));

  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::
    make_string_builder_append_float_code

  Inputs:
    code - the code of a function call

 Outputs: code for the StringBuilder.append(F) function:
          > string1 = arguments[1].toString()
          > string_expr1 = string_to_string_expr(string1)
          > string_expr2 = concat(this, string_expr1)
          > this = string_expr_to_string(string_expr2)
          > return this

\*******************************************************************/

codet java_string_library_preprocesst::make_string_builder_append_float_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  code_typet::parameterst params=type.parameters();
  exprt this_obj=symbol_exprt(params[0].get_identifier(), params[0].type());

  // Getting types
  typet length_type=string_length_type(symbol_table);
  typet data_type=string_data_type(symbol_table);

  // String expression that will hold the result
  refined_string_typet ref_type(length_type, java_char_type());
  string_exprt string_expr1=fresh_string_expr(loc, symbol_table);
  string_exprt string_expr2=fresh_string_expr(loc, symbol_table);

  // Code to be returned
  code_blockt code;

  exprt::operandst arguments=process_parameters(
    type.parameters(), loc, symbol_table, code);
  assert(arguments.size()==2);

  // > string1 = arguments[1].toString()
  exprt string1=fresh_string(this_obj.type(), loc, symbol_table);
  code_function_callt fun_call;
  fun_call.lhs()=string1;
  // TODO: we should look in the symbol table for such a symbol
  fun_call.function()=symbol_exprt(
    "java::java.lang.Float.toString:()Ljava/lang/String;");
  fun_call.arguments().push_back(arguments[1]);
  code_typet fun_type;
  fun_type.return_type()=string1.type();
  fun_call.function().type()=fun_type;
  code.copy_to_operands(fun_call);

  // > string_expr1 = string_to_string_expr(string1)
  code.copy_to_operands(code_assign_java_string_to_string_expr(
    string_expr1, string1, symbol_table));

  // > string_expr2 = concat(this, string1)
  exprt::operandst concat_arguments(arguments);
  concat_arguments[1]=string_expr1;
  code.copy_to_operands(code_assign_function_to_string_expr(
    string_expr2,
    ID_cprover_string_concat_func,
    concat_arguments,
    symbol_table));

  // > this = string_expr
  code.copy_to_operands(code_assign_string_expr_to_java_string(
    this_obj, string_expr2, symbol_table));

  // > return this
  code.copy_to_operands(code_returnt(this_obj));

  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::string_literal

  Inputs:
    s - a string

 Outputs: an expression representing a Java string literal with the
          given content.

 Purpose: construct a Java string literal from a constant string value

\*******************************************************************/

exprt java_string_library_preprocesst::string_literal(const std::string &s)
{
  exprt string_literal(ID_java_string_literal);
  string_literal.set(ID_value, s);
  return string_literal;
}

/*******************************************************************\

Function: get_exponent

  Inputs:
    src - a floating point expression
    spec - specification for floating points

 Outputs:
    a java integer representing the exponent

 Purpose: Gets the unbiased exponent in a floating-point bit-vector

\*******************************************************************/

exprt get_exponent(
  const exprt &src,
  const ieee_float_spect &spec)
{
  exprt exp_bits=extractbits_exprt(
    src, spec.f+spec.e-1, spec.f,
    unsignedbv_typet(spec.e));
  // exponent is in biased from (numbers form -128 to 127 are encoded with
  // integer from 0 to 255) we have to remove the bias.
  return minus_exprt(typecast_exprt(exp_bits, java_int_type()),
                     from_integer(spec.bias(), java_int_type()));
}

/*******************************************************************\

Function: get_magnitude

  Inputs:
    src - a floating point expression
    spec - specification for floating points

 Outputs:

 Purpose: Gets the magnitude without hidden bit

\*******************************************************************/

exprt get_magnitude(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return extractbits_exprt(
    src, spec.f-1, 0,
    unsignedbv_typet(spec.f));
}

/*******************************************************************\

Function: get_significand

  Inputs:
    src - a floating point expression
    spec - specification for floating points

 Outputs:

 Purpose: Gets the significand as a java integer, looking for the hidden bit

\*******************************************************************/

exprt get_significand(
  const exprt &src,
  const ieee_float_spect &spec)
{
  typecast_exprt magnitude(get_magnitude(src, spec), java_int_type());
  exprt exponent=get_exponent(src, spec);
  equal_exprt all_zeros(exponent, from_integer(0, exponent.type()));
  plus_exprt with_hidden_bit(
    magnitude, from_integer(0x800000, java_int_type()));
  return if_exprt(all_zeros, magnitude, with_hidden_bit);
}

/*******************************************************************\

Function:  single_precision_float

\*******************************************************************/

exprt single_precision_float(float f)
{
  ieee_float_spect float_spec=ieee_float_spect::single_precision();
  // Subcase of 0.0
  ieee_floatt fl(float_spec);
  fl.from_float(f);
  return fl.to_expr();
}

/*******************************************************************\

Function:  estimate_decimal_exponent

Purpose:
         We are looking for d such that n * 10^d = m * 10^e, so:
         d = log_10(m) + log_10(2) * e - log_10(n)
         m - the magnitude - should be between 1 and 2 so log_10(m)
         in [0,log_10(2)]
         n - the magnitude in base 10 - should be between 1 and 10 so
         log_10(n) in [0, 1]
         So the estimate is given by:
         d ~=~  floor( log10(2) * e)

\*******************************************************************/

exprt log_10_of_2=single_precision_float(0.301029995663981);

exprt estimate_decimal_exponent(const exprt &f,  const ieee_float_spect &spec)
{
  exprt bin_exp=get_exponent(f, spec);
  mult_exprt dec_exponent(
    typecast_exprt(bin_exp, java_float_type()), log_10_of_2);
  return typecast_exprt(dec_exponent, java_int_type());
}


/*******************************************************************\

Function:  estimate_decimal_magnitude

Purpose:


\*******************************************************************/


exprt estimate_decimal_magnitude(const exprt &f,  const ieee_float_spect &spec)
{
  exprt bin_frac=get_magnitude(f, spec);
  return typecast_exprt(bin_frac, java_int_type());
}

/*******************************************************************\

Function:  get_first_character_from_log_representation

Purpose: Given logarithm 10 of n, finds out what should be the first
         character in the representation of n.
         For instance if n=8, its logarithm is 0.90309, so given 0.90309
         the function should return '8'

\*******************************************************************/

double log_table[]={0.0000000, 0.3010300, 0.4771213, 0.6020600, 0.6989700,
                    0.7781513, 0.8450980, 0.9030900, 0.9542425, 0.1000000};

exprt get_first_character_from_log_representation(const exprt &log)
{
  exprt ret=from_integer('0', java_char_type());
  for(std::size_t i=9; i>0; --i)
    ret=if_exprt(
      binary_relation_exprt(log, ID_le, single_precision_float(log_table[i])),
      from_integer('0'+i, java_char_type()),
      ret);
  return ret;
}

// Table for values of 2^e / 10^(floor(log_10(2) * e)) for e from 0 to 128
std::vector<double> two_power_e_over_ten_power_d_table(
{1, 2, 4, 8, 1.6, 3.2, 6.4, 1.28, 2.56,
 5.12, 1.024, 2.048, 4.096, 8.192, 1.6384, 3.2768, 6.5536,
 1.31072, 2.62144, 5.24288, 1.04858, 2.09715, 4.19430, 8.38861, 1.67772,
 3.35544, 6.71089, 1.34218, 2.68435, 5.36871, 1.07374, 2.14748, 4.29497,
 8.58993, 1.71799, 3.43597, 6.87195, 1.37439, 2.74878, 5.49756, 1.09951,
 2.19902, 4.39805, 8.79609, 1.75922, 3.51844, 7.03687, 1.40737, 2.81475,
 5.62950, 1.12590, 2.25180, 4.50360, 9.00720, 1.80144, 3.60288, 7.20576,
 1.44115, 2.88230, 5.76461, 1.15292, 2.30584, 4.61169, 9.22337, 1.84467,
 3.68935, 7.37870, 1.47574, 2.95148, 5.90296, 1.18059, 2.36118, 4.72237,
 9.44473, 1.88895, 3.77789, 7.55579, 1.51116, 3.02231, 6.04463, 1.20893,
 2.41785, 4.83570, 9.67141, 1.93428, 3.86856, 7.73713, 1.54743, 3.09485,
 6.18970, 1.23794, 2.47588, 4.95176, 9.90352, 1.98070, 3.96141, 7.92282,
 1.58456, 3.16913, 6.33825, 1.26765, 2.53530, 5.07060, 1.01412, 2.02824,
 4.05648, 8.11296, 1.62259, 3.24519, 6.49037, 1.29807, 2.59615, 5.1923,
 1.03846, 2.07692, 4.15384, 8.30767, 1.66153, 3.32307, 6.64614, 1.32923,
 2.65846, 5.31691, 1.06338, 2.12676, 4.25353, 8.50706, 1.70141});


/*******************************************************************\

Function: java_string_library_preprocesst::code_for_scientific_notation

Purpose:
         A float is represented as $f=m*2^e$ where
         $0 <= m < 2$ is the significand and $-126 <= e <= 127$ is the exponent
         We want an alternate representation by finding n and d
         such that $f=n*10^d$. We can estimate d using the following:
         $d ~= log_10(f/n) ~= log_10(m) + log_10(2) * e - log_10(n)$
         Then $n$ can be expressed by the equation:
         $log_10(n) = log_10(m) + log_10(2) * e - d$
         log_10(m) can be 0 or -1

\*******************************************************************/

codet java_string_library_preprocesst::code_for_scientific_notation(
  const exprt &arg,
  const ieee_float_spect &float_spec,
  const string_exprt &string_expr,
  const exprt &tmp_string,
  const refined_string_typet &refined_string_type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  code_blockt code;

  // `binary_exponent` is $e$ in the formulas
  exprt binary_exponent=get_exponent(arg, float_spec);

  // `binary_significand` is `m` in the formulas
  exprt binary_significand=get_significand(arg, float_spec);

  // `decimal_exponent` is $d$ in the formulas
  exprt decimal_exponent=estimate_decimal_exponent(arg, float_spec);

  // bias_factor is $2^e/10^d$
  array_exprt bias_table(
    array_typet(java_float_type(), from_integer(128, java_int_type())));
  for(const auto &f:two_power_e_over_ten_power_d_table)
    bias_table.copy_to_operands(single_precision_float(f));
  index_exprt bias_factor(bias_table, binary_exponent, java_float_type());

  // `dec_significand` is $n = m * bias_factor$
  mult_exprt dec_significand(
    typecast_exprt(binary_significand, java_float_type()), bias_factor);

  // we divide this number by 0x80000 because it represents a fraction
  // and multiply by 1000000 to get more digits
  mult_exprt dec_significand_with_8_digits(
    dec_significand, single_precision_float(1.192092896));
  typecast_exprt dec_significand_int(
    dec_significand_with_8_digits,
    java_int_type());

  // The first character is given by dec_significand_int / 1000000
  div_exprt dec_significand_integer_part(
    dec_significand_int, from_integer(1000000, java_int_type()));
  string_exprt string_first_character=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_first_character,
      ID_cprover_string_of_int_func,
      {dec_significand_integer_part},
      symbol_table));

  // string_lit_dot = "."
  string_exprt string_lit_dot=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_string_literal_to_string_expr(
      string_lit_dot, tmp_string, ".", symbol_table));

  // string_expr_with_dot = concat(string_magnitude, string_lit_dot)
  string_exprt string_expr_with_dot=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr_with_dot,
      ID_cprover_string_concat_func,
      {string_first_character, string_lit_dot},
      symbol_table));

  // string_fractional_part
  minus_exprt dec_significand_fractional_part(
    dec_significand_int,
    mult_exprt(dec_significand_integer_part,
               from_integer(1000000, java_int_type())));

  string_exprt string_fractional_part=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_fractional_part,
      ID_cprover_string_of_int_func,
      {typecast_exprt(dec_significand_fractional_part, java_int_type())},
      symbol_table));

  // string_expr_with_fractional_part =
  //   concat(string_with_do, string_fractional_part)
  string_exprt string_expr_with_fractional_part=fresh_string_expr(
    loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr_with_fractional_part,
      ID_cprover_string_concat_func,
      {string_expr_with_dot, string_fractional_part},
      symbol_table));

  // string_lit_E = "E"
  string_exprt string_lit_E=fresh_string_expr(loc, symbol_table);

  code.copy_to_operands(
    code_assign_string_literal_to_string_expr(
      string_lit_E, tmp_string, "E", symbol_table));

  // string_expr_with_E = concat(string_magnitude, string_lit_E)
  string_exprt string_expr_with_E=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr_with_E,
      ID_cprover_string_concat_func,
      {string_expr_with_fractional_part, string_lit_E},
      symbol_table));

  // exponent_string = string_of_int(decimal_exponent)
  string_exprt exponent_string=fresh_string_expr(loc, symbol_table);

  code.copy_to_operands(
    code_assign_function_to_string_expr(
      exponent_string,
      ID_cprover_string_of_int_func,
      {decimal_exponent},
      symbol_table));

  // string_expr = concat(string_expr_withE, exponent_string)
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr,
      ID_cprover_string_concat_func,
      {string_expr_with_E, exponent_string},
      symbol_table));

  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_float_to_string_code

  Inputs:
    code - the code of a function call

 Outputs: code for the Float.toString(F) function:
          > String * str;
          > str = MALLOC(String);
          > String * tmp_string;
          > int string_expr_length;
          > char[] string_expr_content;
          > CPROVER_string string_expr_sym;
          > if arguments[1]==NaN
          > then {tmp_string="NaN"; string_expr=(string_expr)tmp_string}
          > if arguments[1]==Infinity
          > then {tmp_string="Infinity"; string_expr=(string_expr)tmp_string}
          > if 1e-3<arguments[1]<1e6
          > then {tmp_string=string_of_int((int)arguments[1]);
          >       string_expr=(string_expr)tmp_string}
          > string_expr_sym=string_expr;
          > str=(String*) string_expr;
          > return str;

\*******************************************************************/

codet java_string_library_preprocesst::make_float_to_string_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  // Getting the argument
  code_typet::parameterst params=type.parameters();
  assert(params.size()==1 && "wrong number of parameters in Float.toString");
  exprt arg=symbol_exprt(params[0].get_identifier(), params[0].type());

  // Holder for output code
  code_blockt code;

  // Declaring and allocating String * str
  exprt str=fresh_string(type.return_type(), loc, symbol_table);
  code.copy_to_operands(code_declt(str));
  exprt malloc=allocate_dynamic_object(
    str, str.type().subtype(), symbol_table, loc, code, false);
  exprt tmp_string=fresh_string(type.return_type(), loc, symbol_table);

  // Declaring CPROVER_string string_expr
  refined_string_typet ref_type(java_int_type(), java_char_type());
  string_exprt string_expr=fresh_string_expr(loc, symbol_table);
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table);

  // List of the different cases
  std::vector<code_ifthenelset> case_list;

  // First case in the list is the default
  code_ifthenelset case_sci_notation;
  ieee_float_spect float_spec=ieee_float_spect::single_precision();
  // Subcase of 0.0
  ieee_floatt zero_float(float_spec);
  zero_float.from_float(0.0);
  constant_exprt zero=zero_float.to_expr();
  case_sci_notation.cond()=ieee_float_equal_exprt(arg, zero);
  case_sci_notation.then_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "0.0", symbol_table);

  // Subcase of computerized scientific notation
  case_sci_notation.else_case()=code_for_scientific_notation(
    arg, float_spec, string_expr, tmp_string, ref_type, loc, symbol_table);
  case_list.push_back(case_sci_notation);

  // Case of NaN
  code_ifthenelset case_nan;
  case_nan.cond()=isnan_exprt(arg);
  case_nan.then_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "NaN", symbol_table);
  case_list.push_back(case_nan);

  // Case of Infinity
  code_ifthenelset case_infinity;
  case_infinity.cond()=isinf_exprt(arg);
  // TODO: should also detect -Infinity
  case_infinity.then_case()=code_assign_string_literal_to_string_expr(
        string_expr, tmp_string, "Infinity", symbol_table);
  case_list.push_back(case_infinity);

  // Case of simple notation
  code_ifthenelset case_simple_notation;

  ieee_floatt bound_inf_float(float_spec);
  ieee_floatt bound_sup_float(float_spec);
  bound_inf_float.from_float(1e-3);
  bound_sup_float.from_float(1e7);
  constant_exprt bound_inf=bound_inf_float.to_expr();
  constant_exprt bound_sup=bound_sup_float.to_expr();

  and_exprt is_simple_float(
    binary_relation_exprt(arg, ID_ge, bound_inf),
    binary_relation_exprt(arg, ID_lt, bound_sup));
  case_simple_notation.cond()=is_simple_float;
  case_simple_notation.then_case()=code_blockt();

  // integer part
  typecast_exprt integer_part(arg, java_int_type());
  string_exprt integer_part_string_expr=fresh_string_expr(loc, symbol_table);

  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      integer_part_string_expr,
      ID_cprover_string_of_int_func,
      {integer_part},
      symbol_table));

  // dot
  string_exprt dot_string_lit=fresh_string_expr(loc, symbol_table);
  case_simple_notation.then_case().copy_to_operands(
    code_assign_string_literal_to_string_expr(
      dot_string_lit, tmp_string, ".", symbol_table));
  string_exprt with_dot_string_expr=fresh_string_expr(loc, symbol_table);

  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      with_dot_string_expr,
      ID_cprover_string_concat_func,
      {integer_part_string_expr, dot_string_lit},
      symbol_table));

  // fractional_part = arg - (float) integer_part
  minus_exprt fractional_part(arg, typecast_exprt(integer_part, arg.type()));
  string_exprt fractional_part_string_expr=fresh_string_expr(loc, symbol_table);
  ieee_floatt shifting(float_spec);
  shifting.from_float(1e7);
  typecast_exprt fractional_part_shifted(
    mult_exprt(fractional_part, shifting.to_expr()), java_int_type());
  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      fractional_part_string_expr,
      ID_cprover_string_of_fractional_part_func,
      {fractional_part_shifted, from_integer(7, java_int_type())},
      symbol_table));

  // string_expr = concat(with_dot_string_expr, string_of_int(fractional_part))
  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr,
      ID_cprover_string_concat_func,
      {with_dot_string_expr, fractional_part_string_expr},
      symbol_table));

  case_list.push_back(case_simple_notation);

  // Combining all cases
  for(std::size_t i=1; i<case_list.size(); i++)
    case_list[i].else_case()=case_list[i-1];
  code.copy_to_operands(case_list[case_list.size()-1]);

  // str = string_expr
  code.copy_to_operands(code_assign_string_expr_to_java_string(
    str, string_expr, symbol_table));

  // Assign string_expr_sym = { string_expr_length, string_expr_content }
  code.copy_to_operands(code_assignt(string_expr_sym, string_expr));

  // Return str
  code.copy_to_operands(code_returnt(str));
  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_init_code

  Inputs:
    type - the type of the function call
    loc - location in program
    symbol_table - the symbol table to populate

 Outputs: code for the String.<init>(java/lang/String) function:
          > cprover_string_length = arg->length;
          > cprover_string_array = *arg1->data;
          > this->length = cprover_string_length;
          > this->data = cprover_string_array;
          > cprover_string = {.=cprover_string_length, .=cprover_string_array};

  Purpose: Generate the goto code for string initialization.

\*******************************************************************/

codet java_string_library_preprocesst::make_init_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  // Getting the assignment arguments (String arg0 = new String(arg1);)
  code_typet::parameterst params=type.parameters();
  assert(params.size()==2 && "wrong number of parameters in String.<init>");
  exprt arg0=symbol_exprt(params[0].get_identifier(), params[0].type());
  exprt arg1=symbol_exprt(params[1].get_identifier(), params[1].type());

  // Holder for output code
  code_blockt code;

  // Declaring and allocating String * str

  // Declaring cprover_string string_expr
  string_exprt string_expr=fresh_string_expr(loc, symbol_table);
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table);

  // Make the assignment: string_expr <- arg1
  code.copy_to_operands(
    code_assign_java_string_to_string_expr(string_expr, arg1, symbol_table));

  // Make the assignment: arg0 <- string_expr
  code.copy_to_operands(
    code_assign_string_expr_to_java_string(arg0, string_expr, symbol_table));

  code.copy_to_operands(code_assignt(string_expr_sym, string_expr));

  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_init_function_from_call

  Inputs:
    type - the type of the function call
    loc - location in program
    symbol_table - the symbol table to populate
    ignore_first_arg - boolean flag telling that the first argument
        should not be part of the arguments of the call (but only used
        to be assigned the result)

 Outputs: code for the String.<init>(args) function:
          > cprover_string_length = fun(arg).length;
          > cprover_string_array = fun(arg).data;
          > this->length = cprover_string_length;
          > this->data = cprover_string_array;
          > cprover_string = {.=cprover_string_length, .=cprover_string_array};

  Purpose: Generate the goto code for string initialization.

  TODO: part of this function could be factorized with make_init_code

\*******************************************************************/

codet java_string_library_preprocesst::make_init_function_from_call(
  const irep_idt &function_name,
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  bool ignore_first_arg)
{
  code_typet::parameterst params=type.parameters();

  // The first parameter is the object to be initialized
  assert(!params.empty());
  exprt arg_this=symbol_exprt(params[0].get_identifier(), params[0].type());
  if(ignore_first_arg)
    params.erase(params.begin());

  // Holder for output code
  code_blockt code;

  // Processing parameters
  exprt::operandst args=process_parameters(params, loc, symbol_table, code);

  // Declaring cprover_string string_expr
  refined_string_typet refined_string_type(java_int_type(), java_char_type());
  string_exprt string_expr=fresh_string_expr(loc, symbol_table);
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table);

  // Make the assignment: string_expr <- function(arg1)
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr, function_name, args, symbol_table));

  // Make the assignment: arg_this <- string_expr
  code.copy_to_operands(code_assign_string_expr_to_java_string(
                          arg_this, string_expr, symbol_table));

  code.copy_to_operands(code_assignt(string_expr_sym, string_expr));

  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::
            make_assign_and_return_function_from_call

  Inputs:
    function_name - name of the function to be called
    type - the type of the function call
    loc - location in program
    symbol_table - the symbol table to populate

 Outputs: code

  Purpose: Call a cprover internal function, assign the result to
           object `this` and return it.

\*******************************************************************/

codet java_string_library_preprocesst::
  make_assign_and_return_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table)
{
  // This is similar to initialization function except we also return
  // a pointer to `this`
  code_typet::parameterst params=type.parameters();
  assert(!params.empty());
  exprt arg_this=symbol_exprt(params[0].get_identifier(), params[0].type());
  codet code=make_init_function_from_call(
    function_name, type, loc, symbol_table, false);
  code.copy_to_operands(code_returnt(arg_this));
  return code;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::make_char_at_code

  Inputs:

 Outputs:

\*******************************************************************/

codet java_string_library_preprocesst::make_char_at_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  return make_function_from_call(
    ID_cprover_string_char_at_func, type, loc, symbol_table);
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_function

  Inputs:

 Outputs:

\*******************************************************************/

codet java_string_library_preprocesst::make_function_from_call(
  const irep_idt &function_name,
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  code_blockt code;
  exprt::operandst args=process_parameters(
    type.parameters(), loc, symbol_table, code);
  code.copy_to_operands(code_return_function_application(
    function_name, args, type.return_type(), symbol_table));
  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_string_returning_function

  Inputs:

 Outputs: code :
          > string_expr = function_name(args)
          > string = string_expr_to_string(string)
          > return string

\*******************************************************************/

codet java_string_library_preprocesst::
  make_string_returning_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table)
{
  // Getting types
  typet length_type=string_length_type(symbol_table);

  // String expression that will hold the result
  refined_string_typet ref_type(length_type, java_char_type());
  string_exprt string_expr=fresh_string_expr(loc, symbol_table);
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table);

  // Code for the output
  code_blockt code;

  // Calling the function
  exprt::operandst arguments=process_parameters(
    type.parameters(), loc, symbol_table, code);
  code.copy_to_operands(code_assign_function_to_string_expr(
    string_expr, function_name, arguments, symbol_table));

  // Assigning string_expr to symbol for keeping track of it
  code.copy_to_operands((string_expr_sym, string_expr));

  // Assigning to string
  exprt str=fresh_string(type.return_type(), loc, symbol_table);
  code.copy_to_operands(code_assign_string_expr_to_java_string(
    str, string_expr, symbol_table));

  // Return value
  code.copy_to_operands(code_returnt(str));
  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::code_of_function

  Inputs:
    function_id - name of the function
    type - its type
    loc - location in the program
    symbol_table - a symbol table

 Outputs: code for the body of the String functions if they are part
          of the supported String functions nil_exprt otherwise.

\*******************************************************************/

exprt java_string_library_preprocesst::code_of_function(
  const irep_idt &function_id,
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  auto it_id=cprover_equivalent_to_java_function.find(function_id);
  if(it_id!=cprover_equivalent_to_java_function.end())
    return make_function_from_call(it_id->second, type, loc, symbol_table);

  it_id=cprover_equivalent_to_java_initialization_function.find(function_id);
  if(it_id!=cprover_equivalent_to_java_initialization_function.end())
    return make_init_function_from_call(
      it_id->second, type, loc, symbol_table);

  it_id=cprover_equivalent_to_java_assign_and_return_function.find(function_id);
  if(it_id!=cprover_equivalent_to_java_assign_and_return_function.end())
    return make_assign_and_return_function_from_call(
      it_id->second, type, loc, symbol_table);

  auto it=conversion_table.find(function_id);
  if(it!=conversion_table.end())
    return it->second(type, loc, symbol_table);

  return nil_exprt();
}

/*******************************************************************\

Function: java_string_library_preprocesst::add_string_type_success

  Inputs:
    class_name - name of the class
    symbol_table - a symbol table

 Outputs: true if the type is one that is known to our preprocessing

 Purpose: Declare a class for String types that are used in the program

\*******************************************************************/

bool java_string_library_preprocesst::add_string_type_success(
  irep_idt class_name, symbol_tablet &symbol_table)
{
  if(string_types.find(class_name)!=string_types.end())
  {
    add_string_type(class_name, symbol_table);
    return true;
  }
  else
    return false;
}

/*******************************************************************\

Function: java_string_library_preprocesst::initialize_conversion_table

 Purpose: fill maps with correspondance from java method names to
          conversion functions

\*******************************************************************/

void java_string_library_preprocesst::initialize_conversion_table()
{
  character_preprocess.initialize_conversion_table();

  string_types={"java.lang.String",
                "java.lang.StringBuilder",
                "java.lang.CharSequence",
                "java.lang.StringBuffer"};

  // String library
#if 0  //this duplicates the following one
  conversion_table["java::java.lang.String.<init>:(Ljava/lang/String;)V"]=
    &java_string_library_preprocesst::make_init_code;
#endif
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.String.<init>:(Ljava/lang/String;)V"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.String.<init>:(Ljava/lang/StringBuilder;)V"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.String.<init>:([C)V"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.String.<init>:([CII)V"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.String.<init>:()V"]=
      ID_cprover_string_empty_string_func;
  // Not supported java.lang.String.<init>:(Ljava/lang/StringBuffer;)

  cprover_equivalent_to_java_function
    ["java::java.lang.String.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.codePointAt:(I)I"]=
      ID_cprover_string_code_point_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.codePointBefore:(I)I"]=
      ID_cprover_string_code_point_before_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.codePointCount:(II)I"]=
      ID_cprover_string_code_point_count_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.compareTo:(Ljava/lang/String;)I"]=
      ID_cprover_string_compare_to_func;
  // Not supported "java.lang.String.contentEquals"
  cprover_equivalent_to_java_function
    ["java::java.lang.String.concat:(Ljava/lang/String;)Ljava/lang/String;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.contains:(Ljava/lang/CharSequence;)Z"]=
    ID_cprover_string_contains_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.copyValueOf:([CII)Ljava/lang/String;"]=
    ID_cprover_string_copy_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.copyValueOf:([C)Ljava/lang/String;"]=
    ID_cprover_string_copy_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.endsWith:(Ljava/lang/String;)Z"]=
      ID_cprover_string_endswith_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.equals:(Ljava/lang/Object;)Z"]=
      ID_cprover_string_equal_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.equalsIgnoreCase:(Ljava/lang/String;)Z"]=
      ID_cprover_string_equals_ignore_case_func;
  // Not supported "java.lang.String.format"
  // Not supported "java.lang.String.getBytes"
  // Not supported "java.lang.String.getChars"
  cprover_equivalent_to_java_function
    ["java::java.lang.String.hashCode:()I"]=
      ID_cprover_string_hash_code_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.indexOf:(I)I"]=
      ID_cprover_string_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.indexOf:(II)I"]=
      ID_cprover_string_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.indexOf:(Ljava/lang/String;)I"]=
      ID_cprover_string_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.indexOf:(Ljava/lang/String;I)I"]=
      ID_cprover_string_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.intern:()Ljava/lang/String;"]=
      ID_cprover_string_intern_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.isEmpty:()Z"]=
      ID_cprover_string_is_empty_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.lastIndexOf:(I)I"]=
      ID_cprover_string_last_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.lastIndexOf:(II)I"]=
      ID_cprover_string_last_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.lastIndexOf:(Ljava/lang/String;)I"]=
      ID_cprover_string_last_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.lastIndexOf:(Ljava/lang/String;I)I"]=
      ID_cprover_string_last_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.length:()I"]=
      ID_cprover_string_length_func;
  // Not supported "java.lang.String.matches"
  cprover_equivalent_to_java_function
    ["java::java.lang.String.offsetByCodePoints:(II)I"]=
      ID_cprover_string_offset_by_code_point_func;
  // Not supported "java.lang.String.regionMatches"
  cprover_equivalent_to_java_function
    ["java::java.lang.String.replace:(CC)Ljava/lang/String;"]=
      ID_cprover_string_replace_func;
  // Not supported "java.lang.String.replace:(LCharSequence;LCharSequence)"
  // Not supported "java.lang.String.replaceAll"
  // Not supported "java.lang.String.replaceFirst"
  // Not supported "java.lang.String.split"
  cprover_equivalent_to_java_function
    ["java::java.lang.String.startsWith:(Ljava/lang/String;)Z"]=
      ID_cprover_string_startswith_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.startsWith:(Ljava/lang/String;I)Z"]=
      ID_cprover_string_startswith_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.subSequence:(II)Ljava/lang/CharSequence;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.substring:(II)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  // "java.lang.String.toCharArray has a special treatment in the
  // replace_string_calls function
  cprover_equivalent_to_java_function
    ["java::java.lang.String.toLowerCase:()Ljava/lang/String;"]=
      ID_cprover_string_to_lower_case_func;
  // Not supported "java.lang.String.toLowerCase:(Locale)"
  // Not supported "java.lang.String.toString:()"
  cprover_equivalent_to_java_function
    ["java::java.lang.String.toUpperCase:()Ljava/lang/String;"]=
      ID_cprover_string_to_upper_case_func;
  // Not supported "java.lang.String.toUpperCase:(Locale)"
  cprover_equivalent_to_java_function
    ["java::java.lang.String.trim:()Ljava/lang/String;"]=
      ID_cprover_string_trim_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.valueOf:(Z)Ljava/lang/String;"]=
      ID_cprover_string_of_bool_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.valueOf:(C)Ljava/lang/String;"]=
      ID_cprover_string_of_char_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.valueOf:([C)Ljava/lang/String;"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.valueOf:([CII)Ljava/lang/String;"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.valueOf:(D)Ljava/lang/String;"]=
      ID_cprover_string_of_double_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.valueOf:(F)Ljava/lang/String;"]=
      ID_cprover_string_of_float_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.valueOf:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.valueOf:(J)Ljava/lang/String;"]=
      ID_cprover_string_of_long_func;
  // Not supported "java.lang.String.valueOf:(LObject;)"

  // StringBuilder library
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.StringBuilder.<init>:(Ljava/lang/String;)V"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.StringBuilder.<init>:()V"]=
      ID_cprover_string_empty_string_func;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Z)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(C)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:([C)"
      "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_func;
  // Not supported: "java.lang.StringBuilder.append:([CII)"
  // Not supported: "java.lang.StringBuilder.append:(LCharSequence;)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(D)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_double_func;
  conversion_table["java::java.lang.StringBuilder.append:"
                   "(F)Ljava/lang/StringBuilder;"]=
    &java_string_library_preprocesst::make_string_builder_append_float_code;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(I)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(J)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_long_func;

  conversion_table["java::java.lang.StringBuilder.append:"
                   "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"]=
    &java_string_library_preprocesst::make_string_builder_append_object_code;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Ljava/lang/String;)"
      "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.appendCodePoint:(I)"
     "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_code_point_func;
  // Not supported: "java.lang.StringBuilder.append:(Ljava/lang/StringBuffer;)"
  // Not supported: "java.lang.StringBuilder.capacity:()"
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.codePointAt:(I)I"]=
      ID_cprover_string_code_point_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.codePointBefore:(I)I"]=
      ID_cprover_string_code_point_before_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.codePointCount:(II)I"]=
      ID_cprover_string_code_point_count_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.delete:(II)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_delete_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.deleteCharAt:(I)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_delete_char_at_func;
  // Not supported: "java.lang.StringBuilder.ensureCapacity:()"
  // Not supported: "java.lang.StringBuilder.getChars:()"
  // Not supported: "java.lang.StringBuilder.indexOf:()"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(IZ)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(IC)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(I[C)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(I[CII)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  // Not supported "java.lang.StringBuilder.insert:(ILCharSequence;)"
  // Not supported "java.lang.StringBuilder.insert:(ILCharSequence;II)"
  // Not supported "java.lang.StringBuilder.insert:(ID)"
  // Not supported "java.lang.StringBuilder.insert:(IF)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(II)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(IJ)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_long_func;
  // Not supported "java.lang.StringBuilder.insert:(ILObject;)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(ILjava/lang/String;)"
     "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  // Not supported "java.lang.StringBuilder.lastIndexOf"
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.length:()I"]=
      ID_cprover_string_length_func;
  // Not supported "java.lang.StringBuilder.offsetByCodePoints"
  // Not supported "java.lang.StringBuilder.replace"
  // Not supported "java.lang.StringBuilder.reverse"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.setCharAt:(IC)V"]=
      ID_cprover_string_char_set_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.setLength:(I)V"]=
      ID_cprover_string_set_length_func;
  // Not supported "java.lang.StringBuilder.subSequence"
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.substring:(II)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.toString:()Ljava/lang/String;"]=
      ID_cprover_string_copy_func;
  // Not supported "java.lang.StringBuilder.trimToSize"
  // TODO clean irep ids from insert_char_array etc...

  // StringBuffer library
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.StringBuffer.<init>:(Ljava/lang/String;)V"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_initialization_function
    ["java::java.lang.StringBuffer.<init>:()V"]=
      ID_cprover_string_empty_string_func;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(Z)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(C)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:([C)"
      "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_func;
  // Not supported: "java.lang.StringBuffer.append:([CII)"
  // Not supported: "java.lang.StringBuffer.append:(LCharSequence;)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(D)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_double_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(F)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_float_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(I)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(J)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_long_func;
  // Not supported: "java.lang.StringBuffer.append:(LObject;)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(Ljava/lang/String;)"
      "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.appendCodePoint:(I)"
     "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_code_point_func;
  // Not supported: "java.lang.StringBuffer.append:(Ljava/lang/StringBuffer;)"
  // Not supported: "java.lang.StringBuffer.capacity:()"
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointAt:(I)I"]=
      ID_cprover_string_code_point_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointBefore:(I)I"]=
      ID_cprover_string_code_point_before_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointCount:(II)I"]=
      ID_cprover_string_code_point_count_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.delete:(II)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_delete_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.deleteCharAt:(I)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_delete_char_at_func;
  // Not supported: "java.lang.StringBuffer.ensureCapacity:()"
  // Not supported: "java.lang.StringBuffer.getChars:()"
  // Not supported: "java.lang.StringBuffer.indexOf:()"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IZ)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IC)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(I[C)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(I[CII)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  // Not supported "java.lang.StringBuffer.insert:(ILCharSequence;)"
  // Not supported "java.lang.StringBuffer.insert:(ILCharSequence;II)"
  // Not supported "java.lang.StringBuffer.insert:(ID)"
  // Not supported "java.lang.StringBuffer.insert:(IF)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(II)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IJ)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_long_func;
  // Not supported "java.lang.StringBuffer.insert:(ILObject;)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(ILjava/lang/String;)"
     "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  // Not supported "java.lang.StringBuffer.lastIndexOf"
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.length:()I"]=
      ID_cprover_string_length_func;
  // Not supported "java.lang.StringBuffer.offsetByCodePoints"
  // Not supported "java.lang.StringBuffer.replace"
  // Not supported "java.lang.StringBuffer.reverse"
  cprover_equivalent_to_java_assign_and_return_function["java::java.lang.StringBuffer.setCharAt:(IC)V"]=
    ID_cprover_string_char_set_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.setLength:(I)V"]=
    ID_cprover_string_set_length_func;
  // Not supported "java.lang.StringBuffer.subSequence"
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.substring:(II)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.toString:()Ljava/lang/String;"]=
      ID_cprover_string_copy_func;
  // Not supported "java.lang.StringBuffer.trimToSize"

  // Other libraries
  cprover_equivalent_to_java_function
    ["java::java.lang.CharSequence.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  conversion_table
    ["java::java.lang.Float.toString:(F)Ljava/lang/String;"]=
      &java_string_library_preprocesst::make_float_to_string_code;
  cprover_equivalent_to_java_function
    ["java::java.lang.Integer.toHexString:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_hex_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.Integer.parseInt:(Ljava/lang/String;)I"]=
      ID_cprover_string_parse_int_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.Integer.toString:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_func;

}
