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

 Purpose: for each expression that is of a type implementing strings,
          we declare a new `cprover_string` whose contents is deduced
          from the expression and replace the
          expression by this cprover_string in the output list;
          in the other case the expression is kept as is for the output list.

\*******************************************************************/

exprt::operandst java_string_library_preprocesst::process_arguments(
  const code_typet::parameterst &params,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  exprt::operandst ops;
  for(const auto &p : params)
  {
    if(implements_java_char_sequence(p.type()))
    {
      refined_string_typet ref_type(
        string_length_type(symbol_table),
        string_data_type(symbol_table).subtype().subtype());
      symbol_exprt sym(p.get_identifier(), p.type());
      dereference_exprt deref(sym, to_pointer_type(sym.type()).subtype());
      member_exprt length(deref, "length", string_length_type(symbol_table));
      member_exprt data(deref, "data", string_data_type(symbol_table));
      dereference_exprt deref_data(data, data.type().subtype());
      string_exprt string_expr=fresh_string_expr(ref_type, loc, symbol_table);
      exprt string_expr_sym=fresh_string_expr_symbol(
        ref_type, loc, symbol_table);
      init_code.copy_to_operands(code_declt(string_expr.length()));
      init_code.copy_to_operands(code_declt(string_expr.content()));
      init_code.copy_to_operands(code_declt(string_expr_sym));
      init_code.copy_to_operands(code_assignt(string_expr.length(), length));
      init_code.copy_to_operands(code_assignt(string_expr.content(), deref_data));
          init_code.copy_to_operands(code_assignt(string_expr_sym, string_expr));
      ops.push_back(string_expr);
    }
    else
    {
      ops.push_back(symbol_exprt(p.get_identifier(), p.type()));
    }
  }
  return ops;
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
  const refined_string_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
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
  const refined_string_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  symbolt sym=get_fresh_aux_symbol(
    type,
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
    lhs - an expression representing a java string
    rhs - a string expression
    location - a location in the program

  Output: return the following code:
          > rhs.length=lhs->length
          > rhs.data=*(lhs->data)

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

  // Getting types
  typet length_type=string_length_type(symbol_table);
  typet data_type=string_data_type(symbol_table);

  // String expression that will hold the result
  refined_string_typet ref_type(length_type, java_char_type());
  string_exprt string_expr1=fresh_string_expr(ref_type, loc, symbol_table);
  string_exprt string_expr2=fresh_string_expr(ref_type, loc, symbol_table);

  // Code to be returned
  code_blockt code;

  exprt::operandst arguments=process_arguments(
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
  string_exprt string_expr1=fresh_string_expr(ref_type, loc, symbol_table);
  string_exprt string_expr2=fresh_string_expr(ref_type, loc, symbol_table);

  // Code to be returned
  code_blockt code;

  exprt::operandst arguments=process_arguments(
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
  refined_string_typet refined_string_type(java_int_type(), java_char_type());
  string_exprt string_expr=fresh_string_expr(
    refined_string_type, loc, symbol_table);
  exprt string_expr_sym=fresh_string_expr_symbol(
    refined_string_type, loc, symbol_table);

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
  // TODO: specify this subcase
  case_sci_notation.else_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "0.0e0", symbol_table);
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
  string_exprt integer_part_string_expr=fresh_string_expr(
    refined_string_type, loc, symbol_table);

  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      integer_part_string_expr,
      ID_cprover_string_of_int_func,
      {integer_part},
      symbol_table));

  // dot
 string_exprt dot_string_lit=fresh_string_expr(
    refined_string_type, loc, symbol_table);
  case_simple_notation.then_case().copy_to_operands(
    code_assign_string_literal_to_string_expr(
      dot_string_lit, tmp_string, ".", symbol_table));
  string_exprt with_dot_string_expr=fresh_string_expr(
    refined_string_type, loc, symbol_table);

  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      with_dot_string_expr,
      ID_cprover_string_concat_func,
      {integer_part_string_expr, dot_string_lit},
      symbol_table));

  // fractional_part = arg - (float) integer_part
  minus_exprt fractional_part(arg, typecast_exprt(integer_part, arg.type()));
  string_exprt fractional_part_string_expr=fresh_string_expr(
    refined_string_type, loc, symbol_table);
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

Function: java_string_library_preprocesst::make_char_at_code

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
  exprt::operandst args=process_arguments(
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
  string_exprt string_expr=fresh_string_expr(ref_type, loc, symbol_table);
  exprt string_expr_sym=fresh_string_expr_symbol(ref_type, loc, symbol_table);

  // Code for the output
  code_blockt code;

  // Calling the function
  exprt::operandst arguments=process_arguments(
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

  conversion_table["java::java.lang.StringBuilder.append:"
                   "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"]=
    &java_string_library_preprocesst::make_string_builder_append_object_code;

  conversion_table["java::java.lang.StringBuilder.append:"
                   "(F)Ljava/lang/StringBuilder;"]=
    &java_string_library_preprocesst::make_string_builder_append_float_code;

  conversion_table["java::java.lang.Float.toString:(F)Ljava/lang/String;"]=
    &java_string_library_preprocesst::make_float_to_string_code;

  conversion_table["java::java.lang.String.charAt:(I)C"]=
    &java_string_library_preprocesst::make_char_at_code;
}
