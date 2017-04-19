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
#include "java_types.h"

#include "java_string_libraries_preprocess.h"

// Identifiers for string functions
#define ID_STRING_BUILDER_APPEND_OBJECT 0

/*******************************************************************\

Constructor: java_string_libraries_preprocesst

     Inputs:
       _symbol_table - a symbol table

    Purpose: initialize the symbol_table field and the conversion table.

\*******************************************************************/

java_string_libraries_preprocesst::java_string_libraries_preprocesst(
  symbol_tablet _symbol_table):
    symbol_table(_symbol_table)
{ }

/*******************************************************************\

Function: java_string_libraries_preprocesst::check_java_type

  Inputs: a type and a string

 Outputs: Boolean telling whether the type is a struct with the given
          tag or a symbolic type with the tag prefixed by "java::"

\*******************************************************************/

bool java_string_libraries_preprocesst::check_java_type(
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

Function: java_string_libraries_preprocesst::is_java_string_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string pointers

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_pointer_type(
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

Function: java_string_libraries_preprocesst::is_java_string_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.String");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_builder_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string builder

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_builder_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.StringBuilder");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_builder_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java StringBuilder
          pointers

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_builder_pointer_type(
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

Function: java_string_libraries_preprocesst::is_java_string_buffer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string buffer

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_buffer_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.StringBuffer");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_buffer_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java StringBuffer
          pointers

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_buffer_pointer_type(
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

Function: java_string_libraries_preprocesst::is_java_char_sequence_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char sequence

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_char_sequence_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.CharSequence");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_char_sequence_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of a pointer
          to a java char sequence

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_char_sequence_pointer_type(
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

Function: java_string_libraries_preprocesst::is_java_char_array_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char array

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_char_array_type(
  const typet &type)
{
  return check_java_type(type, "array[char]");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_char_array_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of a pointer
          to a java char array

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_char_array_pointer_type(
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

Function: java_string_libraries_preprocesst::string_data_type

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

Function: java_string_libraries_preprocesst::string_length_type

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

Function: fresh_array

  Inputs:
    type - an array type
    location - a location in the program

 Outputs: a new symbol

 Purpose: add a symbol in the table with static lifetime and name
          containing `cprover_string_array` and given type

\*******************************************************************/

symbol_exprt java_string_libraries_preprocesst::fresh_array(
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

Function: java_string_libraries_preprocesst::declare_function

  Inputs: a name and a type

 Purpose: declare a function with the given name and type

 TODO: duplicates goto_programs/string_refine_preprocess function

\*******************************************************************/

void java_string_libraries_preprocesst::declare_function(
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

 Outputs: a list of expressions

 Purpose: for each expression that is of a type implementing strings,
          we declare a new `cprover_string` whose contents is deduced
          from the expression and replace the
          expression by this cprover_string in the output list;
          in the other case the expression is kept as is for the output list.

\*******************************************************************/

exprt::operandst java_string_libraries_preprocesst::process_arguments(
  const code_typet::parameterst &params, symbol_tablet &symbol_table)
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
      string_exprt str(length, data, ref_type);
      ops.push_back(str);
    }
    else
    {
      ops.push_back(symbol_exprt(p.get_identifier(), p.type()));
    }
  }
  return ops;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::fresh_string

  Inputs:
    type - a type for refined strings
    location - a location in the program

 Outputs: a new symbol

 Purpose: add a symbol with static lifetime and name containing
          `cprover_string` and given type

\*******************************************************************/

symbol_exprt java_string_libraries_preprocesst::fresh_string(
  const typet &type, const source_locationt &loc, symbol_tablet &symbol_table)
{
  symbolt string_symbol=get_fresh_aux_symbol(
    type, "java::cprover_string", "cprover_string", loc, ID_java, symbol_table);
  string_symbol.is_static_lifetime=true;
  return string_symbol.symbol_expr();
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::fresh_string_expr

  Inputs:
    type - a type for refined strings
    location - a location in the program

 Outputs: a new string_expr

 Purpose: add symbols with prefixe cprover_string_length and
          cprover_string_data and construct a string_expr from them.

\*******************************************************************/

string_exprt java_string_libraries_preprocesst::fresh_string_expr(
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
  symbol_exprt content_field=fresh_array(type.get_content_type(), loc, symbol_table);
  string_exprt str(length_field, content_field, type);
  return str;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::code_assign_function_to_string_expr

  Inputs:
    str - a string expression
    function_type - a function type
    function_name - the name of the function

  Output: return the following code:
          > str->length=function_name_length(arguments)
          > str->data=function_name_data(arguments)

\*******************************************************************/

codet java_string_libraries_preprocesst::code_assign_function_to_string_expr(
  const string_exprt &str,
  const irep_idt &function_name,
  const code_typet &function_type,
  const exprt::operandst &arguments,
  symbol_tablet &symbol_table)
{
  assert(implements_java_char_sequence(function_type.return_type()));

  // Getting types
  typet length_type=string_length_type(symbol_table);
  typet data_type=string_data_type(symbol_table);

  // Names of function to call
  std::string fun_name_length="java::"+id2string(function_name)+"_length";
  std::string fun_name_data="java::"+id2string(function_name)+"_data";

  // Declaring functions
  declare_function(fun_name_length, length_type, symbol_table);
  declare_function(fun_name_data, data_type.subtype(), symbol_table);

  // Declaring function applications
  function_application_exprt rhs_length(
    symbol_exprt(fun_name_length), length_type);
  function_application_exprt rhs_data(
    symbol_exprt(fun_name_data), data_type.subtype());

  // Adding arguments
  rhs_length.arguments()=arguments;
  rhs_data.arguments()=arguments;

  // Assignments
  std::list<codet> assigns;
  assigns.push_back(code_assignt(str.length(), rhs_length));
  assigns.push_back(code_assignt(str.content(), rhs_data));
  return code_blockt(assigns);
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::
            code_assign_string_expr_to_java_string

  Inputs:
    lhs - an expression representing a java string
    rhs - a string expression
    location - a location in the program

  Output: return the following code:
          > lhs->length=rhs.length
          > lhs->data=&rhs.data

\*******************************************************************/

codet java_string_libraries_preprocesst::code_assign_string_expr_to_java_string(
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

Function: java_string_libraries_preprocesst::
            code_assign_java_string_to_string_expr

  Inputs:
    lhs - an expression representing a java string
    rhs - a string expression
    location - a location in the program

  Output: return the following code:
          > rhs.length=lhs->length
          > rhs.data=*(lhs->data)

\*******************************************************************/

codet java_string_libraries_preprocesst::code_assign_java_string_to_string_expr(
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

Function: java_string_libraries_preprocesst::
    make_string_builder_append_object_code

  Inputs:
    code - the code of a function call

 Outputs: code for the StringBuilder.append(Object) function

\*******************************************************************/

codet java_string_libraries_preprocesst::make_string_builder_append_object_code(
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
  string_exprt str=fresh_string_expr(ref_type, loc, symbol_table);

  exprt::operandst arguments=process_arguments(type.parameters(), symbol_table);
  assert(arguments.size()==2);

  // Case of Strings
  exprt::operandst arguments_string=arguments;
  string_exprt string_expr_argument=fresh_string_expr(ref_type, loc, symbol_table);
  typecast_exprt string_argument(
    arguments[1], pointer_typet(symbol_typet("java::java.lang.String")));
  codet assign_to_string_expr=code_assign_java_string_to_string_expr(
    string_expr_argument, string_argument, symbol_table);
  arguments_string[1]=string_expr_argument;
  code_blockt case_string({
    assign_to_string_expr,
    code_assign_function_to_string_expr(
      str, ID_cprover_string_concat_func, type, arguments_string, symbol_table)});

  // Case of StringBuilders
  exprt::operandst arguments_string_builder=arguments;
  typecast_exprt string_builder_argument(
    arguments[1], pointer_typet(symbol_typet("java::java.lang.StringBuilder")));
  codet assign_builder_to_string_expr=code_assign_java_string_to_string_expr(
    string_expr_argument, string_builder_argument, symbol_table);
  arguments_string_builder[1]=string_expr_argument;
  code_blockt case_string_builder({
    assign_builder_to_string_expr,
    code_assign_function_to_string_expr(
      str, ID_cprover_string_concat_func, type, arguments_string_builder, symbol_table)});

#if 0
  // Case of Integers
  exprt::operandst arguments_int=arguments;
  arguments_int[1]=typecast_exprt(
    arguments_int[1], symbol_typet("java::java.lang.Integer"));
  codet case_int=code_assign_function_to_string_expr(
    str, ID_cprover_string_concat_int_func, type, arguments_int);
#endif

  // Other cases
  // TODO: we should call "java.lang.Object.toString:()Ljava/lang/String;"
  codet default_case;
  default_case.make_nil();

  // Assigning string expression to the java string
  codet assign_result_to_string=code_assign_string_expr_to_java_string(
    this_obj, str, symbol_table);

  // Looking for class identifier
  symbolt sym_type=symbol_table.lookup("java::java.lang.StringBuilder");
  this_obj.type()=pointer_typet(sym_type.type);
  member_exprt obj(
    dereference_exprt(this_obj, this_obj.type().subtype()),
    "@java.lang.Object",
    symbol_typet("java::java.lang.Object"));
  member_exprt class_id(obj, "@class_identifier", string_typet());

  // Making conditional statement
  code_ifthenelset conditional_string, conditional_string_builder;
  equal_exprt is_string(
     class_id, constant_exprt("java.lang.String", string_typet()));
  equal_exprt is_string_builder(
    class_id, constant_exprt("java.lang.StringBuilder", string_typet()));

  conditional_string_builder.cond()=is_string_builder;
  conditional_string_builder.then_case()=case_string_builder;
  conditional_string_builder.else_case()=default_case;

  conditional_string.cond()=is_string;
  conditional_string.then_case()=case_string;
  conditional_string.else_case()=conditional_string_builder;

  // Return statement
  code_returnt ret(this_obj);

  return code_blockt({conditional_string, assign_result_to_string, ret});
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::replace_string_call

  Inputs:
    code - the code of a function call

 Outputs: code for the body of the String functions if they are part
          of the supported String functions nil_exprt otherwise.

\*******************************************************************/

exprt java_string_libraries_preprocesst::code_of_function(
  const irep_idt &function_id,
  const code_typet &type,
  const source_locationt &loc)
{
  auto it=conversion_table.find(function_id);
  if(it!=conversion_table.end())
    return it->second(type, loc, symbol_table);

  return nil_exprt();
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::initialize_conversion_table

 Purpose: fill maps with correspondance from java method names to
          conversion functions

\*******************************************************************/

void java_string_libraries_preprocesst::initialize_conversion_table()
{
  conversion_table["java::java.lang.StringBuilder.append:"
                   "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"]=
    &java_string_libraries_preprocesst::make_string_builder_append_object_code;
}
