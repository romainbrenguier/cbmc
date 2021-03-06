/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java String
        library are recognized by the PASS algorithm

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_STRING_REFINE_PREPROCESS_H
#define CPROVER_GOTO_PROGRAMS_STRING_REFINE_PREPROCESS_H

#include <goto-programs/goto_model.h>
#include <util/ui_message.h>

class string_refine_preprocesst:public messaget
{
 private:
  namespacet ns;
  symbol_tablet & symbol_table;
  goto_functionst & goto_functions;
  std::map<exprt, exprt> string_builders;
  std::map<irep_idt, irep_idt> side_effect_functions;
  std::map<irep_idt, irep_idt> string_functions;
  std::map<irep_idt, irep_idt> c_string_functions;
  std::map<irep_idt, irep_idt> string_function_calls;
  std::map<irep_idt, irep_idt> string_of_char_array_functions;
  std::map<irep_idt, irep_idt> string_of_char_array_function_calls;
  std::map<irep_idt, irep_idt> side_effect_char_array_functions;

 public:
  string_refine_preprocesst
    (symbol_tablet &, goto_functionst &, message_handlert &);

 private:
  // add a temporary symbol to the symbol table
  symbol_exprt new_tmp_symbol(const std::string &name, const typet &type);

  void declare_function(irep_idt function_name, const typet &type);

  exprt replace_string_literals(const exprt &);

  // replace "lhs=s.some_function(x,...)" by "lhs=function_name(s,x,...)"
  void make_string_function
    (goto_programt::instructionst::iterator & i_it, irep_idt function_name);

  // replace "s.some_function(x,...)" by "s=function_name(x,...)"
  void make_string_function_call
    (goto_programt::instructionst::iterator & i_it, irep_idt function_name);

  // replace "r = s.some_function(x,...)" by "s=function_name(s,x,...)"
  // and add a correspondance from r to s in the string_builders map
  void make_string_function_side_effect
    (goto_programt::instructionst::iterator & i_it, irep_idt function_name);

  // replace "return_tmp0 = s.toCharArray()" with:
  // tmp_assign = MALLOC(struct java::array[reference], 17L);
  // tmp_assign->length = (int)__CPROVER_uninterpreted_string_length_func(s);
  // tmp_assign->data = new (void **)[tmp_assign->length];
  // tmp_nil = __CPROVER_uninterpreted_string_data_func(s, tmp_assign->data);
  // return_tmp0 = tmp_assign;
  void make_to_char_array_function
    (goto_programt & goto_program, goto_programt::instructionst::iterator &);

  // replace "r = some_function(arr,...)" by
  // "r = function_name(arr.length,arr.data,...);
  void make_char_array_function
    (goto_programt::instructionst::iterator & i_it, irep_idt function_name);

  // replace "r.some_function(arr,...)" by
  // "r = function_name(arr.length,arr.data,...);
  void make_char_array_function_call
    (goto_programt::instructionst::iterator & i_it, irep_idt function_name);

  // replace `r = s.some_function(i,arr,...)` by
  // `s=function_name(s,i,arr.length,arr.data)`
  // and add a correspondance from r to s in the string_builders map
  void make_char_array_side_effect
    (goto_programt::instructionst::iterator & i_it, irep_idt function_name);

  bool has_java_string_type(const exprt &expr);

  void replace_string_calls(goto_functionst::function_mapt::iterator f_it);
};

#endif
