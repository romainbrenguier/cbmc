
#ifndef JBCM_CLASS_H
#define JBCM_CLASS_H

#include <util/expanding_vector.h>
#include <util/message.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <analyses/cfg_dominators.h>
#include "java_bytecode_parse_tree.h"
#include "java_bytecode_convert_class.h"

#include <vector>
#include <list>

class symbol_tablet;
class symbolt;
class class_hierarchyt;

class java_bytecode_convert_methodt:public messaget
{
public:
  java_bytecode_convert_methodt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    const bool &_disable_runtime_checks,
    int _max_array_length,
    std::vector<irep_idt>& _needed_methods,
    std::set<irep_idt>& _needed_classes,    
    const class_hierarchyt& _ch);

  typedef java_bytecode_parse_treet::methodt methodt;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  typedef methodt::instructionst instructionst;
  typedef methodt::local_variable_tablet local_variable_tablet;
  typedef methodt::local_variablet local_variablet;

  void operator()(const symbolt &class_symbol, const methodt &method)
  {
    convert(class_symbol, method);
  }

  struct holet {
    unsigned start_pc;
    unsigned length;
  };

  struct local_variable_with_holest
  {
    local_variablet var;
    std::vector<holet> holes;
  };

  typedef std::vector<local_variable_with_holest> local_variable_table_with_holest;

protected:
  irep_idt method_id;
  symbol_tablet &symbol_table;
  const bool &disable_runtime_checks;
  int max_array_length;
  std::vector<irep_idt>& needed_methods;
  std::set<irep_idt>& needed_classes;  
  const class_hierarchyt& class_hierarchy;

  irep_idt current_method;
  typet method_return_type;

 public:
  class variablet
  {
  public:
    symbol_exprt symbol_expr;
    size_t start_pc;
    size_t length;
    bool is_parameter;
    std::vector<holet> holes;
    variablet() : symbol_expr(), is_parameter(false) {}      
  };

 protected:
  typedef std::vector<variablet> variablest;
  expanding_vector<variablest> variables;
  std::set<symbol_exprt> used_local_names;
  
  bool method_has_this;

  typedef enum instruction_sizet
  {
    INST_INDEX = 2, INST_INDEX_CONST = 3
  } instruction_sizet;

  // return corresponding reference of variable
  variablet &find_variable_for_slot(size_t address, variablest &var_list);

  const exprt variable(const exprt&, char type_char, size_t address, bool do_cast = true);

  // temporary variables
  std::list<symbol_exprt> tmp_vars;

  symbol_exprt tmp_variable(const std::string &prefix, const typet &type);

  // JVM program locations
  irep_idt label(const irep_idt &address);

  // JVM Stack
  typedef std::vector<exprt> stackt;
  stackt stack;

  exprt::operandst pop(std::size_t n);
  void push(const exprt::operandst &o);

  struct converted_instructiont
  {
    converted_instructiont(
      const instructionst::const_iterator &it,
      const codet &_code):source(it), code(_code), done(false)
      {}

    instructionst::const_iterator source;
    std::list<unsigned> successors;
    std::set<unsigned> predecessors;
    codet code;
    stackt stack;
    bool done;
  };

public:
  // Expose the address map so that the local variable table code
  // can use it in a template specialisation.
  typedef std::map<unsigned, converted_instructiont> address_mapt;
  typedef std::pair<const methodt&, const address_mapt&> method_with_amapt;
  typedef cfg_dominators_templatet<method_with_amapt,unsigned,false> java_cfg_dominatorst;

protected:
  
  void find_initialisers(
    local_variable_table_with_holest& vars,
    const address_mapt& amap,
    const java_cfg_dominatorst& doms);

  void find_initialisers_for_slot(
    local_variable_table_with_holest::iterator firstvar,
    local_variable_table_with_holest::iterator varlimit,
    const address_mapt& amap,
    const java_cfg_dominatorst& doms);

  void setup_local_variables(const methodt& m, const address_mapt& amap);

  struct block_tree_node {
    bool leaf;
    std::vector<unsigned> branch_addresses;
    std::vector<block_tree_node> branch;
    block_tree_node() : leaf(false) {}
    block_tree_node(bool l) : leaf(l) {}
    static block_tree_node get_leaf() { return block_tree_node(true); }
  };

  code_blockt& get_block_for_pcrange(
    block_tree_node& tree,
    code_blockt& this_block,
    unsigned address_start,
    unsigned address_limit,
    unsigned next_block_start_address);

  code_blockt& get_or_create_block_for_pcrange(
    block_tree_node& tree,
    code_blockt& this_block,
    unsigned address_start,
    unsigned address_limit,
    unsigned next_block_start_address,
    const address_mapt& amap,
    bool allow_merge=true);
  
  // conversion
  void convert(const symbolt &class_symbol, const methodt &);
  void convert(const instructiont &);

  codet convert_instructions(
    const methodt &, const code_typet &);

  const bytecode_infot &get_bytecode_info(const irep_idt &statement);

  void check_static_field_stub(const symbol_exprt& se,
			       const irep_idt& basename);

};

#endif
