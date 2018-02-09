/*******************************************************************\

Module: Coverage Instrumentation

Author:

\*******************************************************************/

/// \file
/// Location blocks detection for Coverage Instrumentation

#include "cover_location_blocks.h"

#include <util/message.h>

cover_location_blockst::cover_location_blockst(
  const goto_programt &_goto_program)
{
  forall_goto_program_instructions(it, _goto_program)
  {
    const auto &bytecode_index = it->source_location.get_java_bytecode_index();
    if(!index_to_block.count(bytecode_index))
    {
      block_infos.push_back(it);
      index_to_block.insert(
        std::make_pair(bytecode_index, block_infos.size() - 1));
    }
  }
}

std::size_t
cover_location_blockst::block_of(goto_programt::const_targett t) const
{
  const auto &bytecode_index = t->source_location.get_java_bytecode_index();
  const auto it = index_to_block.find(bytecode_index);
  INVARIANT(it != index_to_block.end(), "instruction must be part of a block");
  return it->second;
}

optionalt<goto_programt::const_targett>
cover_location_blockst::instruction_of(const std::size_t block_nr) const
{
  INVARIANT(block_nr < block_infos.size(), "block number out of range");
  return block_infos.at(block_nr);
}

const source_locationt &
cover_location_blockst::source_location_of(const std::size_t block_nr) const
{
  INVARIANT(block_nr < block_infos.size(), "block number out of range");
  return block_infos.at(block_nr)->source_location;
}

void cover_location_blockst::output(std::ostream &out) const
{
  for(const auto &block_pair : block_map)
    out << block_pair.first->source_location << " -> " << block_pair.second
        << '\n';
}
