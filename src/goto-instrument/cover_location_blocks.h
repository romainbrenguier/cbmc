/*******************************************************************\

Module: Coverage Instrumentation

Author:

\*******************************************************************/

/// \file
/// Location blocks detection for Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_LOCATION_BLOCKS_H
#define CPROVER_GOTO_INSTRUMENT_COVER_LOCATION_BLOCKS_H

#include <goto-programs/goto_model.h>
#include "cover_basic_blocks.h"

class cover_location_blockst : public cover_blocks_baset
{
public:
  struct block_infot
  {
    /// the program instruction representative for this block
    goto_programt::const_targett representative_inst;

    /// the corresponding bytecode index
    dstringt bytecode_index;
  };

private:
  // map program locations to block numbers
  std::map<goto_programt::const_targett, std::size_t> block_map;
  // map block number to first instruction of the block
  std::vector<goto_programt::const_targett> block_infos;
  // map java indexes to block indexes
  std::unordered_map<dstringt, std::size_t, dstring_hash> index_to_block;

public:
  explicit cover_location_blockst(const goto_programt &_goto_program);

  /// \param t a goto instruction
  /// \return block number the given goto instruction is part of
  std::size_t block_of(goto_programt::const_targett t) const override;

  /// \param block_number a block number
  /// \return first instruction of the given block
  optionalt<goto_programt::const_targett>
  instruction_of(std::size_t block_number) const override;

  /// \param block_number a block number
  /// \return source location corresponding to the given block
  const source_locationt &
  source_location_of(std::size_t block_number) const override;

  /// Outputs the list of blocks
  void output(std::ostream &out) const override;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_LOCATION_BLOCKS_H
