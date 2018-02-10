/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Basic blocks detection for Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H
#define CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H

#include <unordered_set>

#include <goto-programs/goto_model.h>

class message_handlert;

class cover_blocks_baset
{
public:
  /// \param t a goto instruction
  /// \return the block number of the block
  ///         the given goto instruction is part of
  virtual std::size_t block_of(goto_programt::const_targett t) const = 0;

  /// \param block_nr a block number
  /// \return  the instruction selected for
  ///   instrumentation representative of the given block
  virtual optionalt<goto_programt::const_targett>
  instruction_of(std::size_t block_nr) const = 0;

  /// \param block_nr a block number
  /// \return  the source location selected for
  ///   instrumentation representative of the given block
  virtual const source_locationt &
  source_location_of(std::size_t block_nr) const = 0;

  /// Select an instruction to be instrumented for each basic block such that
  /// the java bytecode indices for each basic block is unique
  /// \param goto_program The goto program
  /// \param message_handler The message handler
  virtual void select_unique_java_bytecode_indices(
    const goto_programt &goto_program,
    message_handlert &message_handler){};

  /// Outputs the list of blocks
  virtual void output(std::ostream &out) const = 0;

  /// Output warnings about ignored blocks
  /// \param goto_program The goto program
  /// \param message_handler The message handler
  virtual void report_block_anomalies(
    const goto_programt &goto_program,
    message_handlert &message_handler){};
};

class cover_basic_blockst : public cover_blocks_baset
{
public:
  struct block_infot
  {
    /// the program instruction representative for this block
    optionalt<goto_programt::const_targett> representative_inst;

    /// the source location representative for this block
    // (we need a separate copy of source locations because we attach
    //  the line number ranges to them)
    source_locationt source_location;

    /// the set of lines belonging to this block
    std::unordered_set<unsigned> lines;
  };

  explicit cover_basic_blockst(const goto_programt &_goto_program);

  /// \param t a goto instruction
  /// \return the block number of the block
  ///         the given goto instruction is part of
  std::size_t block_of(goto_programt::const_targett t) const override;

  /// \param block_nr a block number
  /// \return  the instruction selected for
  ///   instrumentation representative of the given block
  optionalt<goto_programt::const_targett>
  instruction_of(std::size_t block_nr) const override;

  /// \param block_nr a block number
  /// \return  the source location selected for
  ///   instrumentation representative of the given block
  const source_locationt &
  source_location_of(std::size_t block_nr) const override;

  /// Select an instruction to be instrumented for each basic block such that
  /// the java bytecode indices for each basic block is unique
  /// \param goto_program The goto program
  /// \param message_handler The message handler
  void select_unique_java_bytecode_indices(
    const goto_programt &goto_program,
    message_handlert &message_handler) override;

  /// Output warnings about ignored blocks
  /// \param goto_program The goto program
  /// \param message_handler The message handler
  void report_block_anomalies(
    const goto_programt &goto_program,
    message_handlert &message_handler) override;

  /// Outputs the list of blocks
  void output(std::ostream &out) const override;

private:
  // map program locations to block numbers
  std::map<goto_programt::const_targett, unsigned> block_map;
  std::vector<block_infot> block_infos;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_BASIC_BLOCKS_H
