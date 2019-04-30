/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_UI_MESSAGE_H
#define CPROVER_UTIL_UI_MESSAGE_H

#include <memory>

#include "cout_message.h"
#include "json_stream.h"
#include "timestamper.h"

/// Wrapper around a message handlert, used to be able to choose whether the
/// object is not owning the pointer, or owning it.
/// In the first case it is initialized from a reference to an object which
/// should outlive this one, in the other case it should be initialized from a
/// unique pointer.
class message_handler_pointert
{
public:
  message_handlert *underlying;

  /// Null pointer
  message_handler_pointert() : underlying(nullptr) {}

  /// Initialization from reference
  explicit message_handler_pointert(message_handlert &message_handler)
    : underlying(&message_handler)
  {}

  message_handlert &operator*()
  {
    return *underlying;
  }

  const message_handlert &operator*() const
  {
    return *underlying;
  }

  message_handlert *operator->()
  {
    return underlying;
  }

  const message_handlert *operator->() const
  {
    return underlying;
  }

  operator bool() const
  {
    return underlying != nullptr;
  }
};

/// Version of message_handler_pointert which owns the object pointed
class owning_message_handler_pointert : public  message_handler_pointert
{
public:
  /// Initialization from unique pointer
  explicit owning_message_handler_pointert(
    std::unique_ptr<message_handlert> message_handler_ptr)
  : value(std::move(message_handler_ptr))
  {
    underlying = &*value;
  }

private:
  std::unique_ptr<message_handlert> value;
};

class ui_message_handlert : public message_handlert
{
public:
  enum class uit { PLAIN, XML_UI, JSON_UI };

  ui_message_handlert(const class cmdlinet &, const std::string &program);

  explicit ui_message_handlert(message_handlert &);
  ui_message_handlert(ui_message_handlert &&) = default;

  virtual ~ui_message_handlert();

  virtual uit get_ui() const
  {
    return _ui;
  }

  virtual void flush(unsigned level) override;

  virtual json_stream_arrayt &get_json_stream()
  {
    PRECONDITION(json_stream!=nullptr);
    return *json_stream;
  }

protected:
  message_handler_pointert message_handler;
  uit _ui;
  const bool always_flush;
  std::unique_ptr<const timestampert> time;
  std::ostream &out;
  std::unique_ptr<json_stream_arrayt> json_stream;

  ui_message_handlert(
    message_handlert *,
    uit,
    const std::string &program,
    const bool always_flush,
    timestampert::clockt clock_type);

  virtual void print(
    unsigned level,
    const std::string &message) override;

  virtual void print(
    unsigned level,
    const std::string &message,
    const source_locationt &location) override;

  virtual void print(
    unsigned level,
    const xmlt &data) override;

  virtual void print(
    unsigned level,
    const jsont &data) override;

  virtual void xml_ui_msg(
    const std::string &type,
    const std::string &msg,
    const source_locationt &location);

  virtual void json_ui_msg(
    const std::string &type,
    const std::string &msg,
    const source_locationt &location);

  virtual void ui_msg(
    const std::string &type,
    const std::string &msg,
    const source_locationt &location);

  const char *level_string(unsigned level);

  std::string command(unsigned c) const override
  {
    if(message_handler)
      return message_handler->command(c);
    else
      return std::string();
  }
};

#define OPT_FLUSH "(flush)"

#define HELP_FLUSH " --flush                      flush every line of output\n"

#endif // CPROVER_UTIL_UI_MESSAGE_H
