/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Christopher L. Conway, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::parser::Parser for CVC and SMT-LIbv2 inputs.
 */

#include <sstream>

#include "api/cpp/cvc5.h"
#include "base/output.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "parser/api/cpp/symbol_manager.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/smt2/smt2.h"
#include "parser/symbol_table.cpp"
#include "smt/command.h"
#include "test.h"

using namespace cvc5::parser;
using namespace cvc5::internal::parser;

namespace cvc5::internal {
namespace test {

class TestParserWhiteParser : public TestInternal
{
 protected:
  TestParserWhiteParser(const std::string& lang) : d_lang(lang) {}

  virtual ~TestParserWhiteParser() {}

  void SetUp() override
  {
    TestInternal::SetUp();
    d_symman.reset(nullptr);
    d_solver.reset(new cvc5::Solver());
    d_solver->setOption("parse-only", "true");
  }

  void TearDown() override
  {
    d_symman.reset(nullptr);
    d_solver.reset(nullptr);
  }

  std::string d_lang;
  std::unique_ptr<cvc5::Solver> d_solver;
  std::unique_ptr<SymbolManager> d_symman;
};

/* -------------------------------------------------------------------------- */

class TestParserWhiteSmt2Parser : public TestParserWhiteParser
{
 protected:
  TestParserWhiteSmt2Parser() : TestParserWhiteParser("LANG_SMTLIB_V2_6") {}
};

TEST_F(TestParserWhiteSmt2Parser, showSymbols)
{
  d_symman.reset(new SymbolManager(d_solver.get()));
  std::unique_ptr<Parser> parser(
      ParserBuilder(d_solver.get(), d_symman.get(), true)
          .withInputLanguage("LANG_SMTLIB_V2_6")
          .build());

  Smt2* smt2 = static_cast<Smt2*>(parser.get());
  smt2->setLogic("ALL");

  cvc5::parser::SymbolManager* manager = smt2->getSymbolManager();
  cvc5::internal::parser::SymbolTable* table = manager->getSymbolTable();
  auto implementation = table->d_implementation.get();
  std::cout << "d_exprMap symbols: " << implementation->d_exprMap.size()
            << std::endl;
  for (const auto& p : implementation->d_exprMap)
  {
    std::cout << "  " << p.first << std::endl;
  }
  std::cout << std::endl;
  std::cout << "d_typeMap symbols: " << implementation->d_typeMap.size()
            << std::endl;
  for (const auto& p : implementation->d_typeMap)
  {
    std::cout << "  " << p.first << std::endl;
  }
  std::cout << "d_operatorKindMap symbols: " << smt2->d_operatorKindMap.size()
            << std::endl;
  for (const auto& p : smt2->d_operatorKindMap)
  {
    std::cout << "  " << p.first << std::endl;
  }
  std::cout << "d_indexedOpKindMap symbols: " << smt2->d_indexedOpKindMap.size()
            << std::endl;
  for (const auto& p : smt2->d_indexedOpKindMap)
  {
    std::cout << "  " << p.first << std::endl;
  }
}
}  // namespace test
}  // namespace cvc5::internal
