/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for null.
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__NULLABLES__NULL_H
#define CVC5__THEORY__NULLABLES__NULL_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

class TypeNode;

class Null
{
 public:
  /**
   * Constructs an Null constant of the specified type. Note that the argument
   * is the type of the Nullable itself, NOT the type of the element.
   */
  Null(const TypeNode& bagType);
  ~Null();
  Null(const Null& other);
  Null& operator=(const Null& other);

  const TypeNode& getType() const;
  bool operator==(const Null& es) const;
  bool operator!=(const Null& es) const;
  bool operator<(const Null& es) const;
  bool operator<=(const Null& es) const;
  bool operator>(const Null& es) const;
  bool operator>=(const Null& es) const;

 private:
  Null();

  /** the type of the empty bag itself (not the type of the elements)*/
  std::unique_ptr<TypeNode> d_type;
}; /* class Null */

std::ostream& operator<<(std::ostream& out, const Null& es);

struct NullHashFunction
{
  size_t operator()(const Null& es) const;
}; /* struct NullHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__NULL_H */
