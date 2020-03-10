/*********************                                                        */
/*! \file emptybag.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Kshitij Bansal, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#pragma once

#include <iosfwd>

namespace CVC4 {
// messy; Expr needs EmptyBag (because it's the payload of a
// CONSTANT-kinded expression), EmptyBag needs BagType, and
// BagType needs Expr. Using a forward declaration here in
// order to break the build cycle.
// Uses of BagType need to be as an incomplete type throughout
// this header.
class BagType;
}  // namespace CVC4

namespace CVC4 {
class CVC4_PUBLIC EmptyBag
{
 public:
  /**
   * Constructs an emptybag of the specified type. Note that the argument
   * is the type of the bag itself, NOT the type of the elements.
   */
  EmptyBag(const BagType& bagType);
  ~EmptyBag();
  EmptyBag(const EmptyBag& other);
  EmptyBag& operator=(const EmptyBag& other);

  const BagType& getType() const;
  bool isBag() const;
  bool operator==(const EmptyBag& es) const;
  bool operator!=(const EmptyBag& es) const;
  bool operator<(const EmptyBag& es) const;
  bool operator<=(const EmptyBag& es) const;
  bool operator>(const EmptyBag& es) const;
  bool operator>=(const EmptyBag& es) const;

 private:
  /** Pointer to the BagType node. This is never NULL. */
  BagType* d_type;

  EmptyBag();

}; /* class EmptyBag */

std::ostream& operator<<(std::ostream& out, const EmptyBag& es) CVC4_PUBLIC;

struct CVC4_PUBLIC EmptyBagHashFunction
{
  size_t operator()(const EmptyBag& es) const;
}; /* struct EmptyBagHashFunction */

}  // namespace CVC4
