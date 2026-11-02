/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference information utility.
 */

#include "theory/bags/rewrites.h"

#include <iostream>

namespace cvc5::internal {
namespace theory {
namespace bags {

const char* toString(Rewrite r)
{
  switch (r)
  {
    case Rewrite::NONE: return "NONE";
    case Rewrite::AGGREGATE_CONST: return "AGGREGATE_CONST";
    case Rewrite::BAG_MAKE_COUNT_NEGATIVE: return "BAG_MAKE_COUNT_NEGATIVE";
    case Rewrite::CARD_DISJOINT: return "CARD_DISJOINT";
    case Rewrite::CARD_BAG_MAKE: return "CARD_BAG_MAKE";
    case Rewrite::CHOOSE_BAG_MAKE: return "CHOOSE_BAG_MAKE";
    case Rewrite::CONSTANT_EVALUATION: return "CONSTANT_EVALUATION";
    case Rewrite::COUNT_EMPTY: return "COUNT_EMPTY";
    case Rewrite::COUNT_BAG_MAKE: return "COUNT_BAG_MAKE";
    case Rewrite::SETOF_BAG_MAKE: return "SETOF_BAG_MAKE";
    case Rewrite::EQ_CONST_FALSE: return "EQ_CONST_FALSE";
    case Rewrite::EQ_REFL: return "EQ_REFL";
    case Rewrite::EQ_SYM: return "EQ_SYM";
    case Rewrite::FILTER_CONST: return "FILTER_CONST";
    case Rewrite::FILTER_BAG_MAKE: return "FILTER_BAG_MAKE";
    case Rewrite::FILTER_UNION_DISJOINT: return "FILTER_UNION_DISJOINT";
    case Rewrite::FILTER_FILTER: return "FILTER_FILTER";
    case Rewrite::FILTER_MAP: return "FILTER_MAP";
    case Rewrite::FILTER_SETOF: return "FILTER_SETOF";
    case Rewrite::MAP_MAP: return "MAP_MAP";
    case Rewrite::PRODUCT_MAP_LEFT: return "PRODUCT_MAP_LEFT";
    case Rewrite::PRODUCT_MAP_RIGHT: return "PRODUCT_MAP_RIGHT";
    case Rewrite::PRODUCT_FILTER_LEFT: return "PRODUCT_FILTER_LEFT";
    case Rewrite::PRODUCT_FILTER_RIGHT: return "PRODUCT_FILTER_RIGHT";
    case Rewrite::PRODUCT_UNION_DISJOINT: return "PRODUCT_UNION_DISJOINT";
    case Rewrite::PRODUCT_ASSOC: return "PRODUCT_ASSOC";
    case Rewrite::PRODUCT_SWAP: return "PRODUCT_SWAP";
    case Rewrite::SETOF_SETOF: return "SETOF_SETOF";
    case Rewrite::EQ_EMPTY_ARG: return "EQ_EMPTY_ARG";
    case Rewrite::AGGREGATE_MAP: return "AGGREGATE_MAP";
    case Rewrite::FILTER_TRUE: return "FILTER_TRUE";
    case Rewrite::FILTER_FALSE: return "FILTER_FALSE";
    case Rewrite::FILTER_SORT_CONJUNCTS: return "FILTER_SORT_CONJUNCTS";
    case Rewrite::CANONICAL_VARIABLE: return "CANONICAL_VARIABLE";
    case Rewrite::AGGREGATE_SORT_OUTPUT: return "AGGREGATE_SORT_OUTPUT";
    case Rewrite::AGGREGATE_NO_KEYS: return "AGGREGATE_NO_KEYS";
    case Rewrite::FOLD_TUPLE: return "FOLD_TUPLE";
    case Rewrite::PRODUCT_BAG_MAKE: return "PRODUCT_BAG_MAKE";
    case Rewrite::SETOF_MAP_CONSTANT: return "SETOF_MAP_CONSTANT";
    case Rewrite::FILTER_SPLIT_CLOSED: return "FILTER_SPLIT_CLOSED";
    case Rewrite::SEMI_JOIN: return "SEMI_JOIN";
    case Rewrite::EQ_EMPTY_FILTER_DECORRELATE:
      return "EQ_EMPTY_FILTER_DECORRELATE";
    case Rewrite::COUNT_MAP_FILTER_KEYS: return "COUNT_MAP_FILTER_KEYS";
    case Rewrite::AGGREGATE_DEAD_COLUMNS: return "AGGREGATE_DEAD_COLUMNS";
    case Rewrite::FOLD_CONSTANT_STEP: return "FOLD_CONSTANT_STEP";
    case Rewrite::MAP_FIXED_COLUMNS: return "MAP_FIXED_COLUMNS";
    case Rewrite::MAP_IDENTITY_ON_FILTER: return "MAP_IDENTITY_ON_FILTER";
    case Rewrite::SETOF_PROJECTION_SORT: return "SETOF_PROJECTION_SORT";
    case Rewrite::AGGREGATE_UNION_OF_MAPS: return "AGGREGATE_UNION_OF_MAPS";
    case Rewrite::AGGREGATE_COLLAPSE: return "AGGREGATE_COLLAPSE";
    case Rewrite::SETOF_ABSORB: return "SETOF_ABSORB";
    case Rewrite::FILTER_KNOWN_MEMBERSHIP: return "FILTER_KNOWN_MEMBERSHIP";
    case Rewrite::FILTER_DE_MORGAN: return "FILTER_DE_MORGAN";
    case Rewrite::COUNT_MAP_DUPLICATE_COLUMNS:
      return "COUNT_MAP_DUPLICATE_COLUMNS";
    case Rewrite::SETOF_OF_SET: return "SETOF_OF_SET";
    case Rewrite::COUNT_MAP_CONST_PROBE: return "COUNT_MAP_CONST_PROBE";
    case Rewrite::AGGREGATE_KEYED: return "AGGREGATE_KEYED";
    case Rewrite::NOT_NULL_COLUMNS: return "NOT_NULL_COLUMNS";
    case Rewrite::AGGREGATE_INTEGER_SUM: return "AGGREGATE_INTEGER_SUM";
    case Rewrite::FILTER_NULLABLE_TRUTH: return "FILTER_NULLABLE_TRUTH";
    case Rewrite::AGGREGATE_ROLLUP: return "AGGREGATE_ROLLUP";
    case Rewrite::AGGREGATE_SETOF_IDEMPOTENT:
      return "AGGREGATE_SETOF_IDEMPOTENT";
    case Rewrite::AGGREGATE_JOIN_MERGE: return "AGGREGATE_JOIN_MERGE";
    case Rewrite::AGGREGATE_UNION_SPLIT: return "AGGREGATE_UNION_SPLIT";
    case Rewrite::AGGREGATE_GROUP_KEYS: return "AGGREGATE_GROUP_KEYS";
    case Rewrite::MAP_EQUAL_COLUMNS: return "MAP_EQUAL_COLUMNS";
    case Rewrite::FOLD_MAP: return "FOLD_MAP";
    case Rewrite::SETOF_UNION_SAME: return "SETOF_UNION_SAME";
    case Rewrite::AGGREGATE_UNION_DISJOINT_KEYS:
      return "AGGREGATE_UNION_DISJOINT_KEYS";
    case Rewrite::FILTER_JOIN_TRANSITIVE: return "FILTER_JOIN_TRANSITIVE";
    case Rewrite::PRODUCT_AGGREGATE_DEAD_COLUMN:
      return "PRODUCT_AGGREGATE_DEAD_COLUMN";
    case Rewrite::AGGREGATE_DUPLICATE_COLUMN:
      return "AGGREGATE_DUPLICATE_COLUMN";
    case Rewrite::MAP_IDENTITY: return "MAP_IDENTITY";
    case Rewrite::FILTER_IMPLIED_COUNTER: return "FILTER_IMPLIED_COUNTER";
    case Rewrite::FILTER_CONFLICTING_CONSTANTS:
      return "FILTER_CONFLICTING_CONSTANTS";
    case Rewrite::PROJECT_TO_MAP: return "PROJECT_TO_MAP";
    case Rewrite::ALL_EMPTY: return "ALL_EMPTY";
    case Rewrite::ALL_BAG_MAKE: return "ALL_BAG_MAKE";
    case Rewrite::ALL_UNION_DISJOINT: return "ALL_UNION_DISJOINT";
    case Rewrite::ALL_FILTER: return "ALL_FILTER";
    case Rewrite::SOME_EMPTY: return "SOME_EMPTY";
    case Rewrite::SOME_BAG_MAKE: return "SOME_BAG_MAKE";
    case Rewrite::SOME_UNION_DISJOINT: return "SOME_UNION_DISJOINT";
    case Rewrite::SOME_FILTER: return "SOME_FILTER";
    case Rewrite::FROM_SINGLETON: return "FROM_SINGLETON";
    case Rewrite::FOLD_BAG: return "FOLD_BAG";
    case Rewrite::FOLD_CONST: return "FOLD_CONST";
    case Rewrite::FOLD_UNION_DISJOINT: return "FOLD_UNION_DISJOINT";
    case Rewrite::IDENTICAL_NODES: return "IDENTICAL_NODES";
    case Rewrite::INTERSECTION_EMPTY_LEFT: return "INTERSECTION_EMPTY_LEFT";
    case Rewrite::INTERSECTION_EMPTY_RIGHT: return "INTERSECTION_EMPTY_RIGHT";
    case Rewrite::INTERSECTION_SAME: return "INTERSECTION_SAME";
    case Rewrite::INTERSECTION_SHARED_LEFT: return "INTERSECTION_SHARED_LEFT";
    case Rewrite::INTERSECTION_SHARED_RIGHT: return "INTERSECTION_SHARED_RIGHT";
    case Rewrite::IS_SINGLETON_BAG_MAKE: return "IS_SINGLETON_BAG_MAKE";
    case Rewrite::MAP_CONST: return "MAP_CONST";
    case Rewrite::MAP_BAG_MAKE: return "MAP_BAG_MAKE";
    case Rewrite::MAP_UNION_DISJOINT: return "MAP_UNION_DISJOINT";
    case Rewrite::MEMBER: return "MEMBER";
    case Rewrite::PARTITION_CONST: return "PARTITION_CONST";
    case Rewrite::PRODUCT_EMPTY: return "PRODUCT_EMPTY";
    case Rewrite::REMOVE_FROM_UNION: return "REMOVE_FROM_UNION";
    case Rewrite::REMOVE_MIN: return "REMOVE_MIN";
    case Rewrite::REMOVE_RETURN_LEFT: return "REMOVE_RETURN_LEFT";
    case Rewrite::REMOVE_SAME: return "REMOVE_SAME";
    case Rewrite::SUB_BAG: return "SUB_BAG";
    case Rewrite::SUBTRACT_DISJOINT_SHARED_LEFT:
      return "SUBTRACT_DISJOINT_SHARED_LEFT";
    case Rewrite::SUBTRACT_DISJOINT_SHARED_RIGHT:
      return "SUBTRACT_DISJOINT_SHARED_RIGHT";
    case Rewrite::SUBTRACT_FROM_UNION: return "SUBTRACT_FROM_UNION";
    case Rewrite::SUBTRACT_MIN: return "SUBTRACT_MIN";
    case Rewrite::SUBTRACT_RETURN_LEFT: return "SUBTRACT_RETURN_LEFT";
    case Rewrite::SUBTRACT_SAME: return "SUBTRACT_SAME";
    case Rewrite::UNION_DISJOINT_EMPTY_LEFT: return "UNION_DISJOINT_EMPTY_LEFT";
    case Rewrite::TO_SINGLETON: return "TO_SINGLETON";
    case Rewrite::UNION_DISJOINT_EMPTY_RIGHT:
      return "UNION_DISJOINT_EMPTY_RIGHT";
    case Rewrite::UNION_DISJOINT_MAX_MIN: return "UNION_DISJOINT_MAX_MIN";
    case Rewrite::UNION_MAX_EMPTY: return "UNION_MAX_EMPTY";
    case Rewrite::UNION_MAX_SAME_OR_EMPTY: return "UNION_MAX_SAME_OR_EMPTY";
    case Rewrite::UNION_MAX_UNION_LEFT: return "UNION_MAX_UNION_LEFT";
    case Rewrite::UNION_MAX_UNION_RIGHT: return "UNION_MAX_UNION_RIGHT";

    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Rewrite r)
{
  out << toString(r);
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
