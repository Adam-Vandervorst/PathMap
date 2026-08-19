# Overview

# Concepts and Basic Usage

- [PathMap Intro](./1.00.00_intro.md)
    - [Basic Structure](./1.00.01_basics.md)
- [Algebraic Operations](./1.01.00_algebraic_ops.md)
    - [Traits and Values](./1.01.01_algebraic_traits.md)
- [Zippers](./1.02.00_zippers.md)
    - [Base Trait](./1.02.01_zipper_trait.md)
    - [Value Access](./1.02.02_zipper_values.md)
    - [Paths and Absolute Paths](1.02.03_zipper_paths.md)
    - [Focus Moving](1.02.04_zipper_moving.md)
    - [Iteration](./1.02.05_zipper_iter.md)
    - [Modifying the Trie](./1.02.06_zipper_writing.md)
    - [Algebra on Subtries](./1.02.07_zipper_algebra.md)
- [Concurrent Zippers](./1.03.00_multi_zipper.md)
    - [Multi-threading](./1.03.01_multithreading.md)
- [Abstract Zippers and Virtual Tries](./1.04.00_abstract_zippers.md)
- [Morphisms](./1.05.00_morphisms.md)
    - [Catamorphism](./1.05.01_catamorphism.md)
    - [Anamorphism](./1.05.02_anamorphism.md)
- [Serialization and Deserialization](./1.06.00_serialize_deserilize.md)

# Building a Database on Pathmap

- [Database Management](./2.00.00_database_intro.md)
    - [Concurrency and Multi-threading](./2.00.01_concurrency.md)
- [Encoding Data in Paths](./2.01.00_encoding_overview.md)
- [Primitive Representations](./2.02.00_primitive_representations.md)
    - [Integers](./2.02.01_integer_encoding.md)
    - [Floating Point Numbers](./2.02.02_float_encoding.md)
    - [Spatial Points (2D, 3D, etc.)](./2.02.03_point_encoding.md)
    - [Strings and Symbols](./2.02.04_symbol_encoding.md)
    - [Partial and Fuzzy String Search](./2.02.05_fuzzy_search_encoding.md)

# Examples

GOAT: OEIS
GOAT: Aunt Knowledge Graph
GOAT: Multi-Threaded Map-Reduce

# Discussions, Future Work, and Unresolved Issues

- [Root Values in Maps & Zippers](./A.0001_map_root_values.md)
- [Smart Ptr & Resource Mgmt Improvement](./A.0002_smart_ptr_upgrade.md)
- [Lattice / Policy API Improvment](./A.0003_policy_API.md)
- [Scouting WriteZipper](./A.0004_scouting_write_zipper.md)
- [Cached Cata and Paths](./A.0005_cached_cata_and_path_visibility.md)


{{#include api_links.md}}
