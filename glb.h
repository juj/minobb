// glb.h
//
// Minimal glTF 2.0 reader that extracts world space vertex positions from
// .glb and .gltf files. Depends only on the C++ standard library.

#pragma once

#include <string>
#include <vector>

// Reads the vertex positions of the default scene of a glTF 2.0 file: a
// binary .glb, or a .gltf with its buffers embedded as data URIs or stored in
// external files next to it.
//
// The POSITION attribute of every mesh primitive that the scene's node
// hierarchy instantiates is transformed to world space and appended to `pts`
// as packed xyz float triples (a mesh used by several nodes contributes once
// per node). Skinning, morph targets and animations are not applied, i.e. the
// meshes stay in their bind pose. Sparse and compressed (Draco, meshopt)
// position data is not supported.
//
// Returns false on failure, with a description of the problem in `error`.
bool glb_read_positions(const char *path, std::vector<float> &pts, std::string &error);
