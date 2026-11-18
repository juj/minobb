// web/calculator_api.js
//
// The JavaScript side of site/calculator.js: build_viewer.py appends this file
// to the code that Emscripten generates from web/calculator.cpp.
//
// calculator.js can be used in three ways:
//
// - As a Web Worker (this is what site/view.html does). Post it a message
//   { id, points, tolerance }, and it answers with { id, data } or, if the
//   calculation failed, with { id, error }.
// - As a script of a page (<script src="calculator.js">): call
//   MinobbCalculator.compute(points, tolerance), which returns a Promise of
//   the data.
// - As a Node.js module: require('./calculator.js').compute(points, tolerance).
//
// `points` is a Float32Array of packed xyz triples, and `tolerance` is that of
// minobb() (see minobb.h): how much larger than the minimum volume the box may
// be, as a fraction. It is 0.0015 if left out, and 0 gives the minimum box
// itself, which can take minutes on a finely tessellated ball.
//
// The data is an object like the JSON document that the command line tool
// minobb_glb prints (test/minobb_glb.cpp), with the same numbers:
//
//   {
//     vertices: 8,                       // The number of points.
//     tolerance: 0.0015,
//     timing: { hull_sec, obb_sec },
//     hull: { degenerate: false, vertices: [[x, y, z], ...], faces: [[i, j, k, ...], ...] },
//     aabb_vertices: { min, max, center, size, volume },   // The box of the points,
//     aabb_hull: { min, max, center, size, volume },       // and of the hull vertices.
//     obb: { degenerate: false, center, half_extents, size, axes: [[x, y, z] x 3], volume }
//   }
//
// (obb is { degenerate: true } if there was no finite point to compute a box of.)

var MinobbCalculator = (function () {
  'use strict';

  var DEFAULT_TOLERANCE = 0.0015; // That of minobb() in minobb.h.

  // The layout of the array that calculator_compute() returns: keep in sync
  // with the enum of web/calculator.cpp.
  var R_NUM_HULL_VERTICES = 0, R_NUM_HULL_FACES = 1, R_NUM_FACE_INTS = 2, R_HULL_DEGENERATE = 3,
      R_OBB_DEGENERATE = 4, R_HULL_SEC = 5, R_OBB_SEC = 6, R_AABB_VERTICES = 7, R_AABB_HULL = 20,
      R_OBB = 33, R_COUNT = 52;

  // A wasm memory that has grown never shrinks. A module that a large model
  // has grown past this size is dropped after the calculation, and the next
  // one starts with a new module.
  var KEEP_MODULE_BELOW_BYTES = 256 * 1024 * 1024;

  var modulePromise = null;

  // The numbers of the results are floats. Nine significant digits tell a
  // float apart from all the others, and that is how minobb_glb prints them
  // (%.9g): as a double, a float would print with eight digits of noise.
  function f32(x) { return +x.toPrecision(9); }
  function vec3(a, i) { return [f32(a[i]), f32(a[i + 1]), f32(a[i + 2])]; }
  function aabb(a, i) {
    return { min: vec3(a, i), max: vec3(a, i + 3), center: vec3(a, i + 6), size: vec3(a, i + 9), volume: f32(a[i + 12]) };
  }

  function run(m, points, tolerance) {
    var numPoints = points.length / 3;
    // (The memory of the module is at most 4 GB: a larger size would wrap around as a 32-bit number.)
    var input = points.byteLength < 0xFFFF0000 ? m._malloc(Math.max(points.byteLength, 4)) >>> 0 : 0;
    if (!input) throw new Error('out of memory: the model has too many vertices');
    var r;
    try {
      m.HEAPF32.set(points, input >>> 2);
      r = m._calculator_compute(input, numPoints, tolerance) >>> 0;
    } finally {
      m._free(input);
    }
    // (The views of the heap are taken after the calculation: they are replaced when the memory grows.)
    var R = m.HEAPF64.subarray(r >>> 3, (r >>> 3) + R_COUNT);
    var numVertices = R[R_NUM_HULL_VERTICES], numFaceInts = R[R_NUM_FACE_INTS];
    var v = m._calculator_hull_vertices() >>> 2, f = m._calculator_hull_faces() >>> 2;
    var V = m.HEAPF32.subarray(v, v + 3 * numVertices), F = m.HEAP32.subarray(f, f + numFaceInts);

    var vertices = new Array(numVertices), faces = [];
    for (var i = 0; i < numVertices; ++i) vertices[i] = vec3(V, 3 * i);
    for (var j = 0; j < numFaceInts; j += F[j] + 1) faces.push(Array.from(F.subarray(j + 1, j + 1 + F[j])));

    var o = R_OBB;
    return {
      vertices: numPoints,
      tolerance: tolerance,
      timing: { hull_sec: +R[R_HULL_SEC].toFixed(9), obb_sec: +R[R_OBB_SEC].toFixed(9) },
      hull: { degenerate: !!R[R_HULL_DEGENERATE], vertices: vertices, faces: faces },
      aabb_vertices: aabb(R, R_AABB_VERTICES),
      aabb_hull: aabb(R, R_AABB_HULL),
      obb: R[R_OBB_DEGENERATE] ? { degenerate: true } : {
        degenerate: false,
        center: vec3(R, o),
        half_extents: vec3(R, o + 3),
        size: vec3(R, o + 6),
        axes: [vec3(R, o + 9), vec3(R, o + 12), vec3(R, o + 15)],
        volume: f32(R[o + 18])
      }
    };
  }

  function compute(points, tolerance) {
    if (tolerance === undefined) tolerance = DEFAULT_TOLERANCE;
    if (!(points instanceof Float32Array) || points.length % 3 != 0)
      return Promise.reject(new TypeError('points must be a Float32Array of xyz triples'));
    if (typeof tolerance != 'number' || !(tolerance >= 0) || !isFinite(tolerance))
      return Promise.reject(new RangeError('tolerance must be a number that is not negative'));
    var promise = modulePromise || (modulePromise = createMinobbModule());
    return promise.then(function (m) {
      try {
        var data = run(m, points, tolerance);
      } catch (e) {
        // A module that has failed cannot be used again.
        if (modulePromise === promise) modulePromise = null;
        // (An allocation that fails inside the C++ code aborts the module, which says no more than "Aborted()".)
        if (typeof WebAssembly == 'object' && e instanceof WebAssembly.RuntimeError)
          throw new Error('out of memory, most likely: the model has too many vertices (' + e.message + ')');
        throw e;
      }
      if (m.HEAPU8.length > KEEP_MODULE_BELOW_BYTES && modulePromise === promise) modulePromise = null;
      return data;
    }, function (e) {
      if (modulePromise === promise) modulePromise = null;
      throw e;
    });
  }

  return { compute: compute, DEFAULT_TOLERANCE: DEFAULT_TOLERANCE };
})();

if (typeof WorkerGlobalScope != 'undefined' && self instanceof WorkerGlobalScope) {
  self.onmessage = function (e) {
    var id = e.data.id;
    MinobbCalculator.compute(e.data.points, e.data.tolerance).then(
      function (data) { self.postMessage({ id: id, data: data }); },
      function (error) { self.postMessage({ id: id, error: String((error && error.message) || error) }); });
  };
} else if (typeof module == 'object' && module.exports) {
  module.exports = MinobbCalculator;
}
