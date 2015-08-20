/* Copyright 2015 Johannes Kloos, MPI-SWS.
 *
 * Based on a template under the following license:
 *
 * Copyright 2014 Samsung Information Systems America, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Author: Koushik Sen
// Author: Johannes Kloos
// do not remove the following comment
// JALANGI DO NOT INSTRUMENT
// In the following callbacks one can choose to not return anything.
// If all of the callbacks return nothing, we get a passive analysis where the
// concrete execution happens unmodified and callbacks are used to observe the execution.
// Once can choose to return suitable objects with specified fields in some callbacks
// to modify the behavior of the concrete execution.  For example, one could set the skip
// field of an object returned from putFieldPre to true to skip the actual putField operation.
// Similarly, one could set the result field of the object returned from a write callback
// to modify the value that is actually written to a variable. The result field of the object
// returned from a conditional callback can be suitably set to change the control-flow of the
// program execution.  In functionExit and scriptExit,
// one can set the isBacktrack field of the returned object to true to reexecute the body of
// the function from the beginning.  This in conjunction with the ability to change the
// control-flow of a program enables us to explore the different paths of a function in
// symbolic execution.
(function(sandbox) {
	function MyAnalysis(global) {
		var objects = new WeakMap();
		var functions = new WeakMap();
		var objdesc = [];
		var funcdesc = [];
		var trace = [];
		var globals = {};
		// HACK There seem to be two schools of thought on how to handle
		// global variables: They may be represented as entries in the global
		// object,
		// or as bindings in the global environment without any connection to
		// the
		// global object. We assume that each interpreter uses only one way to
		// handle globals, but we need to know which.
		var globals_are_properties = global.J$ === J$;

		function materialize_object(name, props_obj, props_proto) {
			eval("var obj = " + name);
			if (obj !== undefined) {
				var desc = {
					id : objid(obj)
				};
				var obj_data = {};
				materialize_properties(obj_data, obj, props_obj);
				desc.obj_data = obj_data;
				var proto_data = {};
				if (obj.prototype != undefined) {
					materialize_properties(proto_data, obj.prototype, props_proto);
				}
				desc.proto_data = proto_data;
				globals[name] = desc;
			}
		}
		function materialize_properties(desc, base, offsets) {
			for (i = 0; i < offsets.length; i++) {
				materialize_property(desc, base, offsets[i]);
			}
		}
		function materialize_property(desc, base, offset) {
			if (base.hasOwnProperty(offset)) {
				var propdesc = Object.getOwnPropertyDescriptor(base, offset);
				if (propdesc == undefined)
					propdesc = {};
				if (propdesc["get"]) {
					propdesc.get = objid(propdesc.get)
				}
				if (propdesc["set"]) {
					propdesc.set = objid(propdesc.set)
				}
				propdesc.value = objid(base[offset]);
				desc[offset] = propdesc;
			}
		}
		// CAVE: This has to come first. We use the fact that the
		// global object has index 0 in the oracle.
		globals.global = {
			id : objid(global),
			obj_data: {}
		};
		materialize_properties(globals.global.obj_data, global,
				["Infinity", "NaN", "undefined", "eval", "isFinite", "isNaN",
				 "parseFloat", "parseInt", "decodeURI", "decodeURIComponent",
				 "encodeURI", "encodeURIComponent"])
		materialize_object("Object", [ "assign", "create", "defineProperties",
				"defineProperty", "freeze", "getOwnPropertyDescriptor",
				"getOwnPropertyNames", "getOwnPropertySymbols",
				"getPrototypeOf", "is", "isExtensible", "isFrozen", "isSealed",
				"keys", "preventExtensions", "prototype", "seal",
				"setPrototypeOf" ], [ "constructor", "hasOwnProperty",
				"isPrototypeOf", "propertyIsEnumerable", "toLocaleString",
				"toString", "valueOf" ]);
		materialize_object("Function", [ "length", "prototype" ], [ "apply",
				"bind", "call", "constructor", "toString" ]);
		materialize_object("Boolean", [ "length", "prototype" ], [
				"constructor", "toString", "valueOf" ]);
		materialize_object("Symbol", [ "for", "hasInstance",
				"isConcatSpreadable", "iterator", "keyFor", "match",
				"prototype", "replace", "search", "species", "split",
				"toPrimitive", "toStringTag", "unscopables" ], [ "constructor",
				"toString", "valueOf" ]);
		materialize_object("Error", [ "prototype" ], [ "constructor",
				"message", "name", "toString" ]);
		materialize_object("Number", [ "EPSILON", "isFinite", "isInteger",
				"isNaN", "isSafeInteger", "MAX_SAFE_INTEGER", "MAX_VALUE",
				"MIN_SAFE_INTEGER", "MIN_VALUE", "NAN", "NEGATIVE_INFINITY",
				"parseFloat", "parseInt", "POSITIVE_INFINITY", "prototype" ], [
				"constructor", "toExponential", "toFixed", "toLocaleString",
				"toPrecision", "toString", "valueOf" ])
		materialize_object("Math", [ "E", "LN10", "LN2", "LOG10E", "LOG2E",
				"PI", "SQRT1_2", "SQRT2", "abs", "acos", "acosh", "asin",
				"asinh", "atan", "atanh", "atan2", "cbrt", "ceil", "clz32",
				"cos", "cosh", "exp", "expm1", "floor", "fround", "hypot",
				"imul", "log", "log1p", "log10", "log2", "max", "min", "pow",
				"random", "round", "sign", "sin", "sinh", "sqrt", "tan",
				"tanh", "trunc" ], [])
		materialize_object("Date", [ "now", "parse", "prototype", "UTC" ], [
				"constructor", "getDate", "getDay", "getFullYear", "getHours",
				"getMilliseconds", "getMinutes", "getMonth", "getSeconds",
				"getTime", "getTimezoneOffset", "getUTCDate", "getUTCDay",
				"getUTCFullYear", "getUTCHours", "getUTCMilliseconds",
				"getUTCMinutes", "getUTCMonth", "getUTCSeconds", "setDate",
				"setFullYear", "setHours", "setMilliseconds", "setMinutes",
				"setMonth", "setSeconds", "setTime", "setUTCDate",
				"setUTCFullYEar", "setUTCHours", "setUTCMilliseconds",
				"setUTCMinutes", "setUTCMonth", "setUTCMinutes",
				"setUTCSeconds", "toDateString", "toISOString", "toJSON",
				"toLocateDateString", "toLocaleString", "toLocaleTimeString",
				"toString", "toTimeString", "toUTCString", "valueOf" ]);
		materialize_object("String", [ "fromCharCode", "fromCodePoint",
				"prototype", "raw" ], [ "charAt", "charCodeAt", "codePointAt",
				"concat", "constructor", "endsWith", "includes", "indexOf",
				"lastIndexOf", "localeCompare", "match", "normalize", "repeat",
				"replace", "search", "slice", "split", "startWith",
				"substring", "toLocaleLowerCase", "toLocaleUpperCase",
				"toLowerCase", "toString", "toUpperCase", "trim", "valueOf" ]);
		materialize_object("RegExp", [ "prototype", "getRegExp" ], [
				"constructor", "exec", "flags", "global", "ignoreCase",
				"multiline", "source", "replace", "split", "search", "sticky",
				"test", "toString", "unicode" ]);
		materialize_object("Array", [ "from", "isArray", "of", "prototype" ], [
				"concat", "isConcatSpreadable", "constructor", "copyWithin",
				"entries", "every", "fill", "filter", "find", "findIndex",
				"forEach", "indexOf", "join", "keys", "lastIndexOf", "map",
				"pop", "push", "reduce", "reduceRight", "reverse", "shift",
				"slice", "some", "sort", "splice", "toLocaleString",
				"toString", "unshift", "values", "iterator" ]);
		/*
		 * for (obj in ["Int8Array", "Uint8Array", "Uint8ClampedArray",
		 * "Int16Array", "Uint16Array", "Int32Array", "Uint32Array",
		 * "Float32Array", "Float64Array"]) { materialize_object(obj, ["from",
		 * "of", "prototype", "species", "BYTES_PER_ELEMENT" ], ["buffer",
		 * "byteLength", "byteOffset", "constructor", "copyWithin", "entries",
		 * "every", "fill", "filter", "find", "findIndex", "forEach", "indexOf",
		 * "join", "keys", "lastIndexOf", "length", "map", "reduce",
		 * "reduceRight", "reverse", "set", "slice", "some", "sort", "subarray",
		 * "toLocaleString", "toString", "values", "iterator", "toStringTag"]); }
		 */
		/*
		materialize_object("Map", [ "prototype", "species", "length" ], [
				"clear", "constructor", "delete", "entries", "forEach", "get",
				"has", "keys", "set", "size", "values", "iterator",
				"toStringTag" ]);
		materialize_object("Set", [ "prototype", "species" ], [ "add", "clear",
				"constructor", "delete", "entries", "forEach", "has", "keys",
				"size", "values", "iterator", "toStringTag" ]);
		materialize_object("WeakMap", [ "prototype", "length" ], [
				"constructor", "delete", "get", "has", "set", "toStringTag" ]);
		materialize_object("WeakSet", [ "prototype", "length" ], [ "add",
				"constructor", "delete", "has", "toStringTag" ]);
		materialize_object("ArrayBuffer", [ "length", "isView", "prototype",
				"species" ], [ "byteLength", "constructor", "slice",
				"toStringTag" ]);
		materialize_object("DataView", [ "length", "prototype" ], [ "buffer",
				"byteLength", "byteOffset", "constructor", "getFloat32",
				"getFloat64", "getInt8", "getInt16", "getInt32", "getUint8",
				"getUint16", "getUint32", "setFloat32", "setFloat64",
				"setInt8", "setInt16", "setInt32", "setUint8", "setUint16",
				"setUint32", "toStringTag" ]);
				*/
		materialize_object("JSON", [ "parse", "stringify", "toStringTag" ], []);

		// recurse along prototype chain
		function get_all_properties(obj, props) {
			var props_here = Object.getOwnPropertyNames(obj);
			props.concat(props_here);
			var proto = Object.getPrototypeOf(obj);
			if (proto != null) {
				get_all_properties(proto, props);
			}
		}
		function describeobj(obj) {
			// We know that obj is of type object (or something very similar,
			// like function)
			var desc = {};
			var all_properties = new Array();
			get_all_properties(obj, all_properties);
			for (var i = 0; i < all_properties.length; i++) {
				var prop = all_properties[i];
				var propdesc = Object.getOwnPropertyDescriptor(obj, prop);
				if (propdesc == undefined)
					propdesc = {};
				if (propdesc["get"]) {
					propdesc.get = objid(propdesc.get)
				}
				if (propdesc["set"]) {
					propdesc.set = objid(propdesc.set)
				}
				propdesc.value = objid(obj[prop]);
				desc[prop] = propdesc;
			}
			return desc;
		}

		function funcid(obj) {
			// We know that obj is of type function
			if (functions.has(obj)) {
				return functions.get(obj);
			} else {
				var id = funcdesc.length;
				functions.set(obj, id);
				funcdesc.push({
					instrumented : obj.toString(),
					obj : objid(obj)
				});
				return id;
			}
		}

		function objid(obj) {
			switch (typeof obj) {
			case "undefined":
				return {
					type : "undefined"
				};
			case "boolean":
			case "number":
			case "string":
			case "symbol":
				return {
					type : typeof obj,
					val : obj.toString()
				}
			case "function":
				if (objects.has(obj)) {
					return {
						type : "function",
						id : objects.get(obj),
						funid : funcid(obj)
					}
				} else {
					var id = objdesc.length;
					objects.set(obj, id);
					objdesc.push(describeobj(obj));
					return {
						type : "function",
						id : id,
						funid : funcid(obj)
					}
				}
			case "object":
				if (obj === null) {
					return {
						type : "null"
					}
				} else if (objects.has(obj)) {
					return {
						type : "object",
						id : objects.get(obj)
					}
				} else {
					var id = objdesc.length;
					objects.set(obj, id);
					objdesc.push(describeobj(obj));
					return {
						type : "object",
						id : id
					}
				}
			default:
				if (objects.has(obj)) {
					return {
						type : typeof obj,
						id : objects.get(obj)
					}
				} else {
					var id = objdesc.length;
					objects.set(obj, id);
					objdesc.push({
						external : true
					});
					return {
						type : typeof obj,
						id : id
					}
				}
			}
		}

		this.invokeFunPre = function(iid, f, base, args, isConstructor,
				isMethod) {
			trace.push({
				step : "funpre",
				iid : iid,
				f : objid(f),
				base : objid(base),
				args : objid(args),
				isConstructor : isConstructor,
				isMethod : isMethod
			});
		};

		this.invokeFun = function(iid, f, base, args, result, isConstructor,
				isMethod) {
			trace.push({
				step : "funpost",
				iid : iid,
				f : objid(f),
				base : objid(base),
				args : objid(args),
				isConstructor : isConstructor,
				isMethod : isMethod,
				result : objid(result)
			});
		};

		this.literal = function(iid, val, hasGetterSetter) {
			// Special handling for function literals.
			var id = objid(val);
			trace.push({
				step : "literal",
				iid : iid,
				val : id,
				hasGetterSetter : hasGetterSetter
			});
			if (typeof val == "function") {
				var data = J$.smap[J$.sid];
				var pos = data[iid].map(function(x) {
					return x - 1
				});
				var lines = data.code.split("\n");
				var text;
				if (pos[0] == pos[2]) {
					text = lines[pos[0]].substr(pos[1], pos[3] - pos[1]);
				} else {
					text = lines[pos[0]].substr(pos[1]);
					for (var i = pos[0] + 1; i < pos[2]; i++) {
						text += "\n" + lines[i];
					}
					text += "\n" + lines[pos[2]].substr(0, pos[3]);
				}
				funcdesc[id.funid].uninstrumented = text;
			}
		};

		this.forinObject = function(iid, val) {
			trace.push({
				step : "forin",
				iid : iid,
				val : objid(val)
			});
		};

		this.declare = function(iid, name, val, isArgument, argumentIndex,
				isCatchParam) {
			trace.push({
				step : "declare",
				iid : iid,
				name : name,
				val : objid(val),
				isArgument : isArgument,
				argumentIndex : argumentIndex,
				isCatchParam : isCatchParam
			});
		};

		this.getFieldPre = function(iid, base, offset, isComputed, isOpAssign,
				isMethodCall) {
			trace.push({
				step : "getpre",
				iid : iid,
				base : objid(base),
				offset : offset.toString(),
				isComputed : isComputed,
				isOpAssign : isOpAssign,
				isMethodCall : isMethodCall
			});
		};

		this.getField = function(iid, base, offset, val, isComputed,
				isOpAssign, isMethodCall) {
			trace.push({
				step : "getpost",
				iid : iid,
				base : objid(base),
				offset : offset.toString(),
				val : objid(val),
				isComputed : isComputed,
				isOpAssign : isOpAssign,
				isMethodCall : isMethodCall
			});
		};

		this.putFieldPre = function(iid, base, offset, val, isComputed,
				isOpAssign) {
			trace.push({
				step : "putpre",
				iid : iid,
				base : objid(base),
				offset : offset.toString(),
				val : objid(val),
				isComputed : isComputed,
				isOpAssign : isOpAssign
			});
		};

		this.putField = function(iid, base, offset, val, isComputed, isOpAssign) {
			trace.push({
				step : "putpost",
				iid : iid,
				base : objid(base),
				offset : offset.toString(),
				val : objid(val),
				isComputed : isComputed,
				isOpAssign : isOpAssign
			});
		};

		this.read = function(iid, name, val, isGlobal, isScriptLocal) {
			trace.push({
				step : "read",
				iid : iid,
				name : name,
				val : objid(val),
				isGlobal : isGlobal,
				isScriptLocal : isScriptLocal
			});
		};

		this.write = function(iid, name, val, lhs, isGlobal, isScriptLocal) {
			trace.push({
				step : "write",
				iid : iid,
				name : name,
				val : objid(val),
				lhs : objid(lhs),
				isGlobal : isGlobal,
				isScriptLocal : isScriptLocal
			});
		};

		this._return = function(iid, val) {
			trace.push({
				step : "return",
				iid : iid,
				val : objid(val)
			});
		};

		this._throw = function(iid, val) {
			trace.push({
				step : "throw",
				iid : iid,
				val : objid(val)
			});
		};

		this.functionEnter = function(iid, f, dis, args) {
			trace.push({
				step : "funcenter",
				iid : iid,
				f : objid(f),
				"this" : objid(dis),
				args : objid(args)
			});
		};

		this.functionExit = function(iid, returnVal, wrappedExceptionVal) {
			trace.push({
				step : "funcexit",
				iid : iid,
				ret : objid(returnVal),
				exc : objid(wrappedExceptionVal)
			});
		};

		this.scriptEnter = function(iid, instrumentedFileName, originalFileName) {
			trace.push({
				step : "scriptenter"
			});
		};

		this.scriptExit = function(iid, wrappedExceptionVal) {
			if (wrappedExceptionVal === undefined) {
				trace.push({
					step : "scriptexit"
				});
			} else {
				trace.push({
					step : "scriptexc",
					exc : objid(wrappedExceptionVal)
				});
			}
		};

		this.binaryPre = function(iid, op, left, right, isOpAssign,
				isSwitchCaseComparison, isComputed) {
			trace.push({
				step : "binarypre",
				iid : iid,
				op : op,
				left : objid(left),
				right : objid(right),
				isOpAssign : isOpAssign,
				isSwitchComparison : isSwitchCaseComparison,
				isComputed : isComputed
			});
		};

		this.binary = function(iid, op, left, right, result, isOpAssign,
				isSwitchCaseComparison, isComputed) {
			trace.push({
				step : "binarypost",
				iid : iid,
				op : op,
				left : objid(left),
				right : objid(right),
				isOpAssign : isOpAssign,
				isSwitchComparison : isSwitchCaseComparison,
				isComputed : isComputed,
				result : objid(result)
			});
		};

		this.unaryPre = function(iid, op, left) {
			trace.push({
				step : "unarypre",
				iid : iid,
				op : op,
				left : objid(left)
			});
		};

		this.unary = function(iid, op, left, result) {
			trace.push({
				step : "unarypost",
				iid : iid,
				op : op,
				left : objid(left),
				result : objid(result)
			});
		};

		this.conditional = function(iid, result) {
			trace.push({
				step : "conditional",
				iid : iid,
				result : objid(result)
			});
		};

		this.endExpression = function(iid) {
			trace.push({
				step : "exprend",
				iid : iid
			});
		};

		this.endExecution = function() {
			console.log(JSON.stringify({
				func : funcdesc,
				obj : objdesc,
				trace : trace,
				globals : globals,
				globals_are_properties : globals_are_properties
			}))
		};

		this._with = function(iid, val) {
			trace.push({
				step : "with",
				iid : iid,
				val : val
			});
		};
	}
	sandbox.analysis = new MyAnalysis(this);
})(J$);
