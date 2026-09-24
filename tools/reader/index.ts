// @bendlib/reader public API: version-matched bend.ts source, load, decls, show.
export { bendSource, installedVersion, declaredVersion, importBend, SourceError, type BendSource, type SourceOptions } from "./src/source.ts";
export {
  load, decls, show, blankImports, BendReadError,
  type Loaded, type LoadOptions, type Decl, type Binder, type Statement, type Kind, type Quant, type Origin, type Scope, type SourceFile,
} from "./src/reader.ts";
