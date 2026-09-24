// license: what a package's LICENSE files say. `bend guide` (2.0.27): --publish takes
// every file named exactly LICENSE, and a package without one is MIT-0.

export type License = { id: string; from: string | null };

const KNOWN: [RegExp, string][] = [
  [/MIT No Attribution/i, "MIT-0"],
  [/Permission is hereby granted, free of charge/i, "MIT"],
  [/Apache License,?\s+Version 2\.0/i, "Apache-2.0"],
  [/GNU AFFERO GENERAL PUBLIC LICENSE\s+Version 3/i, "AGPL-3.0"],
  [/GNU LESSER GENERAL PUBLIC LICENSE\s+Version 3/i, "LGPL-3.0"],
  [/GNU GENERAL PUBLIC LICENSE\s+Version 3/i, "GPL-3.0"],
  [/GNU GENERAL PUBLIC LICENSE\s+Version 2/i, "GPL-2.0"],
  [/Mozilla Public License,?\s+(Version|v\.?)\s*2\.0/i, "MPL-2.0"],
  [/This is free and unencumbered software released into the public domain/i, "Unlicense"],
  [/Redistribution and use in source and binary forms/i, "BSD"],
  [/Permission to use, copy, modify, and\/or distribute this software for any purpose/i, "ISC or 0BSD"],
];

export function identify(text: string): string {
  const spdx = text.match(/SPDX-License-Identifier:\s*([A-Za-z0-9.+\- ()]+?)\s*$/m);
  if (spdx) return spdx[1];
  for (const [re, id] of KNOWN) if (re.test(text)) return id;
  return "custom (see LICENSE)";
}

/** One entry per LICENSE file (by path); MIT-0 when the package has none. */
export function licenses(files: { path: string; text: () => string }[]): License[] {
  const found = files.filter((f) => f.path === "LICENSE" || f.path.endsWith("/LICENSE"));
  if (found.length === 0) return [{ id: "MIT-0", from: null }];
  return found.map((f) => ({ id: identify(f.text()), from: f.path }));
}
