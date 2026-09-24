// Package-list filter for index.html; bundled by build.ts into assets/site.js.

function filter() {
  const input = document.getElementById("filter") as HTMLInputElement | null;
  const rows = Array.from(document.querySelectorAll<HTMLTableRowElement>("#pkgs tbody tr"));
  const shown = document.getElementById("shown");
  if (input === null || shown === null) return;
  const apply = () => {
    const words = input.value.toLowerCase().split(/\s+/).filter(Boolean);
    let n = 0;
    for (const r of rows) {
      const s = r.dataset.s ?? "";
      const ok = words.every((w) => s.includes(w));
      r.hidden = !ok;
      if (ok) n++;
    }
    shown.textContent = words.length ? `${n} of ${rows.length} shown` : "";
  };
  input.addEventListener("input", apply);
  apply();
}

filter();
