import { readFile, writeFile } from "node:fs/promises";
import { createRequire } from "node:module";
import path from "node:path";
import { fileURLToPath } from "node:url";

const localRequire = createRequire(import.meta.url);
const runtimeModules = process.env.FORMALIZATION_NODE_MODULES;
const packageRequire = runtimeModules
  ? createRequire(path.join(runtimeModules, "package.json"))
  : localRequire;
const { instance } = packageRequire("@viz-js/viz");
const sharp = packageRequire("sharp");

const scriptDirectory = path.dirname(fileURLToPath(import.meta.url));
const repositoryRoot = path.resolve(scriptDirectory, "..");
const graphDirectory = path.join(repositoryRoot, "paper");
const dotPath = path.join(graphDirectory, "dependency-graph.dot");
const svgPath = path.join(graphDirectory, "dependency-graph.svg");
const pngPath = path.join(graphDirectory, "dependency-graph.png");

const dot = await readFile(dotPath, "utf8");
const viz = await instance();
const svg = viz.renderString(dot, { format: "svg", engine: "dot" });

await writeFile(svgPath, svg, "utf8");
await sharp(Buffer.from(svg)).png({ quality: 95 }).toFile(pngPath);

process.stdout.write(`Rendered ${svgPath}\nRendered ${pngPath}\n`);
