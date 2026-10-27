# UberSlicer

NW ubershader specialisation pipeline: option vector in, a specialised NVN/NVN2
`_bytecode.bin` + `_control.bin` out (spliced from the debug ubershader binary).
The bundling part is available at [HoianViewer](https://github.com/nvnprogram/HoianViewer).
Only tested on Splatoon 3 and Splatoon Raiders, other games may break(if they do work 
but you see artifacts, likely scheduling issue. If you were interested in getting it 
to work on another game that has debug ubershader bins and its broken, you can
contact me on discord @nvnprogram).

On my benchmarks, this should achieve approximately 1.1x the instructions count of a stock variation, and is roughly 1.2x slower than an equivalent stock variation.
(Which is obviously much better than an ubershader, which has at least 25x instrs)

## Build

```sh
./build.sh
```

Any C99 + C++17 gcc will do. The binary is `out/uberspec.exe` on Windows and
`out/uberspec` on Linux; the output is byte identical between the two.

## Run

```sh
./out/uberspec \
    --uber          <bytecode.bin> \
    --options-table <options.json> \
    --option-bank   <N> \
    --options-file  <options.txt> \
    --out <dir> [--name <basename>]
```

| argument | what it is | comes from |
|---|---|---|
| `--uber` | the debug ubershader program to specialise | bfsha |
| `--options-table` | which dword of the option buffer each option lands in | bfsha |
| `--option-bank` | the constant bank that buffer is bound to, per stage | bfsha |
| `--options-file` | the option vector, one `option=choice` per line | you |
| `--out` / `--name` | output directory and basename; writes `<name>_bytecode.bin` and `<name>_control.bin` | you, or the default below |

Stage is read out of the ubershader's own hader program header.  
`--uber-control` is optional; without it the `_control.bin` counterpart of the bytecode is used.

`--name` is optional. Left out, the basename is hash of the emitted code.

### Example

Some samples are provided from Splatoon 3 v11.3.0:

```sh
./out/uberspec \
    --uber          data/ubershader/370703aad8d5cd3c_bytecode.bin \
    --options-table data/options.json \
    --option-bank   6 \
    --options-file  data/sample_options.txt \
    --out ./sample --name sample_fragment

./out/uberspec \
    --uber          data/ubershader/92c6d352f13360ca_vertex_bytecode.bin \
    --options-table data/options.json \
    --option-bank   5 \
    --options-file  data/sample_options.txt \
    --out ./sample
```

| option vector | `gsys_weight` | fragment ubershader | vertex ubershader |
|---|---|---|---|
| `data/sample_options.txt` | 4 | `data/ubershader/370703aad8d5cd3c_bytecode.bin` (bank 6) | `data/ubershader/92c6d352f13360ca_vertex_bytecode.bin` (bank 5) |
| `data/sample_options_w0.txt` | 0 | `data/ubershader/370703aad8d5cd3c_bytecode.bin` (bank 6) | `data/ubershader/bd69fe13cfd67640_vertex_bytecode.bin` (bank 5) |
| `data/sample_options_w2.txt` | 2 | `data/ubershader/370703aad8d5cd3c_bytecode.bin` (bank 6) | `data/ubershader/311cc9e748507504_vertex_bytecode.bin` (bank 5) |
| `data/sample_options_w3.txt` | 3 | `data/ubershader/370703aad8d5cd3c_bytecode.bin` (bank 6) | `data/ubershader/f240863ff3acd9ad_vertex_bytecode.bin` (bank 5) |

`--gate` runs structural verification gates; `uberspec gate
<bytecode.bin> <control.bin>` runs them on an already existing pair.
