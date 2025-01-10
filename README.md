# Hibiscus

## Preparement

1. Install `ghcup` and `stack` ([Ref](https://www.haskell.org/ghcup/install/))
1. Install `spirv-tools` (ex: `sudo pacman -S spirv-tools`)
1. Shader Runner [`Indigo`](https://github.com/x06lan/Indigo/actions/runs/12656237974)
1. Vertex Shader ([test.vert.spv.txt](https://github.com/user-attachments/files/18155498/test.vert.spv.txt))

## Quick Start

```bash
wget https://github.com/user-attachments/files/18155498/test.vert.spv.txt
mv test.vert.spv.txt test.vert.spv
sh ./run.sh ./test/example.hi 
```

should look this 

![screenshot-2024-12-17-15-44-15](https://github.com/user-attachments/assets/1c9012d3-2c1a-4617-a253-1152bee0e223)

