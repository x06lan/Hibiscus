# Hibiscus

### run.sh
```bash
FILE="$1"
FILENAME="${FILE%.*}"
stack run $FILE &&
spirv-as $FILE.asm -o $FILE.spv &&
spirv-val $FILE.spv &&
./Indigo test.vert.spv $FILE.spv
```


### example/test.hi 
```haskell
Vec4 :: Float -> Float -> Float -> Float -> Vec4 
Vec2 :: Float -> Float -> Vec2
extract_0 :: Vec2 ->  Float
extract_1 :: Vec2 ->  Float

add :: Float -> Float -> Float
add a b = a + b;

main :: Vec2 -> Vec4
main uv = Vec4 (extract_0 uv) (extract_1 uv) (add (extract_0 uv) (extract_1 uv)) 1.0;
```

### indigo (shader runner)
[link](https://github.com/x06lan/Indigo/actions/runs/12656237974)

# run this
```bash
wget https://github.com/user-attachments/files/18155498/test.vert.spv.txt
mv test.vert.spv.txt test.vert.spv
sh run.sh ./example/test.hi 
```
should look this 

![screenshot-2024-12-17-15-44-15](https://github.com/user-attachments/assets/1c9012d3-2c1a-4617-a253-1152bee0e223)

