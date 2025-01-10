FILE="$1"
FILENAME="${FILE%.*}"
stack run $FILE &&
spirv-as $FILE.asm -o $FILE.spv &&
spirv-val $FILE.spv &&
./Indigo test.vert.spv $FILE.spv
