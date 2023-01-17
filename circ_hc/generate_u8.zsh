#!/usr/bin/env zsh

template=$1
dest=$2
body=$(cat $template \
    | sed '/SocketAddrV6/d' \
    | sed 's/TemplateOp/u8/g')

echo "
// Warning: this file is generated from src/template.rs and generate_u8.zsh
$body
" | rustfmt > $dest

