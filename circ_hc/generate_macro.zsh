#!/usr/bin/env zsh

template=$1
dest=$2
body=$(cat $template \
    | sed '/SocketAddrV6/d' \
    | sed 's/crate::/$crate::/' \
    | sed 's/TemplateOp/$Op/g')

echo "
// Warning: this file is generated from src/template.rs and generate_macro.zsh
#[macro_export]
macro_rules! generate_hashcons {
    (\$Op:ty) => {
$body
    };
}
" | rustfmt > $dest
