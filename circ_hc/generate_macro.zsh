#!/usr/bin/env zsh

template=$1
dest=$2
macro_name=$3
body=$(cat $template \
    | sed '/SocketAddrV6/d' \
    | sed 's/crate::/$crate::/' \
    | sed 's/TemplateOp/$Op/g')

echo "
// Warning: this file is generated from $template and generate_macro.zsh
#[macro_export]
macro_rules! $macro_name {
    (\$Op:ty) => {
$body
    };
}
pub use crate::$macro_name as generate_hashcons;
" | rustfmt > $dest
