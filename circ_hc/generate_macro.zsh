#!/usr/bin/env zsh

template=$1
dest=$2
body=$(cat $template \
    | sed '/SocketAddrV6/d' \
    | sed 's/TemplateOp/$Op/g')

echo "
#[macro_export]
macro_rules! generate_hashcons {
    (\$Op:ty) => {
$body
    };
}
" | rustfmt > $dest
