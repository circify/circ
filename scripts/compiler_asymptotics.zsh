#!/usr/bin/env zsh
set -ex

function usage {
    echo "Usage: $0 COMPILER_COMMAND TEMPLATE PATTERN REPLACEMENTS..."
    exit 2
}

compiler_command=($(eval echo $1))
template_file=$2
pattern=$3
replacements=(${@:4})

[[ ! -z $compiler_command ]] || (echo "Empty compiler command" && usage)
if [[ ! -a $template_file ]]
then
    for arg in $compiler_command
    do
        if [[ $arg =~ .*.zok ]]
        then
            echo "template $arg"
            template_file=$arg
        fi
    done
fi
[[ -a $template_file ]] || (echo "No file at $template_file" && usage)
[[ ! -z $pattern ]] || (echo "Empty pattern" && usage)
[[ ! -z $replacements ]] || (echo "Empty replacements" && usage)

echo $replacements

for replacement in $replacements
do
    t=$(mktemp compiler_asymptotics_XXXXXXXX.zok)
    cat $template_file | sed "s/$pattern/$replacement/g" > $t
    instantiated_command=$(echo $compiler_command | sed "s/$template_file/$t/")
    echo $instantiated_command
    rm $t
done

