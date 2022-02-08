import getopt
import subprocess
import sys

from util import *

def help():
    """ Print help string """

    help_str = """
python3 driver.py 

Description
-----------
    -i, --install 
        install all dependencies from the feature set
    
    -c, --check
        run `cargo check` 

    -b, --build
        run `cargo build` and build all dependencies from the feature set 

    -t, --test 
        run `cargo test` and test all dependencies from the feature set
    
    -f, --format
        run `cargo fmt --all`
        
    -l, --lint 
        run `cargo clippy`
        
    -C, --clean 
        remove all generated files
    
    -A, --all_features
        set all features on 

    -L, --list_features
        print active feaures

    -a, --add_feature=<aby,c_front>
        add a feature to the feature set
        
    -r, --remove_feature=<aby,c_front>"
        remove a feature from the feature set
"""
    print(help_str)

def install(features):
    """
    Used for installing third party libraries

    Parameters
    ----------
        features : set of str
            set of features required
    """

    for f in features:
        if f in ('aby'):
            subprocess.run(["git", "clone", "https://github.com/edwjchen/ABY.git", ABY_SOURCE])
        else:
            raise Exception("Unknown feature: "+f)

def check(features):
    """
    Run cargo check

    Parameters
    ----------
        features : set of str
            set of features required
    """

    cmd = ["cargo", "check"]

    cargo_features = filter_cargo_features(features)
    if cargo_features:        
       cmd = cmd + ["--features"] + cargo_features

    subprocess.run(cmd)

def build(features):
    """
    Run cargo build and any test cases in the feature list

    Parameters
    ----------
        features : set of str
            set of features required
    """

    release_cmd = ["cargo", "build", "--release", "--examples"]
    cmd = ["cargo", "build", "--examples"]

    cargo_features = filter_cargo_features(features)
    if cargo_features:
        release_cmd = release_cmd + ["--features"] + cargo_features
        cmd = cmd + ["--features"] + cargo_features

    subprocess.run(release_cmd)
    subprocess.run(cmd)

    for f in features: 
        if f in ('aby'):
            if 'c_front' in features:
                subprocess.run(["./scripts/build_mpc_c_test.zsh"])
            subprocess.run(["./scripts/build_mpc_zokrates_test.zsh"])
            subprocess.run(["./scripts/build_aby.zsh"])

def test(features):
    """
    Run cargo tests and any test cases in the feature list

    Parameters
    ----------
        features : set of str
            set of features required
    """

    subprocess.run(["cargo", "test"])
    subprocess.run(["./scripts/zokrates_test.zsh"])
    subprocess.run(["./scripts/test_zok_to_ilp.zsh"])
    subprocess.run(["./scripts/test_zok_to_ilp_pf.zsh"])
    subprocess.run(["./scripts/test_datalog.zsh"])
    subprocess.run(["python3", "./scripts/aby_tests/zokrates_test_aby.py"])

    for f in features: 
        if f in ('aby'):
            if 'c_front' in features:
                subprocess.run(["python3", "./scripts/aby_tests/c_test_aby.py"])

def format():
    print("formatting!")
    subprocess.run(["cargo", "fmt", "--all"])

def lint():
    print("linting!")
    subprocess.run(["cargo", "clippy"])

def clean():
    print("cleaning!")
    subprocess.run(["./scripts/clean_aby.zsh"])
    subprocess.run(["rm", "-rf", "scripts/aby_tests/__pycache__"])
    subprocess.run(["rm", "-rf", "P", "V", "pi", "perf.data perf.data.old flamegraph.svg"])

def set_features(features):
    """
    Filter invalid features and save features to a file.

    Parameters
    ----------
        features : set of str
            set of features required
    """
    def verify_feature(f):
        if f in valid_features:
            return True
        return False
    features = set(sorted([f for f in features if verify_feature(f)]))
    print("Feature set:", features)
    save_features(features)
    return features 

if __name__ == '__main__':
    acts = "hicbtflCLAa:r:"
    actions = ["help", "install","check","build","test","format","lint","clean","all_features","list_features","add_feature=","remove_feature="]
    try:
        opts, args = getopt.getopt(sys.argv[1:],acts,actions)
    except getopt.GetoptError:
        print("python3 driver.py --help")
        sys.exit(2)

    features = load_features()
    set_env(features)
    all_flag = False
    install_flag = False
    check_flag = False
    build_flag = False
    test_flag = False
    format_flag = False
    lint_flag = False
    clean_flag = False
    list_features_flag = False
    features_flag = False
    for opt, arg in opts:
        if opt in ('-A', '--all_features'):
            all_flag = True
        if opt in ('-h', '--help'):
            help()
        if opt in ('-i', '--install'):
            install_flag = True
        if opt in ('-c', '--check'):
            check_flag = True
        if opt in ('-b', '--build'):
            build_flag = True
        if opt in ('-t', '--test'):
            test_flag = True
        if opt in ('-f', '--format'):
            format_flag = True
        if opt in ('-l', '--lint'):
            lint_flag = True
        if opt in ('-C', '--clean'):
            clean_flag = True
        if opt in ('-L', '--list_features'):
            list_features_flag = True
        if opt in ('-a', '--add_feature'):
            features_flag = True
            features.add(arg)
        if opt in ('-r', '--remove_feature'):
            features_flag = True
            if arg in features:
                features.remove(arg)
    
    if all_flag:
        features = set_all_features()
        print("Feature set:", features)
    else:
        if features_flag:
            features = set_features(features)

        if list_features_flag and not features_flag:
            print("Feature set:", features)
    
    if install_flag:
        install(features)
    
    if check_flag:
        check(features)
    
    if build_flag:
        build(features)

    if test_flag:
        test(features)

    if format_flag:
        format()

    if lint_flag:
        lint()

    if clean_flag:
        clean()
