SHELL='bash -ex'

for flag in $1 $2 $3 $4
do
  case $flag in
        --install-aby)
          echo "=== Install ABY"
          cd ..
          if [[ ! -d "ABY" ]]; then 
            git clone https://github.com/edwjchen/ABY.git
            pushd ABY
            mkdir -p build
            pushd build
            cmake .. -DABY_BUILD_EXE=On
            make
            popd
            popd
          fi
          cd circ 
          ;;
        --install-ezpc) 
          echo "=== Get EZPC header"
          cd ..
          mkdir -p EZPC 
          pushd EZPC
          if [[ ! -f "ezpc.h" ]]; then 
            wget -O ezpc.h https://raw.githubusercontent.com/circify/circ/master/third_party/EZPC/ezpc.h
          fi
          popd
          cd circ
          ;;
        --install-seal)
          echo "=== Install SEAL"
          cd ..
          if [[ ! -d "SEAL" ]]; then 
            git clone https://github.com/microsoft/SEAL.git
            pushd SEAL
            mkdir -p build
            pushd build
            cmake -S . -B build
            cmake --build build
            sudo cmake --install build
            popd
            popd
          fi
          cd circ 
          ;;
        --default-env-flags)
          echo "=== Set default env flags"
          source ./scripts/env.sh
          ;;
        *)
          echo "Unknown command-line flag" $flag
  esac
done

# export ENV paths
if [[ -z "${ABY_SOURCE}" ]]; then
  echo "Missing ABY_SOURCE environment variable."
fi

if [[ -z "${SEAL_SOURCE}" ]]; then
  echo "Missing SEAL_SOURCE environment variable."
fi

