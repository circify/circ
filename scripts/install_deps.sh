SHELL='bash -ex'

for flag in $1 $2 $3 $4 $5
do
  case $flag in
        --install-aby)
          echo "=== Install ABY"
          cd ..
          if [[ ! -d "ABY" ]]; then 
            git clone https://github.com/edwjchen/ABY.git
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
        --install-kahip)
          echo "=== Install KaHIP"
          cd ..
          if [[ ! -d "KaHIP" ]]; then 
            git clone https://github.com/edwjchen/KaHIP.git
          fi
          cd circ 
          ;;
        --install-seal)
          echo "=== Install SEAL"
          cd ..
          if [[ ! -d "SEAL" ]]; then 
            git clone https://github.com/microsoft/SEAL.git
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

