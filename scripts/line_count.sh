#!/bin/bash

if [ $# -ne 1 ]; then
  echo "Use one arguments [CompCert_v2.1 / CompCert_v3.0.1 / CompCert_v3.5 / CompCertX / CompComp / CompCertM / CompCertM-linking / tex]"
  exit 1
fi

if [ "$1" == "CompCert_v2.1" ]; then
    wget -q http://compcert.inria.fr/release/compcert-2.1.tgz
    mkdir _CompCert
    tar xvfzp compcert-2.1.tgz -C ./_CompCert > /dev/null
    cp line_count/CompCert_v2.1.rb _CompCert/compcert-2.1
    cp line_count/ndfun _CompCert/compcert-2.1
    cd _CompCert/compcert-2.1
    ruby CompCert_v2.1.rb
    cd ../..
    rm -rf _CompCert compcert-2.1.tgz
elif [ "$1" == "CompCert_v3.0.1" ]; then
    git clone -c advice.detachedHead=false -q -b v3.0.1 https://github.com/AbsInt/CompCert.git _CompCert
    cp line_count/CompCert_v3.0.1.rb _CompCert/
    cp line_count/ndfun _CompCert/
    cd _CompCert
    ruby CompCert_v3.0.1.rb
    cd ..
    rm -rf _CompCert
elif [ "$1" == "CompCert_v3.5" ]; then
    git clone -c advice.detachedHead=false -q -b v3.5 https://github.com/AbsInt/CompCert.git _CompCert
    cp line_count/CompCert_v3.5.rb _CompCert/
    cp line_count/ndfun _CompCert/
    cd _CompCert
    ruby CompCert_v3.5.rb
    cd ..
    rm -rf _CompCert
elif [ "$1" == "CompCertX" ]; then
    git clone -c advice.detachedHead=false -q https://github.com/DeepSpec/dsss17.git _CompCertX
    cp line_count/Yale-CompCertX.rb _CompCertX/CAL
    cp line_count/ndfun _CompCertX/CAL
    cd _CompCertX/CAL
    ruby Yale-CompCertX.rb
    cd ../..
    rm -rf _CompCertX
elif [ "$1" == "CompComp" ]; then
    git clone -c advice.detachedHead=false -q https://github.com/PrincetonUniversity/compcomp.git _CompComp
    cp line_count/Princeton-CompComp.rb _CompComp/
    cp line_count/ndfun _CompComp/
    cd _CompComp
    ruby Princeton-CompComp.rb
    cd ..
    rm -rf _CompComp
elif [ "$1" == "CompCertM" ]; then
    cp line_count/CompCertM.rb ../../
    cp line_count/ndfun ../../
    cd ../../
    ruby CompCertM.rb
    rm CompCertM.rb ndfun
    cd compcomp-linking/scripts
elif [ "$1" == "CompCertM-linking" ]; then
    cp line_count/CompCertM-linking.rb ../
    cd ../
    ruby CompCertM-linking.rb
    rm CompCertM-linking.rb
    cd scripts
elif [ "$1" == "tex" ]; then
    cp line_count/CompCertM-linking-tex.rb ../
    cd ../
    ruby CompCertM-linking-tex.rb
    rm CompCertM-linking-tex.rb
    cd scripts
else
  echo "Use one arguments [CompCert_v2.1 / CompCert_v3.0.1 / CompCert_v3.5 / CompCertX / CompComp / CompCertM / CompCertM-linking/ tex]"
fi
