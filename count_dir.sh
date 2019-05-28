for d in ./*/ ; do (cd "$d" && pwd && loc --files && echo && echo); done
