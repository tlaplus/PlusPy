./pluspy -S0 -c100 Exprs > test11.out 2>test11.out2
if cmp -s test11.out regression/test11.exp
then
    if cmp -s test11.out2 regression/test11.exp2
    then
        rm -rf test11.out test11.out2
        exit 0
    fi
fi
exit 1
