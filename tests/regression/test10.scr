./pluspy -S0 -c100 -i Spec TestBoundedFIFO > test10.out 2>test10.out2
if cmp -s test10.out regression/test10.exp
then
    if cmp -s test10.out2 regression/test10.exp2
    then
        rm -rf test10.out test10.out2
        exit 0
    fi
fi
exit 1
