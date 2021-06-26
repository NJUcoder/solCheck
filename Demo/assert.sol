contract A{
    uint a;
    uint c;
    function B(bool b) public {
        if(b)
            c = 12;
        else
            c = 34;
        a = c + 2;
        assert(a >= c && a >= 2);
    }
}