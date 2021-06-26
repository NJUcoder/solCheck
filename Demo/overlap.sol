contract overlapEx{
    uint a;
    uint b;
    function f(uint _a, uint _b) public {
        assert(a > _a);
        assert(b > _b);
        a = a + _a;
        b = b + _b;
    }
}