contract sloadExample{
    bool b;
    address owner;
    function f(address newOwner) public{
        assert(b);
        assert(owner == msg.sender);
        owner = newOwner;
    }
    function f1(address a1, address a2) public{
        f(a1);
        f(a2);
    }
    function f2(address a1) public{
        f1(a1, a1);
        f1(a1, a1);
    }
}