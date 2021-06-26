contract sloadExample{
    bool b;
    address owner;
    function f(address newOwner) public{
        assert(b);
        assert(owner == msg.sender);
        owner = newOwner;
    }
}