contract Token{
    mapping(address => uint) balances;
    function transfer(address _to, uint _value) public {
        assert(balances[_to] + _value > balances[_to]);
        balances[_to] = balances[_to] + _value;
    }
}