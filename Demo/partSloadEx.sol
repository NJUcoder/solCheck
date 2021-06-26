contract partSloadEx{
    mapping(address => uint) balances;
    function transfer(address _to, uint _value) public{
        assert(balances[_to] + _value > balances[_to]);
        addValue(_to, _value);
    }
    function addValue(address _to, uint _value) public{
        balances[_to] = balances[_to] + _value;
    }
}