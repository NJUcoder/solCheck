contract Token{
    mapping(address => uint) balances;
    function transfer(address _to, uint _value) public{
        assert(balances[_to] + _value > balances[_to]);
        addValue(_to, _value);
    }
    function addValue(address _to, uint _value) public{
        balances[_to] = balances[_to] + _value;
    }
    function transfer2(address _to1, address _to2, uint _value) public{
        assert(balances[_to1] + _value > balances[_to1]);
        assert(balances[_to2] + _value > balances[_to2]);
        balances[_to1] = balances[_to1] + _value;
        balances[_to2] = balances[_to2] + _value;
    }
}