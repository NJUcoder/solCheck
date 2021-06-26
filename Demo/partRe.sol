contract A{
	uint a;
	function safeAdd(uint a, uint b) returns(uint) {
		uint c = a + b;
		assert(c >= a && c >= b);
		return c;
	}
	function B() public {
		a = safeAdd(a, 0x15);
		a = 0x40;
		a = safeAdd(a, 0x35);
	}
}