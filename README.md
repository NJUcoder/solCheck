# Build and Install Z3
git clone https://github.com/Z3Prover/z3.git

cd z3

python scripts/mk_make.py

cd build

make

sudo make install

# Download and build evmOp


#How to Use

首先使用 **python chMod.py** 改变solc目录下所有版本的编译器执行权限

然后执行 **make** 生成  **solcCheck** 可执行文件

**solcCheck** 使用方式如下：

> ./solcCheck &lt;solFile&gt; &lt;contractName&gt; &lt;solcVersion&gt; &lt;solcOpEnabled&gt; &lt;solcOpRuns&gt;

其中

solFile : 待验证合约源代码文件路径

contractName : 待验证合约名

solcVersion : Solidity编译器版本

solcOpEnabled (默认为true): true or false, 表示是否开启编译器的编译优化选项

solcOpRuns (默认为200): Estimated number of contract runs for optimizer tuning
