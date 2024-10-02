/*
 * Verification of MulWad for MathMasters
 */

methods {
    function mulWadUp(uint256 x, uint256 y) external returns uint256 envfree;
}

definition WAD() returns uint256 = 1000000000000000000;

rule check_testMulWadUpFuzz(uint256 x, uint256 y) {
    require(x == 0 || y == 0 || y <= assert_uint256(max_uint256 / x));
    uint256 result = mulWadUp(x, y);
    mathint expected = x * y == 0 ? 0 : (x * y - 1) / WAD() + 1;
    assert(result == assert_uint256(expected));
}

// super power of certora are defining invariants
invariant mulWadUpInvariant(uint256 x, uint256 y)
    mulWadUp(x, y) == assert_uint256(x * y == 0 ? 0 : (x * y - 1)/ WAD() + 1)
    {
        preserved {
            require(x == 0 || y == 0 || y <= assert_uint256(max_uint256 / x));
        }
    }