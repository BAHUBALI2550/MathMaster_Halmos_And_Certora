// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity ^0.8.3;

import {Base_Test, console2} from "./Base_Test.t.sol";
import {MathMasters} from "src/MathMasters.sol";
import {SymTest} from "halmos-cheatcodes/SymTest.sol";

contract MathMastersTest is Base_Test {
    function testMulWad() public {
        assertEq(MathMasters.mulWad(2.5e18, 0.5e18), 1.25e18);
        assertEq(MathMasters.mulWad(3e18, 1e18), 3e18);
        assertEq(MathMasters.mulWad(369, 271), 0);
    }

    function testMulWadFuzz(uint256 x, uint256 y) public pure {
        // Ignore cases where x * y overflows.
        unchecked {
            if (x != 0 && (x * y) / x != y) return;
        }
        assert(MathMasters.mulWad(x, y) == (x * y) / 1e18);
    }

    function testMulWadUp() public {
        assertEq(MathMasters.mulWadUp(2.5e18, 0.5e18), 1.25e18);
        assertEq(MathMasters.mulWadUp(3e18, 1e18), 3e18);
        assertEq(MathMasters.mulWadUp(369, 271), 1);
    }

    function testMulWadUpFuzz(uint256 x, uint256 y) public {
        // We want to skip the case where x * y would overflow.
        // Since Solidity 0.8.0 checks for overflows by default,
        // we cannot just multiply x and y as this could revert.
        // Instead, we can ensure x or y is 0, or
        // that y is less than or equal to the maximum uint256 value divided by x
        if (x == 0 || y == 0 || y <= type(uint256).max / x) {
            uint256 result = MathMasters.mulWadUp(x, y);
            uint256 expected = x * y == 0 ? 0 : (x * y - 1) / 1e18 + 1;
            assertEq(result, expected);
        }
        // If the conditions for x and y are such that x * y would overflow,
        // this function will simply not perform the assertion.
        // In a testing context, you might want to handle this case differently,
        // depending on whether you want to consider such an overflow case as passing or failing.
    }

    function check_testMulWadFuzz(uint256 x, uint256 y) public pure {
        // Ignore cases where x * y overflows.
        unchecked {
            if (x != 0 && (x * y) / x != y) revert();
        }
        assert(MathMasters.mulWad(x, y) == (x * y) / 1e18);
    }

    // From CodeHawks participant!
    // https://www.codehawks.com/report/clrp8xvh70001dq1os4gaqbv5#H-02
    function testMulWadUpFuzzOverflow(uint256 x, uint256 y) public pure {
        // Precondition: x * y > uint256 max
        vm.assume(x > 1 && x < 10);
        vm.assume(y > type(uint256).max / x);

        // vm.expectRevert();
        // This should revert! But it does not
        MathMasters.mulWadUp(x, y);
    }

    function testCheckCertoraOutput() public pure {
        uint256 x = 1000000000000001025;
        uint256 y = 1000000000000000000;
        uint256 result = MathMasters.mulWadUp(x, y);
        uint256 expected = (x * y - 1) / 1e18 + 1;
        assert(result == expected);
    }

    // halmos --function check_sqrt --solver-timeout-assertion 0
    // Ahh! This is too complicated for our measly computer!
    // Is there another way we can compare?
    function check_sqrt(uint256 randomNumber) public pure {
        assert(uniSqrt(randomNumber) == MathMasters.sqrt(randomNumber));
    }

    function testSqrt() public {
        assertEq(MathMasters.sqrt(0), 0);
        assertEq(MathMasters.sqrt(1), 1);
        assertEq(MathMasters.sqrt(2704), 52);
        assertEq(MathMasters.sqrt(110889), 333);
        assertEq(MathMasters.sqrt(32239684), 5678);
        assertEq(MathMasters.sqrt(type(uint256).max), 340282366920938463463374607431768211455);
    }

    function testSqrtFuzzUni(uint256 x) public pure {
        assert(MathMasters.sqrt(x) == uniSqrt(x));
    }

    function testSqrtFuzzSolmate(uint256 x) public pure {
        assert(MathMasters.sqrt(x) == solmateSqrt(x));
    }

    function test_strippedSqrt(uint256 randomNumber) public pure {
        uint256 z = _mathMastersSqrtStripped(randomNumber);
        if (z != _solmateSqrtStripped(randomNumber)) {
            assert(_secondHalfOfSqrtFunction(randomNumber, z) == uniSqrt(randomNumber));
        }
    }

    /*//////////////////////////////////////////////////////////////
                            HELPER FUNCTIONS
    //////////////////////////////////////////////////////////////*/
    // The full Solmate function, with the final part removed because it's identical in both implementations.
    function _solmateSqrtStripped(uint256 x) internal pure returns (uint256 z) {
        assembly {
            let y := x

            z := 181
            if iszero(lt(y, 0x10000000000000000000000000000000000)) {
                y := shr(128, y)
                z := shl(64, z)
            }
            if iszero(lt(y, 0x1000000000000000000)) {
                y := shr(64, y)
                z := shl(32, z)
            }
            if iszero(lt(y, 0x10000000000)) {
                y := shr(32, y)
                z := shl(16, z)
            }
            if iszero(lt(y, 0x1000000)) {
                y := shr(16, y)
                z := shl(8, z)
            }

            z := shr(18, mul(z, add(y, 65536)))
        }
    }

    function _mathMastersSqrtStripped(uint256 x) internal pure returns (uint256 z) {
        assembly {
            // z := 0xb5 // 181
            z := 181

            let r := shl(0x7, lt(0xffffffffffffffffffffffffffffffffff, x))
            r := or(r, shl(0x6, lt(0xffffffffffffffffff, shr(r, x))))
            r := or(r, shl(0x5, lt(0xffffffffff, shr(r, x))))
            // Correct: 16777215 0xffffff
            r := or(r, shl(0x4, lt(16777002, shr(r, x))))
            z := shl(shr(0x1, r), z)

            z := shr(0x12, mul(z, add(shr(r, x), 0x10000)))
        }
    }

    // The final part of the original functions, which has been abstracted out for clarity.
    function _secondHalfOfSqrtFunction(uint256 x, uint256 z) internal pure returns (uint256 ret) {
        assembly {
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))

            ret := sub(z, lt(div(x, z), z))
        }
    }
}
