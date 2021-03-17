// SPDX-License-Identifier: MIT

pragma solidity >=0.6.0 <0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IPool {
    function stake(address token,uint256 amount) public override ;
    function withdraw(address token,uint256 amount) public override ;
}
