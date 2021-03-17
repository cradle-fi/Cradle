// SPDX-License-Identifier: MIT
pragma solidity ^0.6.0;
pragma experimental ABIEncoderV2;

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow, so we distribute
        return (a / 2) + (b / 2) + (((a % 2) + (b % 2)) / 2);
    }
}

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly {
            size := extcodesize(account)
        }
        return size > 0;
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data)
    internal
    returns (bytes memory)
    {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return
        functionCallWithValue(
            target,
            data,
            value,
            "Address: low-level call with value failed"
        );
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) =
        target.call{value: value}(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data)
    internal
    view
    returns (bytes memory)
    {
        return
        functionStaticCall(
            target,
            data,
            "Address: low-level static call failed"
        );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.3._
     */
    function functionDelegateCall(address target, bytes memory data)
    internal
    returns (bytes memory)
    {
        return
        functionDelegateCall(
            target,
            data,
            "Address: low-level delegate call failed"
        );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.3._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) private pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transfer.selector, to, value)
        );
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transferFrom.selector, from, to, value)
        );
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.approve.selector, spender, value)
        );
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance =
        token.allowance(address(this), spender).add(value);
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance =
        token.allowance(address(this), spender).sub(
            value,
            "SafeERC20: decreased allowance below zero"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.
        bytes memory returndata =
        address(token).functionCall(
            data,
            "SafeERC20: low-level call failed"
        );
        if (returndata.length > 0) {
            // Return data is optional
            // solhint-disable-next-line max-line-length
            require(
                abi.decode(returndata, (bool)),
                "SafeERC20: ERC20 operation did not succeed"
            );
        }
    }
}

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount)
    external
    returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender)
    external
    view
    returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

contract Operator is Context, Ownable {
    address private _operator;

    event OperatorTransferred(
        address indexed previousOperator,
        address indexed newOperator
    );

    constructor() internal {
        _operator = _msgSender();
        emit OperatorTransferred(address(0), _operator);
    }

    function operator() public view returns (address) {
        return _operator;
    }

    modifier onlyOperator() {
        require(
            _operator == msg.sender,
            "operator: caller is not the operator"
        );
        _;
    }

    function isOperator() public view returns (bool) {
        return _msgSender() == _operator;
    }

    function transferOperator(address newOperator_) public onlyOwner {
        _transferOperator(newOperator_);
    }

    function _transferOperator(address newOperator_) internal {
        require(
            newOperator_ != address(0),
            "operator: zero address given for new operator"
        );
        emit OperatorTransferred(address(0), newOperator_);
        _operator = newOperator_;
    }
}

contract Cradle is Operator {
    event Buy(address indexed user, address project, uint256 stockAmt);
    event Create(address indexed user, address project);
    event ReFund(address indexed user, address project, uint256 amount);
    event Withdraw(address indexed user, address project, uint256 amount);

    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    mapping(address => bool) public stableTokens;

    struct UserInfo {
        uint256 totalStock;
        uint256 totalMoney;
        uint256 released;
    }

    struct ProjectInfo {
        uint8 status; //0 normal  ;  1 did not start  ;2 vote project.
        uint32 userCount;
        uint256[] times;
        address stock; //stock token address
        address money; //money token address
        uint256 stockAmount; //total stock amount
        uint256 moneyAmount; //total target money amount
        uint256 stockBalance;
        uint256 moneyBalance;
        uint256 subscribed; //have sold stock amount
        address creator;
        mapping(address => UserInfo) userInfo; //user balance
    }

    address public feeAccount;
    uint256 public feeRate;
    uint256 public count = 1; // project count
    mapping(address => ProjectInfo) public allProject;

    constructor() public {
        feeRate = 15;
        feeAccount = msg.sender;
    }

    function setStableToken(address money, bool result) public onlyOwner {
        stableTokens[money] = result;
    }

    function setFeeAccount(address _feeAccount) public onlyOwner {
        feeAccount = _feeAccount;
    }

    function setFeeRate(uint256 _feeRate) public onlyOwner {
        feeRate = _feeRate;
    }

    function projectInfo(address projectId)
    public
    view
    returns (uint256[3] memory times)
    {
        ProjectInfo memory project = allProject[projectId];
        times[0] = project.times[0];
        times[1] = project.times[1];
        times[2] = project.times[2];
    }

    //create project
    function create(
        address stock,
        address money,
        uint256 stockAmount,
        uint256 moneyAmount,
        uint256[] memory times
    ) public returns (address projectId) {
        //check time
        require(stock != address(0), "create:stock address cannot be zero");
        require(stableTokens[money] == true, "create:money address error");
        require(stock != money, "create:addresses cannot be equal");
        require(block.timestamp < times[0], "create:startTime error ");
        require(
            times[0].add(3600) <= times[1] && times[0].add(2592000) >= times[1],
            "create:midTime error "
        );
        require(
            times[1].add(3600) <= times[2] &&
            times[1].add(94608000) >= times[2],
            "create:endTime error "
        );
        require(stockAmount > 0, "create:stock error ");
        require(moneyAmount > 0, "create:outAmount error ");
        //transfer stock
        _safeTransferFrom(stock, msg.sender, address(this), stockAmount);
        bytes32 hash = keccak256(abi.encodePacked(stock, msg.sender, count++));
        assembly {
            mstore(0, hash)
            projectId := mload(0)
        }
        require(
            allProject[projectId].stock == address(0),
            "create:projectid error "
        );
        allProject[projectId] = ProjectInfo({
        status: 0,
        stock: stock,
        money: money,
        stockAmount: stockAmount,
        moneyAmount: moneyAmount,
        stockBalance: stockAmount,
        moneyBalance: 0,
        subscribed: 0,
        userCount: 0,
        times: times,
        creator: msg.sender
        });
        emit Create(msg.sender, projectId);
    }

    function buy(address projectId, uint256 targetStockAmount)
    public
    updateProject(projectId)
    {
        ProjectInfo storage project = allProject[projectId];
        require(project.status == 0, "buy:failed project");
        require(
            block.timestamp >= project.times[0],
            "buy:project hasn't started yet"
        );
        require(block.timestamp <= project.times[1], "buy: time over ");
        //check amount
        require(targetStockAmount > 0, "buy:amount error ");
        uint256 left = project.stockAmount.sub(project.subscribed);
        require(left > 0, "buy: finished");
        //adjust amount
        if (targetStockAmount > left) {
            targetStockAmount = left;
        }
        // calc need money
        uint256 moneyNeed =
        project.moneyAmount.mul(targetStockAmount).div(project.stockAmount);
        project.subscribed = project.subscribed.add(targetStockAmount);
        if (project.userInfo[msg.sender].totalStock == 0) {
            project.userCount = project.userCount + 1;
        }
        project.userInfo[msg.sender].totalStock = project.userInfo[msg.sender]
        .totalStock
        .add(targetStockAmount);
        project.userInfo[msg.sender].totalMoney = project.userInfo[msg.sender]
        .totalMoney
        .add(moneyNeed);
        transferIn(false, projectId, msg.sender, moneyNeed);
        emit Buy(msg.sender, projectId, targetStockAmount);
    }

    function userBuyInfo(address projectId, address user)
    public
    view
    returns (uint256 totalStock, uint256 released)
    {
        totalStock = allProject[projectId].userInfo[user].totalStock;
        released = allProject[projectId].userInfo[user].released;
    }

    //user release
    function userRelease(address projectId) public updateProject(projectId) {
        ProjectInfo storage project = allProject[projectId];
        if (project.status == 0) {
            //check time
            require(
                block.timestamp > project.times[1],
                "userRelease：it is not time yet "
            );

            uint256 currentTime = Math.min(block.timestamp, project.times[2]);

            //adjust amount
            uint256 currentMaxAmount =
            currentTime
            .sub(project.times[1])
            .mul(project.userInfo[msg.sender].totalStock)
            .div(project.times[2].sub(project.times[1]))
            .sub(project.userInfo[msg.sender].released);

            if (currentMaxAmount > 0) {
                project.userInfo[msg.sender].released = project.userInfo[
                msg.sender
                ]
                .released
                .add(currentMaxAmount);
                transferOut(true, projectId, msg.sender, currentMaxAmount);
                emit Withdraw(msg.sender, projectId, currentMaxAmount);
            }
        } else if (project.status == 1) {
            if (project.userInfo[msg.sender].totalStock > 0) {
                uint256 moneyAmt = project.userInfo[msg.sender].totalMoney;
                if (moneyAmt > 0) {
                    project.userInfo[msg.sender].totalStock = 0;
                    project.userInfo[msg.sender].totalMoney = 0;
                    transferOut(false, projectId, msg.sender, moneyAmt);
                    emit ReFund(msg.sender, projectId, moneyAmt);
                }
            }
        }
    }

    //project release
    function release(address projectId) public updateProject(projectId) {
        ProjectInfo storage project = allProject[projectId];
        if (project.status == 0) {
            //check time
            require(
                block.timestamp > project.times[1],
                "projectGetMoney:It is not time yet"
            );
            uint256 currentTime = Math.min(block.timestamp, project.times[2]);
            //adjust amount
            uint256 moneyAmt =
            currentTime
            .sub(project.times[1])
            .mul(project.moneyAmount)
            .div(project.times[2].sub(project.times[1]))
            .sub(project.moneyAmount.sub(project.moneyBalance));

            if (moneyAmt > 0) {
                uint256 moneyFee = moneyAmt.mul(feeRate).div(1000);
                uint256 projectAmt = moneyAmt.sub(moneyFee);
                transferOut(false, projectId, feeAccount, moneyFee);
                transferOut(false, projectId, project.creator, projectAmt);
                emit Withdraw(project.creator, projectId, projectAmt);
            }
        } else if (project.status == 1) {
            transferOut(true, projectId, project.creator, project.stockAmount);
            emit ReFund(msg.sender, projectId, project.stockAmount);
        }
    }

    modifier updateProject(address projectId) {
        ProjectInfo storage project = allProject[projectId];
        if (project.times[1] > 0) {
            if (project.status == 0) {
                if (
                    project.times[1] < block.timestamp &&
                    project.subscribed < project.stockAmount
                ) {
                    project.status = 1;
                }
            }
        }
        _;
    }

    function transferOut(
        bool isStock,
        address projectId,
        address to,
        uint256 amount
    ) private {
        ProjectInfo storage project = allProject[projectId];
        address token;
        if (isStock) {
            token = project.stock;
            require(
                project.stockBalance >= amount,
                "transferOut:stockBalance > amount"
            );
            project.stockBalance = project.stockBalance.sub(amount);
        } else {
            token = project.money;
            require(
                project.moneyBalance >= amount,
                "transferOut:moneyBalance > amount"
            );
            project.moneyBalance = project.moneyBalance.sub(amount);
        }
        _safeTransfer(token, to, amount);
    }

    function transferIn(
        bool isStock,
        address projectId,
        address from,
        uint256 amount
    ) private {
        ProjectInfo storage project = allProject[projectId];
        address token;
        if (isStock) {
            token = project.stock;
            project.stockBalance = project.stockBalance.add(amount);
        } else {
            token = project.money;
            project.moneyBalance = project.moneyBalance.add(amount);
        }
        safeTransferFrom(token, from, amount);
    }

    function _safeTransfer(
        address token,
        address to,
        uint256 value
    ) private {
        if (value == 0) {
            return;
        }
        IERC20(token).safeTransfer(to, value);
    }

    function safeTransferFrom(
        address token,
        address from,
        uint256 value
    ) private {
        _safeTransferFrom(token, from, address(this), value);
    }

    function _safeTransferFrom(
        address token,
        address from,
        address to,
        uint256 value
    ) private {
        uint256 beforeAmount = IERC20(token).balanceOf(to);
        IERC20(token).safeTransferFrom(from, to, value);
        uint256 afterAmount = IERC20(token).balanceOf(to);
        require(afterAmount == beforeAmount + value, " TRANSFER_FAILED");
    }
}
