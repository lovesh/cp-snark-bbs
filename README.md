# PoC of using LegoSNARK with BBS+

Using LegoGroth16, the cc-SNARK specified in the LegoSNARK to prove properties of messages signed in a BBS+ signature.

The cc-SNARK is [here](https://github.com/lovesh/legogro16/tree/debugging)

## Examples
1. See test `bound_check_message` where a specific signed message is proven in some range, i.e. for public `min` and `max`, `min < message < max`. This will be useful in doing proof of age in a range. 
2. See test `bound_check_messages_sum` where sum of specific signed messages is proven in some range, i.e. for public `min` and `max`, `min < sum < max`. This can be useful in proving that the sum of income sources is in a range.
3. See test `compare_messages_sum` where  sum of certain signed messages from the 1st signature is proven less than the sum of certain signed messages from 2nd signature. This can be useful in proving sum of liabilities < sum of assets where liabilities and assets are signed under different signatures.