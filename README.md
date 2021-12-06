# PoC of using LegoSNARK with BBS+

Using LegoGroth16, the cc-SNARK specified in the LegoSNARK to prove properties of messages signed in a BBS+ signature.

The cc-SNARK is [here](https://github.com/lovesh/legogro16/tree/debugging)

## Examples
1. See test `bound_check_message` where a specific signed message is proven in some range, i.e. for public `min` and `max`, `min < message < max` 
2. See test `bound_check_messages_sum` where sum of specific signed messages is proven in some range, i.e. for public `min` and `max`, `min < sum < max`.