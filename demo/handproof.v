f32_u64(n) = f32_f64(f64_u64(if n < 2^53 then n else x(n)))

x(n) = (n|((n& 0x7FF) + 0x7FF)) & ~ 0x7FF

f32_s64(n) = f32_f64(f64_s64(if n < 2^53 then n else x(n)))

round_to_odd(n) = (n>>1)|(n&1)
f64_u64(n) = if n < 2^63 then f64_s64(n) else 2*f64_s64(round_to_odd(n))






WTS:
f32_u64(n) =
  if n < 2^63
  then f32_s64(n)
  else f32_s64(round_to_odd(n)) * 2



WTS-(a)
(2^63 <= n) =>
f32_u64(n) = f32_s64(round_to_odd(n)) * 2
<->
f32_f64(f64_u64(if n <2^53 then n else x(n))) = 2 * f32_f64(f64_s64(if (round_to_odd(n)) < 2^53
                                                                  then round_to_odd(n)
                                                                  else x(round_to_odd(n))))
<-
f64_u64(if n <2^53 then n else x(n)) = 2 * f64_s64(if (round_to_odd(n)) < 2^53
                                                 then round_to_odd(n)
                                                 else x(round_to_odd(n)))
<->
f64_u64(x(n)) = 2 * f64_s64(if (round_to_odd(n)) < 2^53
                            then round_to_odd(n)
                            else x(round_to_odd(n)))
<->
if x(n) < 2^63
then f64_s64(n)
else 2*f64_s64(round_to_odd(x(n)))
= 2 * f64_s64(if (round_to_odd(n)) < 2^53
              then round_to_odd(n)
              else x(round_to_odd(n)))
<->
assert(x(n) < 2^63)
{ LHS of & < 2^63. BOTH of | < 2^63 }

f64_s64(n) =
2 * f64_s64(if (round_to_odd(n)) < 2^53
            then round_to_odd(n)
            else x(round_to_odd(n)))
<->
assert((round_to_odd(n)) >= 2^53)
{ round_to_odd(n) >= n>>1 = n/2 >= 2^62 >= 2^53 }

f64_s64(n) =
2 * f64_s64(x(round_to_odd(n)))
<->


Float.of_long
Float.of_long_from_words:
  forall l : int64,
  Float.of_long l =
  Float.add
    (Float.sub (Float.from_words Float.ox4530_0000 (Int.add (Int64.hiword l) Float.ox8000_0000))
       (Float.from_words Float.ox4530_0000 (Int.repr (two_p 20 + two_p 31))))
    (Float.from_words Float.ox4330_0000 (Int64.loword l))
Float.of_long_decomp:
  forall l : int64,
  Float.of_long l =
  Float.add (Float.mul (Float.of_int (Int64.hiword l)) (Fappli_IEEE_extra.BofZ 53 1024 eq_refl eq_refl (2 ^ 32)))
    (Float.of_intu (Int64.loword l))