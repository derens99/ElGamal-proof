# ElGamal Encryption

## General
Proving ElGamal Encryption using EasyCrypt

### Three parts
1. Key Generation
2. Encryption algorithm
3. Decryption algorithm

### Hashed ElGamal

(this has already been done in EasyCrypt, so please don't
 start by looking for an existing EasyCrypt proof)

types:

group

  (e.g., int with +, so inverse is negation, and identity is 0)

  binary operator ^^

    x ^^ y
    associative (x ^^ y) ^^ z = x ^^ (y ^^ z)

  identity gid

    x ^^ gid = x = gid ^^ x

  unary operator kinv  (won't acutally need this)
    (kinv x) ^^ x = gid
    x ^^ (kinv x) = gid

exp (exponent)

  binary operator *
  commutative & associative
    x * y = y * x

  distribution dexp

connecting group and exp:

generator: g : group

exponentiation binary operator ^

  x : group
  q : exp
  --
  x ^ q : group

  all element of group are uniquely determined via exponentiation
  from g

  forall (x : group), there is a unique (q : exp), such that
  x = g ^ q

axiom: (g ^ q1) ^ q2 = g ^ (q1 * q2)

lemma: (x ^ q1) ^ q2 = x ^ (q1 * q2)

Idea: computing ^ is cheap, computing log (g ^ q => q) is hard.

text
  binary operator +^ (exclusive or)
  identity text0

  usual axioms

  distribution dtext

## Hashed ElGamal is a public key encryption scheme, that makes use of a random oracle RO

### key generation:

q <$ dexp
return (g ^ q, q)

pubk = g ^ q
privk = q

### encryption of text t using pubk:

  r <$ dexp
  u <@ RO.f(pubk ^ r)    pubk ^ r = (g ^ q) ^ r = g ^ (q * r)
  return (g ^ r, t +^ u)

  cipher text is (g ^ r, t +^ u)

decryption of cipher text (x, v) using privk:

  u <@ RO.f(x ^ privk)
  return v +^ u

  (g ^ r) ^ q = g ^ (r * q) = g ^ (q * r)

  t +^ u +^ u = t =^ text0 = t

## Contributing
Pull requests are welcome. For major changes, please open an issue first to discuss what you would like to change.

### Contributors
Deren Singh and Tanner Braun

## License
[MIT](https://choosealicense.com/licenses/mit/)
