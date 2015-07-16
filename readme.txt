Eliptic Curve Cryptography in JavaScript
Bitcoin curve and Jacobian optimization
----------------------------------------
This is an implimentation of eliptic curves and corresponding
cryptographical functions to allow for key sharing.

Utilizes internal jacobian coordinates to avoid division operations.

Default setup uses the bitcoin eliptic curve parameters.

Large integer operations are done using the BigInteger.js library:
https://github.com/peterolson/BigInteger.js

Eliptic curve code is based on Orion Lawlor's python implementation:
https://www.cs.uaf.edu/2015/spring/cs463/lecture/02_27_ECC_jacobi/ECC_bitcoin_jacobi.py