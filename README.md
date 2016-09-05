# Differential_attack

Linear and Differential Cryptanalysis.

I implemented a simple and weak chiper in MAGMA. Afterwards, I implemented a two types of attack, linear and differential, that break this chiper easily using Boolean function knowledge. The attack is of kind partial-key-recovery.

The implementation is based on the paper of M. Heys.

All the files contains all the needed function (encryption,decryption functions and attack functions). The file diff_attack.m allows the user to modify the key (at the beginning of the file), the others generate randomly the keys. The choosen file has to be loaded and the function run_attack(n) has to be performed. The input n is the number of plaintext used in the attack (randomly generated).
