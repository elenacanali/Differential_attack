KS := ["ABCD","BCDE","CDEF","DEF0","EF01"];
/* FUNZIONI AUSILIARIE */

//input intero modulo e lunghezza della sequenza di output
function IntToSeqPadding(int, modulo, length) 
	seq := IntegerToSequence(int, modulo);
return seq cat [0: i in [1..length-#seq]];
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

//xor di sequenze di uguale lunghezza
function Bitwise_sum(A,B)
return [ ( A[i] + B[i] ) mod 2 : i in [1..#A] ];
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// divide in sottosequenze di 4 bit una sequenza di 16 bit
function SubBlocks(a)
	out:=[];
	for i in [1..(#a/4)] do     
		out:=out cat [a[(i-1)*4+1..(i-1)*4+4]];
	end for;
	return out;
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

//input una stringa di caratteri esadecimali, output sequenza di 16 bit
function ManageInput(P)
	P:=[StringToInteger(P[i],16): i in [1..#P]];
	out:=[];
	for i in [#P..1 by -1] do //reverse order, i 4 bit piu significativi sono a dx
		out:=out cat IntToSeqPadding(P[i],2,4);
	end for;
	return out;
end function;

 //----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

//input una sequenza di sequenze di 4 bit del tipo output di SubBlocks, output stringa di 4 caratteri esadecimali
function ManageOutput(C)
	out:="";
	for i in [#C..1 by -1] do //reverse order, vedi ManageInput
		out:=out cat IntegerToString(Seqint(C[i], 2), 16);
	end for;
	return out;
end function;
 //----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

//input sequenza di 16 bit, del tipo output di ManageInput
function MixingLayer(S)
	perm_ml:=Sym(16)!(2, 5)(3, 9)(4,13)(7,10)(8,14)(12,15);
	perm_ml:=[1..16]^perm_ml;
	out:=[];
	for i in [1..16] do
		out[i]:=S[perm_ml[i]];
	end for;
	return out;
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// input l'output di SubBlocks, output sequenza di 16 bit
function SBox(S)
	X:={0..15};
	perm_s:=SymmetricGroup(X)! (0,14)(1,4,2,13,9,10,6,11,12,5,15,7,8,3);
	out:=[];
	for i in [1..#S] do
		out:=out cat IntToSeqPadding(Seqint(S[i],2)^perm_s,2,4);
	end for;
	return out;
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// inversa della SBox, input e output come Sbox
function SBox_i(S)
	X:={0..15};
	perm_is:=SymmetricGroup(X)! (0,14)(1,4,2,13,9,10,6,11,12,5,15,7,8,3);
	perm_is:=perm_is^13; //Order(perm)=14, compongo (ord-1) volte
	out:=[];
	for i in [1..#S] do
		out:=out cat IntToSeqPadding(Seqint(S[i],2)^perm_is,2,4);
	end for;
	return out;
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
/* CIFRATURA E DECIFRATURA */

// input P stringa esadecimale di 4 caratteri, K sequenza di 5 stringhe esadecimali di 4 caratteri
function Encryption(P,K)
	P:=ManageInput(P);
	//primi 3 round regolari
	for i in [1..3] do
		P:=Bitwise_sum(P,ManageInput(K[i])); // xor con la chiave 
		P:=SubBlocks(P); //SBox
		P:=SBox(P);
		P:=MixingLayer(P); //MixingLayer
	end for;
	//round 4
	P:=Bitwise_sum(P,ManageInput(K[4]));
	P:=SubBlocks(P);
	P:=SBox(P);
	//round 5
	P:=Bitwise_sum(P,ManageInput(K[5]));
	//in output una stringa di 4 caratteri esadecimali
	P:=SubBlocks(P);
	return ManageOutput(P);
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// input e output come Encryption
function Decryption(C, K)
C:=ManageInput(C);
// round 1
C:=Bitwise_sum(C, ManageInput(K[5]));
// round 2
C:=SubBlocks(C);
C:=SBox_i(C);
C:=Bitwise_sum(C, ManageInput(K[4]));
// 3 round regolari
for i in [3..1 by -1] do //reverse order delle chiavi di round
	C:=MixingLayer(C);
	C:=SubBlocks(C);
	C:=SBox_i(C);
	C:=Bitwise_sum(C, ManageInput(K[i]));
end for;
// output
C:=SubBlocks(C);
return ManageOutput(C);
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
/* FUNZIONI DI SUPPORTO PER UTILIZZO DI SBox e sua inversa */

// input stringa di 4 caratteri esadecimali, output stringa di 4 caratteri esadecimali
function usa_SBox(P)
P:=ManageInput(P);
P:=SubBlocks(P); 
P:=SBox(P);
P:=SubBlocks(P);
return ManageOutput(P);
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

function usa_SBox_i(P)
	//P:=ManageInput(P);
	P:=SubBlocks(P); 
	P:=SBox_i(P);
	return SubBlocks(P);
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

//input due plaintext e ciphertext come stringhe esadecimali, 
// output sequenza di 2^8 bit che ha al posto i-esimo il valore della eq5 per la 2-nibble-chiave i-esima  
function Attack(P,C)
	P:=ManageInput(P);
	P:=(P[12]+P[10]+P[9]) mod 2; // seleziono i bit di P correlati
	C:=ManageInput(C);
	C:=SubBlocks(C);
	C:=C[1] cat C[3]; // seleziono il 4 ed il 2 nibble più significativo di C
	X:={@x : x in Subsequences({0,1}, 8)@}; // genero tutti i possibili nibbles 4 e 2 per la chiave K[5]
	eq5:=[];
	for k in X do
		pC:=Bitwise_sum(C,k); // somma con la chiave
		pC:=usa_SBox_i(pC); // inverto SBox
		// selelziono i bit del (de)cifrato parziale (C+random key) coinvolti in eq5, calcolo valore di eq5 su input e lo salvo in eq5[i]
 		eq5:=eq5 cat [( pC[1][1]+pC[1][3]+pC[2][1]+pC[2][3]+P ) mod 2]; // 
	end for;
return eq5;
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// input numero di plaintext
function run_Attack(n)
	KS := ["ABCD","BCDE","CDEF","DEF0","EF01"];
	freq:=[0 : i in [1..2^8]];
	// genero tutti possibili plaintext
    M:={ Q cat W cat R cat T : Q,W,R,T in {"0","1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F"} };
	N:=RandomSubset(M, n);
	for P in N do
		C:=Encryption(P,KS);
		freq:=[freq[i] + (Attack(P,C))[i] : i in [1..2^8]]; // 2^8 è # spazio delle chiavi ridotte=dim sequenza output di Attack	
	end for;
	X:={@x : x in Subsequences({0,1}, 8)@}; // genero tutti i possibili nibbles 4 e 2 per la chiave K[5]
	min:=Min(freq);
	max:=Max(freq);
	v_min:=[];
	v_max:=[];
	for i in [1..2^8] do
		if (freq[i] eq min) then 
			v_min:=v_min cat [i];
			print SubBlocks(X[i]);
			print ManageOutput(SubBlocks(X[i]));
		end if;
		if (freq[i] eq max) then 
			v_max:=v_max cat [i];
			print SubBlocks(X[i]);
			print ManageOutput(SubBlocks(X[i]));
			end if;
	end for;

	return v_min, v_max;
end function;
