/* FUNZIONI AUSILIARIE */

SetNthreads(16);

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
		Append(~out, a[(i-1)*4+1..(i-1)*4+4]);
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
	Set:={0..15};
	perm_s:=SymmetricGroup(Set)! (0,14)(1,4,2,13,9,10,6,11,12,5,15,7,8,3);
	out:=[];
	for i in [1..#S] do
		out:=out cat IntToSeqPadding(Seqint(S[i],2)^perm_s,2,4);
	end for;
	return out;
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// inversa della SBox, input e output come Sbox
function SBox_i(S)
	Set:={0..15};
	perm_is:=SymmetricGroup(Set)! (0,14)(1,4,2,13,9,10,6,11,12,5,15,7,8,3);
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
/* ATTACCO */
KeySpace:={@ x : x in Subsequences({0,1}, 8)@}; // indexed set dei possibili nibbles 4 e 2 per la chiave K[5], variabile globale :(

//input due plaintext e ciphertext come stringhe esadecimali, KeySpace delle possibili chiavi parziali di 8 bit
// output sequenza di 2^8 bit che ha al posto i-esimo il valore della eq5 per la 2-nibble-chiave i-esima  
function Attack(P,C)
	P:=ManageInput(P);
	P:=(P[12]+P[10]+P[9]) mod 2; // seleziono i bit di P correlati
	C:=ManageInput(C);
	C:=SubBlocks(C);
	C:=C[1] cat C[3]; // seleziono il 4 ed il 2 nibble più significativo di C
	//X:={@x : x in Subsequences({0,1}, 8)@}; // genero tutti i possibili nibbles 4 e 2 per la chiave K[5]
	eq5:=[]; // eq5[i] conterrà il valore di eq5 per la i-esima chiave
	for k in KeySpace do
		pC:=Bitwise_sum(C,k); // somma con la chiave
		pC:=usa_SBox_i(pC); // inverto SBox
 		Append( ~eq5, (pC[1][1]+pC[1][3]+pC[2][1]+pC[2][3]+P) mod 2 );//selelziono i bit del cifrato parziale (C+random key) correlati
	end for;
return eq5;
end function;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// input numero di random coppie plaintext ciphertext cifrati con la stessa chiave utilizzate per l'attacco
// stampa i nibbles 2 e 4 della chiave di round 5 più probabili usati per la cifratura
procedure run_Attack(n)
    M:={ Q cat W cat R cat T : Q,W,R,T in {"0","1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F"} };//spazio plaintext
	N:=RandomSubset(M, n);
	K:=[Random(M): i in [1..5]]; // genero una chiave random
	freq:=Matrix(1, 2^8, [0 : i in [1..2^8]]); // inizializzo vettore delle frequenze
	for P in N do
		C:=Encryption(P,K);
		freq:=freq + Matrix(1, 2^8, Attack(P,C)); // 2^8 è # spazio delle chiavi ridotte=dim sequenza output di Attack	
	end for;
	freq:=Eltseq(freq); // need by Min, Max
	min, p_min:=Min(freq);
	max, p_max:=Max(freq);
	if ( (0.5 - min/n ) ge (max/n - 0.5) ) then // bias maggiore 
		target:=min; 
		key:=p_min;
	else 
		target:=max;
		key:=p_max;
	end if;
	key:=ManageOutput(SubBlocks(KeySpace[key]));
	print "Nibbles 2 e 4 trovati, con bias", Abs( 0.5 - target/n ), " : ", key[1], " ", key[2];
	print "Nibbles corretti:", K[5][2], "  ", K[5][4], ",  bias teorico ", 1.0/32.0 ; 
end procedure;

// input il numero di coppie che si vogliono usare per l'attacco ed il numero di volte che si vuole iterare il test
// stampa il risultato di run_Attack per i parametri in ingresso
procedure Test(n_plaintext, n_iter)
	for i in [1..n_iter] do
		time run_Attack(n_plaintext);
	end for;
end procedure;

//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

//input due plaintext e ciphertext come stringhe esadecimali, KeySpace delle possibili chiavi parziali di 8 bit
// output sequenza di 2^8 bit che ha al posto i-esimo il valore della eq5 per la 2-nibble-chiave i-esima  
function Attack_diff(P1, C1, P2, C2)
	P1:=ManageInput(P1);
	P2:=ManageInput(P2);
	C1:=ManageInput(C1);
	C2:=ManageInput(C2);
	C1:=SubBlocks(C1);
	C2:=SubBlocks(C2);
	C1:=C1[1] cat C1[3]; // seleziono il 4 ed il 2 nibble più significativo di C
	C2:=C2[1] cat C2[3];
	freq:=Matrix(1,2^8, [0: i in [1..2^8]]);
	key_index:=1;
	for k in KeySpace do
		pC1:=Bitwise_sum(C1,k); // somma con la chiave
		pC2:=Bitwise_sum(C2,k);
		pC1:=usa_SBox_i(pC1); // inverto SBox
		pC1:=pC1[1] cat pC1[2];
		pC2:=usa_SBox_i(pC2); // inverto SBox
		pC2:=pC2[1] cat pC2[2];
		delta:=Bitwise_sum(pC1,pC2);
		if delta eq [ 0, 1, 1, 0, 0, 1, 1, 0 ] then // nibbles 6 6
			freq[1][key_index]:=1;
		end if;
		key_index:=key_index+1;
	end for;
return freq;
end function;




// input numero di random coppie plaintext ciphertext cifrati con la stessa chiave utilizzati per l'attacco
// stampa i nibbles 2 e 4 della chiave di round 5 più probabili usati per la cifratura
procedure run_Attack_diff(n)
    M:={ Q cat W cat R cat T : Q,W,R,T in {"0","1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F"} };//spazio plaintext
	N:=RandomSubset(M, n); // insieme di plaintext per attaccante
	K:=[Random(M): i in [1..5]]; // genero una chiave random
	delta_p:="0B00";
	freq_tot:=Matrix(1, 2^8, [0 : i in [1..2^8]]); // inizializzo vettore delle differenze
	for P1 in N do
		P2:=Bitwise_sum(ManageInput(P1), ManageInput(delta_p));
		P2:=ManageOutput(SubBlocks(P2));
		C1:=Encryption(P1,K);
		C2:=Encryption(P2,K);
		freq_tot:=freq_tot+Attack_diff(P1,C1,P2,C2);
	end for;
	freq_tot:=Eltseq(freq_tot); // need by min max
	max, p_max:=Max(freq_tot);
	key:=ManageOutput(SubBlocks(KeySpace[p_max]));
	print "Frequenza ", max, " Nibbles trovati ", key[1], " ", key[2];	
	print "Nibbles corretti:", K[5][2], "  ", K[5][4]; 
	print Sort(freq_tot);

end procedure;



procedure Test_diff(n_plaintext, n_iter)
	for i in [1..n_iter] do
		time run_Attack_diff(n_plaintext);
	end for;
end procedure;