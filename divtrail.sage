
from sage.crypto.boolean_function import BooleanFunction
import sys
from multiset import *

def SBOX_ANF(SBOX):
	"""
	Given a list SBOX of 2^n value
	return (P, y) where
	y is a list of n ANF for each output coordinate
	P is a common BooleanPolynomialRing for all element of y
	"""

	#size of the sbox
	n = max([x.nbits() for x in SBOX])

	#Get the bit representation of each value
	SBOX_bits = [x.bits() + [0 for i in range(n-len(x.bits()))] for x in SBOX]

	#Create the boolean function corresponding to each bit of the output from its truth table
	#i.e. all bits of index i in SBOX-table for the i-th output bit
	B = [ BooleanFunction([x[i] for x in SBOX_bits]) for i in range(n)]

	#Set a common BooleanPolynomialRing for each output function
	y0 = B[0].algebraic_normal_form()
	P = y0.ring()
	x = P.gens()

	#Compute the ANF of each output bit
	y = [P(b.algebraic_normal_form()) for b in B]

	return (P, y)

def greater(a,b):
	#return True if a[i] >= b[i] for all i
	#False otherwise
	for i in range(len(a)):
		if a[i] < b[i]:
			return False
	return True

def SboxDivTrail(y, k):
	"""
	input : 
	- y list of BooleanPolynomial representing the output ANF of the SBox
	- k the input division property
	output :
	 K the set of output division property
	"""

	n = len(k)
	P = y[0].ring()
	x = P.gens()

	S = set()
	for e in range(2^n):
		kbar = Integer(e).bits() + [0 for i in range(n-Integer(e).nbits())]
		if greater(kbar, k):
			S.add(tuple(kbar))

	F = set()
	for kbar in S:
		F.add(P(prod([x[i] for i in range(n) if kbar[i] == 1])))

	Kbar = set()

	for e in range(2^n):
		u = Integer(e).bits() + [0 for i in range(n-Integer(e).nbits())]
		puy = prod([y[i] for i in range(n) if u[i] == 1])
		puyMon = P(puy).monomials()
		contains = False
		for mon in F:
			if mon in puyMon:
				contains = True
				break

		if contains:
			Kbar.add(tuple(u))

	K = []
	for kbar in Kbar:
		great = False
		for kbar2 in Kbar:
			if(kbar != kbar2 and greater(kbar, kbar2)):
				great = True
				break
		if not great:
			K.append(kbar)

	return K

def SboxDivTrailTable(y):
	"""
	Return a dict containing all possible division propagation of the SBOX, where y is a list containing the ANF of each output bits
	"""
	P = y[0].ring()
	n = P.n_variables()

	D = dict()
	for c in range(2^n):
		k = Integer(c).bits() + [0 for i in range(n-Integer(c).nbits())]
		k = tuple(k)
		D[k] = SboxDivTrail(y, k)

	return D

def cmpvec(x,y):
	if x == y:
		return int(0)
	elif sum(x) < sum(y):
		return int(-1)
	elif sum(x) == sum(y) and x > y:
		return int(-1)
	else:
		return int(1)
		
def printDivTable(D):
	Lx = D.keys()
	Lx.sort(cmpvec)

	for dx in Lx:
		s = ""
		for ex in dx:
			s+=str(ex)
		s+= " : "
		Ly = D[dx]
		Ly.sort(cmpvec)
		for dy in Ly:
			for ey in dy:
				s+= str(ey)
			s += " "
		print s	