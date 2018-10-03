#A bunch of auxiliary function used in several another files

def composeLinIn(ANFS,M):
	"""Return the ANF of ANFS o M"""
	n = ANFS[0].parent().n_variables()
	vec_x = vector(ANFS[0].parent().gens())

	Mv = M*vec_x
	s = {vec_x[i] : Mv[i] for i in range(4)}
	return [p.subs(s) for p in ANFS]

def composeLinOut(ANFS,M):
	"""Return the ANF of M o ANFS"""
	n = ANFS[0].parent().n_variables()
	newANF = [ANFS[0].parent()(0) for i in range(n)]
	for i in range(n):
		for j in range(n):
			if(M[i][j] == 1):
				newANF[i] += ANFS[j]

	return newANF

def evalANF(ANFS):
	"""
	Given an S-box ANF, return a list S containing each evaluation i.e. S[x] = S-box(x)
	"""
	n = ANFS[0].parent().n_variables()
	xvar = ANFS[0].parent().gens()
	S = [0 for _ in range(1 << n)]
	for e in range(1 << n):
		x = Integer(e).bits() + [0 for _ in range(n-Integer(e).nbits())]
		d = {xvar[i] : x[i] for i in range(n)}
		Sx = [p.subs(d) for p in ANFS]
		vSx = 0
		b = 1
		for i in range(n):
			vSx += b*int(Sx[i])
			b = b << 1
		S[e] = vSx
	return S
