load("./divtrail.sage")
load("./MILP_function.sage")
load("./aux_function.sage")

def genBaseModel(rMax, MC, P, ANFSin, ANFS, ANFSout,name="model"):
	"""
	Return the base model (i.e. without the initial division property constraints) for the AES-like block cipher using :
	- rMax rounds
	- a round function of the form (MC o P o S) with :
		- S an Sbox layer, with an Sbox of size n
		- P a permutation over the whole state, given as a list
		- MC a MixColumn layer, using the matrix MC, given over GF(2^n)
		  ==/!\== This matrix should be binary (for now) ==/!\==

	- ANFSin as the ANF of the Sbox for the first layer
	- ANFSout as the ANF of the Sbox for the last layer
	- ANFS as the ANF of the Sbox for every other layers
	- name as the name of the model/block cipher
	"""

	m = Model(name)
	n = ANFS[0].parent().n_variables() #Size of the Sbox
	bs = n*len(P)
	nbSbox = bs//n #Number of Sbox
	s = MC.nrows()
	nbcol = nbSbox//s
	irred = list(PolynomialRing(GF(2),"x").irreducible_element(n))

	# print "n = " + str(n)
	# print "bs = " + str(bs)
	# print "nbSbox = " + str(nbSbox)
	# print "s = " + str(s)
	# print "nbcol = " + str(nbcol)

	M = expandMatrix(MC, irred)
	# print M
	expandP = [0 for i in range(bs)]
	for isbox in range(nbSbox):
		for j in range(n):
			expandP[isbox*n+j] = P[isbox]*n+j
	# print expandP

	#Generate the inequalities for the first S-box
	divTable_Sin = SboxDivTrailTable(ANFSin)
	ineq_Sin = sboxReducedInequalities(divTable_Sin)

	#Generate the inequalities for the standard S-box
	divTable_S = SboxDivTrailTable(ANFS)
	ineq_S = sboxReducedInequalities(divTable_S)

	#Generate the inequalities for the last S-box
	divTable_Sout = SboxDivTrailTable(ANFSout)
	ineq_Sout = sboxReducedInequalities(divTable_Sout)


	#Prepare the different lists of variables
	#list x for the input of each round (x[0] : input of the first round, x[rMax] : ciphertext)
	x = [[m.addVar(vtype=GRB.BINARY, name="x_"+str(r)+"_"+str(j)) for j in range(bs)] for r in range(rMax+1)]

	#list y for the output of the Sbox
	y = [[m.addVar(vtype=GRB.BINARY, name="y_"+str(r)+"_"+str(j)) for j in range(bs)] for r in range(rMax)]

	m.update()



	#Modelize the Sbox layer i.e. x[r] -> y[r]
	#First layer, using Sin
	r = 0
	for j in range(nbSbox):
		inputvar = [x[r][n*j+i] for i in range(n)]
		outputvar = [y[r][n*j+i] for i in range(n)]
		addSboxConstr(m, ineq_Sin, inputvar, outputvar)
	#Middle layers, using S
	for r in range(1,rMax-1):
		for j in range(nbSbox):
			inputvar = [x[r][n*j+i] for i in range(n)]
			outputvar = [y[r][n*j+i] for i in range(n)]
			addSboxConstr(m, ineq_S, inputvar, outputvar)
	#Last layer, using Sout
	r = rMax-1
	for j in range(nbSbox):
		inputvar = [x[r][n*j+i] for i in range(n)]
		outputvar = [y[r][n*j+i] for i in range(n)]
		addSboxConstr(m, ineq_Sout, inputvar, outputvar)


	#Modelize the linear layer y[r] -> x[r+1]
	D = [[sig + i*n for i in range(s)] for sig in range(n)]
	# print D
	for r in range(rMax):
		#First reorder the variables y[r] according to P
		Py = [0 for i in range(bs)]
		for i in range(bs):
			Py[expandP[i]] = y[r][i]

		for col in range(nbcol):
			z = Py[col*n*s:(col+1)*n*s]
			for t in range(1,s):
				for sig in range(n):
					for seti in Combinations(D[sig],t):
						Lexpr = quicksum(-x[r+1][col*n*s+i] for i in seti)
						for k in range(n*s):
							a = GF(2)(0)
							for i in seti:
								a += M[i][k]
							Lexpr += int(a)*z[k]
						m.addConstr(Lexpr >= -(t-1))

			for i in range(n):
				m.addConstr(quicksum(z[i+k*n] for k in range(s)) == quicksum(x[r+1][col*n*s+i+k*n] for k in range(s)))


	

	#Set the objective
	m.setObjective(quicksum([x[rMax][i] for i in range(bs)]), GRB.MINIMIZE)

	return (m,x,y)

def addFirstRoundSboxOutput(m,x,MC,P,init):
	"""
	Add constraints to the model m to modelize half a round before the first one, so that we can set the output of the Sbox layer to init
	m : the model
	x : the x-variables of the model
	MC : the MixColumn matrix
	P : the permutation for ShiftRows
	init : 0-1 list representing the div.prop. we want
	"""

	#Add some new variable to modelize half a round before the first one
	bs = len(init)
	nbSbox = len(P)
	n = bs//nbSbox
	s = MC.nrows()
	nbcol = nbSbox//s
	irred = list(PolynomialRing(GF(2),"x").irreducible_element(n))

	M = expandMatrix(MC, irred)
	expandP = [0 for i in range(bs)]
	for isbox in range(nbSbox):
		for j in range(n):
			expandP[isbox*n+j] = P[isbox]*n+j

	yi = [m.addVar(vtype=GRB.BINARY, name="yi_"+str(j)) for j in range(bs)]
	for j in range(bs):
		m.addConstr(yi[j] == init[j])

	D = [[sig + i*n for i in range(s)] for sig in range(n)]

	#So we want to modelize the transition yi -> x[0]
	#First reorder the variables y[r] according to P
	Py = [0 for i in range(bs)]
	for i in range(bs):
		Py[expandP[i]] = yi[i]

	for col in range(nbcol):
		z = Py[col*n*s:(col+1)*n*s]
		for t in range(1,s):
			for sig in range(n):
				for seti in Combinations(D[sig],t):
					Lexpr = quicksum(-x[0][col*n*s+i] for i in seti)
					for k in range(n*s):
						a = GF(2)(0)
						for i in seti:
							a += M[i][k]
						Lexpr += int(a)*z[k]
					m.addConstr(Lexpr >= -(t-1))

		for i in range(n):
			m.addConstr(quicksum(z[i+k*n] for k in range(s)) == quicksum(x[0][col*n*s+i+k*n] for k in range(s)))


def searchDivProp(rMax, MC, P, ANFSin, ANFS, ANFSout, init, name="model"):
	"""
	Search for a distinguisher using:
	- rMax rounds
	- a round function of the form (MC o P o S) with :
		- S an Sbox layer, with an Sbox of size n
		- P a permutation over the whole state, given as a list
		- MC a MixColumn layer, using the matrix MC, given over GF(2^n)
		  ==/!\== This matrix should be binary (for now) ==/!\==

	- ANFSin as the ANF of the Sbox for the first layer
	- ANFSout as the ANF of the Sbox for the last layer
	- ANFS as the ANF of the Sbox for every other layers
	- init as the initial division property (single vector)
	- name as the name of the model/block cipher
	Return (S,r) with S the set of balanced bytes and r the total runtime in the solver
	"""

	(m,x,y) = genBaseModel(rMax,MC,P,ANFSin,ANFS,ANFSout,name)
	n = len(init) #Block size

	for i in range(n):
		m.addConstr(x[0][i] == init[i])
	m.update()
	m.Params.LogToConsole = 0
	return searchDistinguisher(m)

	
def searchAllInit(rMax, MC, P, ANFSin, ANFS, ANFSout, name="model"):
	"""
	Search a distinguisher for each of the possible initial division property (single vector of weight n-1)
	- rMax rounds
	- a round function of the form (MC o P o S) with :
		- S an Sbox layer, with an Sbox of size n
		- P a permutation over the whole state, given as a list
		- MC a MixColumn layer, using the matrix MC, given over GF(2^n)
		  ==/!\== This matrix should be binary (for now) ==/!\==

	- ANFSin as the ANF of the Sbox for the first layer
	- ANFSout as the ANF of the Sbox for the last layer
	- ANFS as the ANF of the Sbox for every other layers
	- name as the name of the model/block cipher
	"""
	fullruntime = 0
	n = ANFS[0].parent().n_variables()*len(P) #size of the Sbox * number of Sboxes
	for i0 in range(n):
		init = [1 for _ in range(n)]
		init[i0] = 0

		print "Init div " + str(i0)
		(L,totalruntime) = searchDivProp(rMax,MC,P,ANFSin,ANFS,ANFSout,init,name)
		fullruntime += totalruntime
		if len(L) == 0:
			print "No balanced bytes" + "(" + ("%.2f" % totalruntime) + "s," + ("%.2f" % fullruntime) + " total time)"
		else:
			print "!! " + str(len(L)) + " balanced bytes : " + str(L) + "(" + ("%.2f" % totalruntime) + "s," + ("%.2f" % fullruntime) + " total time)"


def testLinIn(ANFS):
	"""Bunch of tests for ANFS o M where M is a linear map"""

	n = ANFS[0].parent().n_variables()

	
	nbmat = 0
	nbgoodmatrix = 0

	#mapSetTrans[k] will contain the set of all possible K where k -> K is a possible transition
	mapSetTrans = dict()
	for k in vectorF2n(n):
		mapSetTrans[k] = set()

	setCols = set() 
	#Don't check matrices that have the same set of columns (without considering the order)
	# as they will give an equivalent div. table
	set223 = set()
	set233 = set()
	set23 = set()
	nbnot233 = 0
	mapNb2 = dict()
	mapNb3 = dict()

	setDivTableFull1 = set()
	listDivTableFull1 = []
	listLinFull1 = []

	# MS = MatrixSpace(GF(2),n,n)
	# for M in MS:
	# 	nbmat += 1
	# 	if M.is_invertible()and FrozenMultiset(M.columns()) not in setCols:
	# 		setCols.add(FrozenMultiset(M.columns()))

	MS = load("matrix_4x4_input.sobj")
	nbM = len(MS)
	for M in MS:
		nbgoodmatrix+=1

		sys.stderr.write(str(nbgoodmatrix) + "/" + str(nbM) + "\r")
		sys.stderr.flush()

		newANF = composeLinIn(ANFS,M)
		D = SboxDivTrailTable(newANF)

		fullone = True
		nb2 = 0
		nb3 = 0
		for x in D:
			Dx = D[x]
			Dx.sort()
			mapSetTrans[x].add(tuple(Dx))
			Ls = [sum(xx) for xx in Dx]
			Ls.sort()

			if Ls == [2,2,3]:
				set223.add(tuple(Dx))
			if Ls == [2,3,3]:
				set233.add(tuple(Dx))
			if Ls == [2,3]:
				set23.add(tuple(Dx))

			for s in Ls:
				if s == 2 or s == 3:
					fullone = False

			nb2 += Ls.count(2)
			nb3 += Ls.count(3)

		if fullone:

			knowD = False
			kD = D.keys()
			kD.sort()
			L = []
			for k in kD:
				L.append( tuple([tuple(k)] + [tuple(dk) for dk in D[k]]) )
			L = tuple(L)
			for oldD in setDivTableFull1:
				if L == oldD:
					knowD = True
					break

			if not knowD:
				setDivTableFull1.add(L)
				listDivTableFull1.append(D)
				listLinFull1.append(M)

		if nb2 in mapNb2:
			mapNb2[nb2] += 1
		else:
			mapNb2[nb2] = 1

		if nb3 in mapNb3:
			mapNb3[nb3] += 1
		else:
			mapNb3[nb3] = 1

			

			
	print "Reachable sets from an input of weight 3 :"
	V = vectorF2n(n)
	V = [v for v in V if sum(v) == 3]
	setK_w3 = set()
	for v in V:
		for sety in mapSetTrans[v]:
			sy = list(sety)
			sy.sort(cmpvec)
			setK_w3.add(tuple(sy))
	for sy in setK_w3:
		s = "{" + "".join([str(yy) for yy in sy[0]])
		for i in range(1,len(sy)):
			s += "," + "".join([str(yy) for yy in sy[i]])
		s += "} "
		print s
	print "------------------------------------"
	print "With a linear map on the input :"
	print "Possible transitions :"
	mapWeightTrans = dict()
	for k in vectorF2n(n):
		mapWeightTrans[k] = set()
	Lx = mapSetTrans.keys()
	Lx.sort(cmpvec)
	for x in Lx:
		s = "".join([str(xx) for xx in x])
		s += " : "
		for sety in mapSetTrans[x]:
			sy = list(sety)
			sy.sort(cmpvec)
			mapWeightTrans[x].add(tuple([sum(y) for y in sy]))
			s += "{" + "".join([str(yy) for yy in sy[0]])
			for i in range(1,len(sy)):
				s += "," + "".join([str(yy) for yy in sy[i]])
			s += "} "
		print s
	print "------------------------------------"
	print "Possible transitions (weight only) :"
	for x in Lx:
		s = "".join([str(xx) for xx in x])
		s += " : "
		Lwy = list(mapWeightTrans[x])
		Lwy.sort()
		for wy in Lwy:
			s += "".join([str(yy) for yy in wy])
			s += " "
		print s
	print "------------------------------------"
	print "Possible sets 223 at the start : "
	for K in set223:
		s = ""
		for k in K:
			s += "".join(str(kk) for kk in k)
			s += " "
		print s
	print "Possible sets 233 at the start : "
	for K in set233:
		s = ""
		for k in K:
			s += "".join(str(kk) for kk in k)
			s += " "
		print s

	print "Possible sets 23 at the start : "
	for K in set23:
		s = ""
		for k in K:
			s += "".join(str(kk) for kk in k)
			s += " "
		print s
	print "------------------------------------"
	print "(w : n) = Number n of mappings that have a total number of w vectors of weight 2"
	kmapNb2 = mapNb2.keys()
	kmapNb2.sort()
	for k in kmapNb2:
		print str(k) + " : " + str(mapNb2[k])
	print "------------------------------------"
	print "(w : n) = Number n of mappings that have a total number of w vectors of weight 3"
	kmapNb3 = mapNb3.keys()
	kmapNb3.sort()
	for k in kmapNb3:
		print str(k) + " : " + str(mapNb3[k])
	print "------------------------------------"
	print "Possibles Div Tables with only weight 1 vectors"
	for D in listDivTableFull1:
		printDivTable(D)
		print "------------------------------------"
	print str(len(setDivTableFull1)) + " total different tables"
	print "===================================="
	print nbgoodmatrix
	return (setK_w3,listLinFull1,listDivTableFull1)


def testLinOut(ANFS):
	"""Bunch of tests for M o ANFS where M is a linear map"""

	n = ANFS[0].parent().n_variables()

	
	nbmat = 0

	#mapSetTrans[k] will contain the set of all possible K where k -> K is a possible transition
	mapSetTrans = dict()
	for k in vectorF2n(n):
		mapSetTrans[k] = set()

	mapSet1 = dict()
	#mapSet1[w] wll contains all vectors of weight 1 which will always be in the output set if all vectors of weight w are in the input set
	for w in range(n+1):
		mapSet1[w] = set(vectorF2n(n))

	setRows = set() 

	set223 = set()
	set2223 = set()
	set233 = set()
	set23 = set()
	mapNb1 = dict()
	setDivTable51_1 = set()
	listDivTable51_1 = []
	listLin51_1 = []

	#Don't check matrices that have the same set of rows (without considering the order)
	# as they will give an equivalent div. table
	# MS = MatrixSpace(GF(2),n,n)
	# for M in MS:
	# 	nbmat += 1
	# 	if M.is_invertible() and FrozenMultiset(M.rows()) not in setRows:
	# 		setRows.add(FrozenMultiset(M.rows()))
	MS = load("matrix_4x4_output")
	nbM = len(MS)
	for M in MS:
		nbmat += 1
		sys.stderr.write(str(nbmat) + "/" + str(nbM) + "\r")
		sys.stderr.flush()

		newANF = composeLinOut(ANFS,M)
		D = SboxDivTrailTable(newANF)

		for x in D:
			D[x].sort()

		localSet1 = dict()
		for w in range(n+1):
			localSet1[w] = set()

		nb1 = 0
		for x in D:
			Dx = D[x]
			Dx.sort()
			mapSetTrans[x].add(tuple(Dx))
			for y in Dx:
				localSet1[sum(x)].add(y)
			Ls = [sum(xx) for xx in Dx]
			Ls.sort()
			if Ls == [2,2,3]:
				set223.add(tuple(Dx))
			elif Ls == [2,2,2,3]:
				set2223.add(tuple(Dx))
			elif Ls == [2,3,3]:
				set233.add(tuple(Dx))
			elif Ls == [2,3]:
				set23.add(tuple(Dx))

			nb1 += Ls.count(1)

		for w in range(n+1):
			Lrem = []
			for y in mapSet1[w]:
				if y not in localSet1[w]:
					Lrem.append(y)
			for y in Lrem:
				mapSet1[w].remove(y)

		if nb1 in mapNb1:
			mapNb1[nb1] += 1
		else:
			mapNb1[nb1] = 1

		if nb1 == 51:
			knowD = False
			kD = D.keys()
			kD.sort()
			L = []
			for k in kD:
				L.append( tuple([tuple(k)] + [tuple(dk) for dk in D[k]]) )
			L = tuple(L)
			for oldD in setDivTable51_1:
				if L == oldD:
					knowD = True
					break

			if not knowD:
				setDivTable51_1.add(L)
				listDivTable51_1.append(D)
				listLin51_1.append(M)

				sys.stdout.write("                   \r")
				print M
				printDivTable(D)
				print "------------------------------------"

				

				


	print "With a linear map on the output :"
	print "Possible transitions :"
	mapWeightTrans = dict()
	mapAlways = dict()
	for k in vectorF2n(n):
		mapWeightTrans[k] = set()
		mapAlways[k] = []
	Lx = mapSetTrans.keys()
	Lx.sort(cmpvec)

	for x in Lx:
		s = "".join([str(xx) for xx in x])
		s += " : "
		for sety in mapSetTrans[x]:
			sy = list(sety)
			sy.sort(cmpvec)
			mapWeightTrans[x].add(tuple([sum(y) for y in sy]))
			s += "{" + "".join([str(yy) for yy in sy[0]])
			for i in range(1,len(sy)):
				s += "," + "".join([str(yy) for yy in sy[i]])
			s += "} "
		print s

		for y in list(mapSetTrans[x])[0]:
			always = True
			for sety in mapSetTrans[x]:
				if y not in sety:
					always = False
					break
			if always:
				mapAlways[x].append(y)


	print "------------------------------------"
	print "Possible transitions (weight only) :"
	for x in Lx:
		s = "".join([str(xx) for xx in x])
		s += " : "
		Lwy = list(mapWeightTrans[x])
		Lwy.sort()
		for wy in Lwy:
			s += "".join([str(yy) for yy in wy])
			s += " "
		print s

	print "------------------------------------"
	print "Vectors that are always present : "
	printDivTable(mapAlways)

	print "------------------------------------"
	print "If all vectors of weight w are in the input set, then the following vectors will always be in the output set : "
	for w in range(n+1):
		s = str(w) + " : "
		for y in mapSet1[w]:
			s += "".join([str(yy) for yy in y])
			s += " "
		print s
	print "------------------------------------"
	print "Possible sets 223 at the end : "
	for K in set223:
		s = ""
		for k in K:
			s += "".join(str(kk) for kk in k)
			s += " "
		print s

	print "Possible sets 2223 at the end : "
	for K in set2223:
		s = ""
		for k in K:
			s += "".join(str(kk) for kk in k)
			s += " "
		print s

	print "Possible sets 233 at the end : "
	for K in set233:
		s = ""
		for k in K:
			s += "".join(str(kk) for kk in k)
			s += " "
		print s

	print "Possible sets 23 at the end : "
	for K in set23:
		s = ""
		for k in K:
			s += "".join(str(kk) for kk in k)
			s += " "
		print s
	print "------------------------------------"
	print "(w : n) = Number n of mappings that have a total number of w vectors of weight 1"
	kmapNb1 = mapNb1.keys()
	kmapNb1.sort()
	for k in kmapNb1:
		print str(k) + " : " + str(mapNb1[k])
	print "===================================="
	print str(len(setDivTable51_1)) + " total differents div tables"

	return (listLin51_1,listDivTable51_1)

def expandMatrix(M, modulus=[1,1,0,1,1,0,0,0,1]):
	"""
	Expand the matrix M given on GF(2)[X]/modulus over GF(2)
	M is given as a matrix/double list of integer, no need to coerce it to the actual field
	The modulus is given as a list of coefficient, in ascending degree order
	(i.e. what would be obtained with p.coefficients(sparse=False) where p is a Sage Polynomial)
	e.g : p = x^8 + x^4 + x^3 + x + 1 <=> modulus = [1, 1, 0, 1, 1, 0, 0, 0, 1]
	"""

	deg_mod = len(modulus)-1

	#Precomptuation of the matrices for multiplication by x^i
	#Matrix for multiplication by x
	Mx = Matrix(GF(2),deg_mod, deg_mod)
	#First subdiagonal set to 1
	for j in range(1,deg_mod):
		Mx[j,j-1] = 1
	#Last column set to the coefficients of the modulus
	for j in range(deg_mod):
		Mx[j,deg_mod-1] = modulus[j]

	#Compute each Mxi = matrix of the multiplication by x^i
	L_Mxi = [0 for i in range(deg_mod)]
	L_Mxi[0] = identity_matrix(GF(2),deg_mod)
	for i in range(1,deg_mod):
		L_Mxi[i] = Mx*L_Mxi[i-1]



	#Precomputation for the matrix conversion
	# multMatrix[a] will contains the matrix representing the multiplication of an element by a € GF(2^m) at a bit level
	multMatrix = dict()
	#Get the set of all coefficient appearing in M
	set_coeff = set([int(M[i][j]) for j in range(M.ncols()) for i in range(M.nrows())])
	#Compute each multiplication matrix we will need
	for a in set_coeff:
		Ma = matrix(GF(2),deg_mod,deg_mod)
		for b in range(deg_mod):
			if (a >> b) & 1:
				Ma += L_Mxi[b]
		multMatrix[a] = Ma

	#Now we can convert the diffusion matrix M on GF(2^m) to a matrix Mbit on GF2
	Mbit = matrix(GF(2), 0, M.nrows()*deg_mod)
	for i in range(M.nrows()):
		Mrow = matrix(GF(2), deg_mod, 0)
		for j in range(M.ncols()):
			Mrow = Mrow.augment(multMatrix[M[i][j]])
		Mbit = Mbit.stack(Mrow)

	return Mbit


def compactMatrixPrint(M,space=0):
	"""
	Compact printing of the matrix M, putting a space every "space" coefficient (0 = no space)
	"""
	for i in range(M.nrows()):
		s = ""
		for j in range(M.ncols()):
			s += str(M[i][j])
			if space != 0 and (j+1)%space == 0:
				s += " "
		print s

