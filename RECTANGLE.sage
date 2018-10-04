#RECTANGLE
load("./aux_function.sage")
load("genModelBC.sage")

def RECTANGLE_model(rMax, ANFSin, ANFS, ANFSout):
	"""
	Generate a MILP model for RECTANGLE over rMax rounds using :
	- ANFSin as the ANF of the S-box of the first round
	- ANFSout as the ANF of the S-box of the last round
	- ANFS as the S-box for all other rounds
	"""

	#Generate the inequalities for the first S-box
	divTable_Sin = SboxDivTrailTable(ANFSin)
	ineq_Sin = sboxReducedInequalities(divTable_Sin)

	#Generate the inequalities for the standard S-box
	divTable_S = SboxDivTrailTable(ANFS)
	ineq_S = sboxReducedInequalities(divTable_S)

	#Generate the inequalities for the last S-box
	divTable_Sout = SboxDivTrailTable(ANFSout)
	ineq_Sout = sboxReducedInequalities(divTable_Sout)


	m = Model("RECTANGLE")
	x = [[[m.addVar(vtype=GRB.BINARY,name="x_"+str(r)+"_"+str(i)+"_"+str(j)) for j in range(16)] for i in range(4)] for r in range(rMax+1)]

	for r in range(rMax):
		#Modelize both the Sbox and the linear layer at the same time
		#x[r] -> x[r+1]
		m.update()
		#First reorder the variables of x[r+1] according to the inverse of the permutation
		xrp1 = x[r+1]
		xrp1[1] = xrp1[1][1:] + xrp1[1][:1]
		xrp1[2] = xrp1[2][12:] + xrp1[2][:12]
		xrp1[3] = xrp1[3][13:] + xrp1[3][:13]


		#Then add the constraints from the Sbox
		for j in range(16):
			inputvar = [x[r][i][j] for i in range(4)]
			outputvar = [xrp1[i][j] for i in range(4)]
			if r == 0:
				addSboxConstr(m, ineq_Sin, inputvar, outputvar)
			elif r == rMax-1:
				addSboxConstr(m, ineq_Sout, inputvar, outputvar)
			else:
				addSboxConstr(m, ineq_S, inputvar, outputvar)

		#And reorder back the variables for the next round
		xrp1[1] = xrp1[1][-1:] + xrp1[1][:-1]
		xrp1[2] = xrp1[2][-12:] + xrp1[2][:-12]
		xrp1[3] = xrp1[3][-13:] + xrp1[3][:-13]

		

	m.setObjective(quicksum([x[rMax][i][j] for j in range(16) for i in range(4)]), GRB.MINIMIZE)
	m.update()
	return (m,x)

def RECTANGLE_searchDistinguisher(rMax,ANFSin,ANFS,ANFSout,init):
	"""
	Search for a distinguisher over rMax rounds using initial division property init, using :
	- ANFSin as the ANF of the S-box of the first round
	- ANFSout as the ANF of the S-box of the last round
	- ANFS as the S-box for all other rounds
	Return a pair (K,r) where K is the set of balanced bits and r the total runtime
	"""

	(m,x) = RECTANGLE_model(rMax,ANFSin,ANFS,ANFSout)

	#Now add the constrains for the initial division property
	for i in range(4):
		for j in range(16):
			m.addConstr(x[0][i][j] == init[16*i+j])

	m.update()
	m.Params.OutputFlag = 0
	return searchDistinguisher(m)

def RECTANGLE_searchAllInit(rMax,ANFSin,ANFS,ANFSout):
	"""
	Search for a distinguisher over rMax rounds, going through all initial division property of weight 63, using :
	- ANFSin as the ANF of the S-box of the first round
	- ANFSout as the ANF of the S-box of the last round
	- ANFS as the S-box for all other rounds
	"""
	fullruntime = 0
	for i0 in range(64):
		init = [1 for _ in range(64)]
		init[i0] = 0
		print "Init div " + str(i0)
		(L,totalruntime) = RECTANGLE_searchDistinguisher(rMax,ANFSin,ANFS,ANFSout,init)
		fullruntime += totalruntime
		if len(L) == 0:
			print "No balanced bits" + "(" + ("%.2f" % totalruntime) + "s," + ("%.2f" % fullruntime) + " total time)"
		else:
			print "!! " + str(len(L)) + " balanced bits : " + str(L) + "(" + ("%.2f" % totalruntime) + "s," + ("%.2f" % fullruntime) + " total time)"


#----New distinguisher over 10 rounds ----
def newRECTANGLEDistinguisher10r():
	"""
	Check the new distinguisher over 10 rounds using the extension technique
	"""
	S = [0x6,0x5,0xc,0xa,0x1,0xe,0x7,0x9,0xb,0x0,0x3,0xd,0x8,0xf,0x4,0x2]
	(P,ANFS) = SBOX_ANF(S)

	#Has a transition 1101 -> 0101 1110
	Min = matrix(GF(2),[[1,0,0,0],[0,1,1,0],[0,1,0,0],[0,0,0,1]])
	ANFSin = composeLinIn(ANFS,Min)

	init = [1 for _ in range(64)]
	init[32] = 0

	(K,runtime) = RECTANGLE_searchDistinguisher(10,ANFSin,ANFS,ANFS,init)
	print ""
	print "Balanced bits : " + " ".join([v for v in K])


#----(old) Best known distinguisher over 9 rounds ---
def oldRECTANGLEDistinguisher9r():
	"""
	Check the old best known distinguisher over 9 rounds
	"""
	S = [0x6,0x5,0xc,0xa,0x1,0xe,0x7,0x9,0xb,0x0,0x3,0xd,0x8,0xf,0x4,0x2]
	(P,ANFS) = SBOX_ANF(S)

	init = [1 for _ in range(64)]
	for i in range(4):
		init[16*i+15] = 0
	(K,runtime) = RECTANGLE_searchDistinguisher(9,ANFS,ANFS,ANFS,init)
	print ""
	print "Balanced bits : " + " ".join([v for v in K])

def twkRECTANGLEDistinguisher8r():
	"""Check the 8 rounds distinguisher over 8 rounds on the variant of RECTANGLE"""

	#This Sbox is obtained from the original S-box S' of RECTANGLE, using S = B o S' o A with
	# A = [[1,1,0,0],[1,0,1,0],[1,0,0,1],[0,1,0,0]]
	# B = [[1,0,1,0],[0,1,1,0],[0,0,1,0],[0,0,0,1]]
	S = [5, 9, 0, 7, 15, 13, 14, 8, 1, 10, 12, 3, 4, 6, 2, 11]
	print "Using S-box " + str(S)
	Lin = matrix(GF(2),[[1,0,0,0],[0,1,0,0],[0,0,1,1],[0,0,1,0]])
	Lout = matrix(GF(2),[[1,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,1]])
	(P,ANFS) = SBOX_ANF(S)
	ANFSin = composeLinIn(ANFS,Lin)
	ANFSout = composeLinOut(ANFS,Lout)

	#input transition on S-box 0, 1110 -> 01101, 1110
	init = [1 for _ in range(64)]
	init[48] = 0 #Sboxes are on columns of the state
	(K,r) = RECTANGLE_searchDistinguisher(8,ANFSin,ANFS,ANFSout,init)
	print ""
	print "Balanced bits : x_r_i_j = bit of round r, row i, column j " 
	print K

def twkRECTANGLE9r_check():
	"""
	Check that the variant of RECTANGLE does not have a 9 round distinguisher in classical search
	First it shows that using the original S-box, we do have a distinguisher over 9 rounds
	Then, using the variant's S-box, it shows that none of the possible initial division property lead to a distinguisher
	"""

	#Using S lead to a distinguisher over 9 rounds
	#But using S' = Lout o S o Lin lead to no distinguisher over 9 rounds
	S = [0x6,0x5,0xc,0xa,0x1,0xe,0x7,0x9,0xb,0x0,0x3,0xd,0x8,0xf,0x4,0x2]
	(P,ANFS) = SBOX_ANF(S)
	Lin = matrix(GF(2),[[1,1,0,0],[1,0,1,0],[1,0,0,1],[0,1,0,0]])
	Lout = matrix(GF(2),[[1,0,1,0],[0,1,1,0],[0,0,1,0],[0,0,0,1]] )
	ANFSin = composeLinIn(ANFS,Lin)
	ANFS2 = composeLinOut(ANFSin,Lout)
	#S2 = Lout o S o Lin should be [5, 9, 0, 7, 15, 13, 14, 8, 1, 10, 12, 3, 4, 6, 2, 11]

	#Search for a distinguisher over 9 rounds using Sbox S
	print "Using the Sbox : " + str(S)
	#There is one using the initial division property 011...1
	init = [0] + [1 for _ in range(63)]
	(K,runtime) = RECTANGLE_searchDistinguisher(9,ANFS,ANFS,ANFS,init)
	print "\nBalanced bits : " + " ".join(s for s in K)

	#Search for a distinguisher over 9 rounds using Sbox S'
	#There is none, which we can show be showing that all initial division property of weight 63 (block size - 1)
	# lead to no distinguisher
	print "\n-----------------------------------\nUsing the Sbox : " + str(evalANF(ANFS2))
	check = True
	for i in range(64):
		print "Init " + str(i)
		init = [1 for _ in range(64)]
		init[i] = 0
		(S,runtime) = RECTANGLE_searchDistinguisher(9,ANFS2,ANFS2,ANFS2,init)
		if len(S) > 0:
			check = False
		print ""
	if check:
		print "There is no distinguisher"
	else:
		print "There is a distinguisher !"


def RECTANGLE9r_check_Midori64Sbox():
	"""
	Another tweaked version of RECTANGLE using the Midori64 Sbox
	Using Midori's Sbox S lead to a distinguisher over 9 rounds
	But using S' = S o L lead to no distinguisher over 9 rounds
	"""
	S = [0xc, 0xa, 0xd, 0x3, 0xe, 0xb, 0xf, 0x7, 0x8, 0x9, 0x1, 0x5, 0x0, 0x2, 0x4, 0x6] #Midori64 Sbox
	(P,ANFS) = SBOX_ANF(S)
	L = matrix(GF(2), [[1, 0, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
	ANFS2 = composeLinIn(ANFS,S2)
	#S2 = S o L should be [12, 3, 13, 10, 14, 7, 15, 11, 8, 5, 1, 9, 0, 6, 4, 2]

	#Search for a distinguisher over 9 rounds using Sbox S
	print "Using the Sbox : " + str(S)
	#There is one using the initial division property 011...1
	init = [0] + [1 for _ in range(63)]
	(bitset,runtime) = RECTANGLE_searchDistinguisher(9,ANFS,ANFS,ANFS,init)
	print "\nBalanced bits : " + " ".join(s for s in bitset)

	#Search for a distinguisher over 9 rounds using Sbox S'
	#There is none, which we can show be showing that all initial division property of weight 63 (block size - 1)
	# lead to no distinguisher
	print "\n-----------------------------------\nUsing the Sbox : " + str(evalANF(ANFS2))
	check = True
	for i in range(64):
		print "Init " + str(i)
		init = [1 for _ in range(64)]
		init[i] = 0
		(K,runtime) = RECTANGLE_searchDistinguisher(9,ANFS2,ANFS2,ANFS2,init)
		if len(K) > 0:
			check = False
		print ""
	if check:
		print "There is no distinguisher"
	else:
		print "There is a distinguisher !"
