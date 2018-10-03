#MILP related function, mostly to compute the inequalities for an Sbox and the search algorithm for division property

from sage.crypto.boolean_function import BooleanFunction
from gurobipy import *
import sys

def vectorF2n(n):
	"""
	Create the list of all vector in {0,1}^n
	"""
	return [tuple(Integer(c).bits() + [0 for i in range(n-Integer(c).nbits())]) for c in range(2^n)]

def ineqRepresentation(D):
	"""
	input : a dict D such that D[k] = [k1,...,kt] where k1,...,kt are the possible division propagation from k
	output : (Lineq, A) where Lineq is a list of linear inequalities and equalities representing Conv(A)
			  and A is the list of all vector k|k1,..., k|kt etc.
			  For a given E in Lineq, E[-1] == ">=" means that it's an inequality, and E[-1] == "==" means it's an equality
	Exemple :
	the vector [1,2,3,8] represent the inequality
	1*x[0] + 2*x[1] + 3*x[2] + 8 >= 0
	"""

	#create all the vector
	A = []
	for k in D.keys():
		for k2 in D[k]:
			A.append(k+k2)

	#Create the corresponding polyhedron
	P = Polyhedron(vertices=A)

	#Get the inequalities
	#an inequality is represented as a list L of size 2n+1 (where n is the size of k)
	#the first item (i.e. L[0]) is the constant term, which is not really convenient, so we will put it at the end of the vector

	Ltmp = P.inequalities_list()
	Lineq = [l[1:] + [l[0]] for l in Ltmp]
	Lineq = [l + [">="] for l in Lineq]

	Ltmp = P.equations_list()
	Ltmp = [l[1:] + [l[0]] for l in Ltmp]
	Ltmp = [l + ["=="] for l in Ltmp]

	Lineq += Ltmp

	return(Lineq, A)

def ineqEvaluation(ineq, p):
	"""
	Return whether or not the inequality ineq is verified for point p
	ineq can also be an equation, ineq[-1] wil give the type
	"""

	if ineq[-1] == ">=":
		return sum([ineq[i]*p[i] for i in range(len(p))]) + ineq[-2] >= 0 #constant term of the inequality is at the index -2
	else:
		return sum([ineq[i]*p[i] for i in range(len(p))]) + ineq[-2] == 0


def ineqReduction(L, A):
	"""
	input : L is a list of linear inequalities representing Conv(A)
			 A is a list of points (tuples)		 
	output : a list of inequalities whose feasible solutions in {0,1}^n are A
	"""
	
	Ls = []
	n = len(A[0])

	#Create the list of all vector in {0,1}^n
	Btmp = vectorF2n(n)
	#Remove vector in A from B
	B = [b for b in Btmp if b not in A]
	Lbar = deepcopy(L)

	# print "Init"
	# print "B : " + str(B)
	# print "Lbar : " + str(Lbar)

	while(len(B) > 0):
		l = Lbar[0]
		Bs = [p for p in B if not ineqEvaluation(l, p)]

		#Get the inequality (l) in Lbar which maximize the number of points in B that do not satisfy this inequality (Bs)
		for ineq in Lbar:
			tmpBs = [p for p in B if not ineqEvaluation(ineq, p)]
			if len(tmpBs) > len(Bs):
				l = ineq
				Bs = tmpBs

		# print "Choosed to keep l = " + str(l)
		Ls.append(l)
		Lbar.remove(l)
		# s = ""
		for p in Bs:
			B.remove(p)
			# s += str(p) + ", "
		# print "Removed points " + s
		# print "Remaining points : " + str(B)
		# print ""

	return Ls

def sboxReducedInequalities(D):
	"""
	input : a dict D such that D[k] = [k1,...,kt] where k1,...,kt are the possible division propagation from k (obtained from SboxDivTrailTable)
	output : a reduced list of inequalities whose feasible solutions in {0,1}^n are exactly the possible division trail propagation
	"""

	(Lineq, A) = ineqRepresentation(D)
	return ineqReduction(Lineq, A)

def addSboxConstr(m, L, inputvar, outputvar):
	"""
	add to the model m the linear constraints obtained from L representing the propagation from inputvar to outputvar through one Sbox
	if n is the size of the input/output, then an inequality l in L can be seen with 3 part :
	 - l[:n] is the list of coefficient on the input variables
	 - l[n:2n] is the list of coefficient on the output variables
	 - l[2n] == l[-1] is the constant term of the inequality
	for example, with n = 2, l = [1,2,3,4,5], inputvar = [x0, x1] and outputvar = [y0, y2]
	then we have :
					 x0 + 2*x1 + 3*y0 + 4*y2 + 5 >= 0
	return a list containing the added Gurobi.Constr
	"""

	n = len(inputvar)
	c = []
	for l in L:
		if l[-1] == ">=":
			c.append(m.addConstr(quicksum([l[i]*inputvar[i] for i in range(n)] + [l[i]*outputvar[i-n] for i in range(n,2*n)]) + l[-2] >= 0))
		else:
			c.append(m.addConstr(quicksum([l[i]*inputvar[i] for i in range(n)] + [l[i]*outputvar[i-n] for i in range(n,2*n)]) + l[-2] == 0))

	return c

def cleanOptimize(m_input):
	m = m_input.copy()
	runtime = 0
	while True:
		m.write("testmodelclean.mps")
		m.optimize()
		runtime += m.Runtime

		if m.Status != 2:
			break
		if m.IntVio == 0: #No integer inconsistency
			break
		else:
			Lfix = []
			for v in m.getVars():
				val = v.getAttr('x')
				ival = int(val)
				if val != ival:
					Lfix.append((v,ival))
			for (v,ival) in Lfix:
				m.addConstr(v == ival)
			m.update()

	return (m,runtime)


def searchDistinguisher(m_input):
	"""
	Given the model m_input
	Return a set of balanced bit position
	Algorithm 3
	"""

	m = m_input.copy() #copy as we will modify the model
	m.update()
	m.Params.OutputFlag = 0
	m.Params.IntFeasTol = 1e-9 #not always necessary, can solve some integer inconsistency issues
	# m.Params.Presolve = 0

	ctr = 0
	totalruntime = 0
	obj = m.getObjective()
	S = [obj.getVar(i).getAttr("VarName") for i in range(obj.size())]
	n = len(S)
	for i in range(n):
		# m.optimize()
		(m2,r) = cleanOptimize(m)
		totalruntime += r
		if m2.Status == 2:
			#if the model has feasible solution
			#Check if there is some integer inconsistency
			# obj = m.getObjective()
			# for j in range(n):
			# 	val = obj.getVar(j).getAttr('x')
			# 	if val != int(val):
			# 		print "\n!!! Integer inconsistency detected !!!"
			if m2.ObjVal == 1:
				obj2 = m2.getObjective()
				for j in range(n):
					var = obj2.getVar(j)
					val = var.getAttr('x')
					if val == 1:
						S.remove(var.getAttr("VarName"))
						ctr += 1
						
						sys.stdout.write(str(ctr) + " non balanced variables (" + ("%.2f" % totalruntime) + "s)\r")
						sys.stdout.flush()
						varm = obj.getVar(j)
						m.addConstr(varm == 0)
						m.update()
						break
			else:
				return (S,totalruntime)
		elif m2.Status == 3:
			if i == 0:
				print "Infeasible model at first try"
			return (S,totalruntime)
		else:
			print "Error on model Status (" + str(m.Status) +")"
			return (S,totalruntime)
	return (S,totalruntime)

def computeFullDivisionProperty(m_input):
	"""
	Given a model m_input
	Return the (reduced) list of all the division property vectors in the last round
	"""

	m = m_input.copy() #copy as we will modify the model
	m.Params.OutputFlag = 0
	m.Params.IntFeasTol = 1e-9 #not always necessary, can solve some integer inconsistency issues
	# m.Params.Presolve = 0 #disable presolve for integer inconsistency issues
	m.update()

	totalruntime = 0

	obj = m.getObjective()
	n = obj.size()
	objvars = [obj.getVar(i) for i in range(n)]

	K = []

	#This is to help the solver prove that a solution is optimal
	#Once we found a solution of weight n, we know that there are no other solutions of weight < n
	#Removing these constraint can help with integer inconsistency issues
	prevMinWeight = 1
	helperConstr = m.addConstr(quicksum(v for v in objvars) >= 1)

	while m.Status != 3:
		m.optimize()
		totalruntime += m.Runtime
		if m.Status == 2:
			#If the model has feasible solution
			#Get the solution and cut it
			

			#Check if there is some integer inconsistency
			k = [0 for _ in range(n)]
			s = LinExpr()
			nbbit = 0
			for j in range(n):
				val = objvars[j].X
				ival = int(val)
				if val != ival:
					print "\n!!! Integer inconsistency detected !!!"
					return (K+[-1],totalruntime)

				k[j] = ival
				if ival == 1:
					s += objvars[j]
					nbbit += 1

			#s is the sum of all bits of k that are set to 1
			#So we cut any redudant solution by saying that at least one of those bits must be zero
			m.addConstr(s <= nbbit-1)

			#This is to help the solver prove that a solution is optimal
			#Once we found a solution of weight n, we know that there are no other solutions of weight < n
			oval = m.ObjVal
			if(m.ObjVal > prevMinWeight):
				prevMinWeight = oval
				helperConstr.RHS = oval
				m.update()
			K.append(k)
			sys.stdout.write(str(len(K)) + " elements in K, max weight " + str(oval) + " (" + ("%.2f" % totalruntime) + "s)\r")
			sys.stdout.flush()

		elif m.Status != 3:
			print "Error on model Status (" + str(m.Status) +")"
			return (K,totalruntime)
	print ""
	return (K, totalruntime)

def cmpvec(x,y):
	if x == y:
		return int(0)
	elif sum(x) < sum(y):
		return int(-1)
	elif sum(x) == sum(y) and x > y:
		return int(-1)
	else:
		return int(1)

def printDivSet(K):
	K.sort(cmpvec)
	for k in K:
		s = ""
		for i in range(len(k)):
			if i%4 == 0:
				s += " "
			s += str(k[i])
		print s