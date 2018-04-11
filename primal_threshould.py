#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from scipy.optimize import linprog
from itertools import chain, combinations


# t>=4
t = 7

fout = open('t'+str(t)+'.tex', 'w')

Jobs = set(range(1,t+1))

names = []

for i in range(1,t+1):
    names.append('p_'+str(i))
names += ['C^{PT}', 'C^\\ast']

Constraints = []


for i in range(1,t):
    # p_{t+1} < p_t
    Constraints.append(({i+1}, {i}))
    
# sum_{i}{p_i} = 16
A_eq = [[1 for i in range(t)] + [0,0]]
b_eq = [16]


# convert {1,2,3,4} to {'p_1', 'p_2', 'p_3', 'p_4'}
# Number to String
def N2S(s):
    return ','.join(map(lambda x:'p_'+str(x), s))

def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range((len(s)+2)//2))


All_Assignments = powerset(Jobs)

# remove equivalent assignments
OPT_Assignments = []
for OPT_M1 in powerset(Jobs):
    OPT_M1 = set(OPT_M1)
    if OPT_M1 != set() and Jobs - OPT_M1 not in All_Assignments:
        OPT_Assignments.append(OPT_M1)

def PT(t_now, M1, M2, constraints):
    global Cnt
    if t_now>t:
        # dupilicate one
        constraints_now = list(constraints)
        for OPT_M1 in OPT_Assignments:
            constraints = list(constraints_now)
            # Get the jobs on M2, i.e., all jobs not on M1
            OPT_M2 = Jobs - OPT_M1
            # tot processing time of jobs on M1 <= C^*
            # tot processing time of jobs on M2 <= C^*
            # p_{t+2} is C^*
            constraints.append((OPT_M1, {t+2}))
            constraints.append((OPT_M2, {t+2}))
            # p_{t+1} is C^{PT}
            # C^{PT} <= tot p.t. of machine that p_t is on
            # 9 <= tot p.t. of machine that p_t is on
            # tot p.t. of machines before p_t is assigned <= 7
            if t in M1:
                constraints.append(({t+1}, M1))
                constraints.append(({'9'}, M1))
                constraints.append((M1-{t}, {'7'}))  
                constraints.append((M2, {'7'})) 
            else:
                constraints.append(({t+1}, M2))
                constraints.append(({'9'}, M2))
                constraints.append((M1, {'7'})) 
                constraints.append((M2-{t}, {'7'}))  

            
            # minimize -(C^{PT}-9/8C^*) i.e. maximize C^{PT}-9/8C^*
            c = [0 for i in range(1,t+1)] + [-1, +9/8]
            A_ub = []
            b_ub = []
            #print(constraints)
            for a_cons in constraints:
                a_row = [ 0 for i in range(1,t+1) ] + [0, 0]
                a_b = [0]
                # variables in LHS
                for var in a_cons[0]:
                    # if it is some p_i
                    if type(var)==int:
                        a_row[var-1] = 1
                    # if it is a number, represented using string
                    else:
                        a_b = [-int(var)]
                # variables in RHS
                for var in a_cons[1]:
                    # if it is some p_i
                    if type(var)==int:
                        a_row[var-1] = -1
                    # if it is a number, represented using string
                    else:
                        a_b = [int(var)]
                A_ub.append(a_row)
                b_ub += a_b
            res = linprog(c, A_ub, b_ub, A_eq, b_eq)
            if res.success:
                Cnt += 1
            #if M1=={1,4,5} and OPT_M1=={1,2}:
                #for cs in constraints:
                #    print(cs)
                    
                print(M1)
                print(M2)
                print(OPT_M1)
                print(OPT_M2)
                #for l in range(len(A_ub)):
                #    print(A_ub[l])
                #for l in range(len(A_ub)):
                #    print(b_ub[l])    
                print(res)
                fout.write('PT Assignment:\n')
                fout.write('\\begin{equation}')
                fout.write('M_1 = \\{'+str(N2S(M1))+'\\},')
                fout.write('M_2 = \\{'+str(N2S(M2))+'\\}\n')
                fout.write('\\end{equation}\n')
                fout.write('OPT Assignment:\n')
                fout.write('\\begin{equation*}\n')
                fout.write('M_1 = \\{'+str(N2S(OPT_M1))+'\\},')
                fout.write('M_2 = \\{'+str(N2S(OPT_M2))+'\\}\n')
                fout.write('\\end{equation*}\n')
                fout.write('\\begin{eqnarray*}\n')
                for i in range(len(A_ub)):
                    first = True
                    for j in range(len(A_ub[i])):
                    #    if A_ub[i][j] == 1:
                    #        print('+'+names[j],end='')
                    #    elif A_ub[i][j] == -1:
                    #        print('-'+names[j],end='')
                    #print("<=", end='')
                    #print(b_ub[i], end=',\n')
                        if A_ub[i][j] == 1:
                            if first:
                                fout.write(names[j])
                                first = False
                            else:
                                fout.write('+'+names[j])
                        elif A_ub[i][j] == -1:
                            fout.write('-'+names[j])
                            first = False
                    fout.write('\\leq')
                    fout.write(str(b_ub[i]))
                    fout.write('\\\\\n')
                fout.write('\\end{eqnarray*}\n')
                fout.write('$f^\\ast='+str(-res.fun)+'$\n\n')
            
            #if res.success:
            #    print(res.fun)
            
        return
    # M1 < M2    
    new_cons = (M1, M2)
    # Either jobs on M2 with p_i <7 or >9,
    # otherwise primal assign rule will apply
    constraints1 = constraints + [new_cons] + [(M2 | {t_now}, {'7'})]
    constraints2 = constraints + [new_cons] + [({'9'}, M2 | {t_now})]
    # assign p_i to M1
    PT(t_now+1, M1 | {t_now}, M2, constraints1)
    PT(t_now+1, M1 | {t_now}, M2, constraints2)
    # M2 < M1
    new_cons = (M2, M1)
    # Either jobs on M1 with p_i <7 or >9,
    # otherwise primal assign rule will apply
    constraints1 = constraints + [new_cons] + [(M1 | {t_now}, {'7'})]
    constraints2 = constraints + [new_cons] + [({'9'}, M1 | {t_now})]    
    # assign p_i to M2    
    PT(t_now+1, M1, M2 | {t_now}, constraints1)
    PT(t_now+1, M1, M2 | {t_now}, constraints2)

# p[1] + p[3] < 7
PT(4, {1},{2,3}, Constraints + [({1} | {2}, {'7'})])
# p[1] + p[3] >9
PT(4, {1},{2,3}, Constraints + [({'9'}, {1} | {2})])

fout.close()