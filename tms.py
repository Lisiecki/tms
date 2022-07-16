import sys, getopt
import copy
import config
import time

flows = set()
initial = set()
bad_markings = set()
reachable = set()
places = []
transitions = []
commitmentset = set()
reachability_graph = set()
# Tells us which indices belong to system players
system_indices = set()
environment_indices = set()
log_level = 1

class ReachabilityGraph:

    def __init__(self):
        self.states = set()
        self.edges = set()

    def add_state(self,s):
        self.states.add(s)

    def add_edge(self,s0,s1,t):
        edge = (s0,t,s1)
        self.edges.add(edge)

    def check_safety(self,bad_markings):
        bad_markings = set()
        for edge in self.edges:
            bad = set(marking for marking in bad_markings if omega(edge[2]).issuperset(marking))
            if len(bad) > 0:
                if log_level == 0:
                    print("Safety property violatet at: ", edge[1], ":", edge[2])
                elif log_level == 1:
                    print("Safety property violatet at: ", edge[1], ":", omega(edge[2]))
                elif log_level == 2:
                    print("Safety property violatet at: ", edge[1], ":", edge[0].LKM)


    def check_determinism(self):
        for player in system_indices:
            for edge in self.edges:
                if edge[1] in transitions[player]:
                    edges = set(e for e in self.edges.difference({edge}) if e[1] in transitions[player])
                    state = (edge[0].LKM,edge[0].C)
                    states = list((e[0].LKM,e[0].C) for e in edges)

                    if state in states:
                        if log_level == 0:
                            print("Determinism property violatet at ", edge[1], state)
                        elif log_level == 1:
                            print("Determinism property violatet at ", edge[1], omega(edge[0]))
                        elif log_level == 2:
                            print("Determinism property violatet at ", edge[1], ":", edge[0].LKM)


    def check_deadlock_avoiding(self):
        # Create a set of every state that does not enable any transition
        states = set(state for state in self.states)
        edge_states = set(edge[0] for edge in self.edges)
        states = states.difference(edge_states)

        system_transitions = set(t for player in system_indices for t in transitions[player])

        for f in flows:
            deadlocks_at = set(state for state in states if f.t in system_transitions and f.start.issubset(omega(state)))
            for deadlock in deadlocks_at:
                if log_level == 0:
                    print("Deadlock avoiding property violatet at: ", f.t, ":",deadlock)
                elif log_level == 1:
                    print("Deadlock avoiding property violatet at: ", f.t, ":",omega(deadlock))
                elif log_level == 2:
                    print("Deadlock avoiding property violatet at: ", f.t, ":",deadlock.LKM)



class Counter:
    def __init__(self,token,player):
        self.token = token
        self.player = player

    def __repr__(self):
        return "counter_%d^%d" % (self.token, self.player)
    
    def __repr__(self):
        return "counter_%d^%d" % (self.token, self.player)

    def __eq__(self, other):
        if self.token == other.token and self.player == other.player:
            return True
        else:
            return False

    def __ne__(self, other):
        if self.token != other.token and self.player != other.player:
            return True
        else:
            return False

    def __hash__(self):
        return id(self)

class MemState:
    def __init__(self,LKM,C):
        self.LKM = LKM
        self.C = C

    def update(self,f):
        self.update_lkm(f)
        self.update_counter(f)

    def update_lkm(self,f):
        for i in ind(f.t):
            new_lkm = set()
            if True:
                for j in system_indices.union(environment_indices):
                    if j in ind(f.t):
                        new_p = places[j].intersection(f.end)
                        new_lkm.update(new_p)
                    else:
                        m = list(max(self.C[j],f.t))[0]
                        new_p = places[j].intersection(self.LKM[m])
                        new_lkm.update(new_p) 

            if False:
                for j in range(len(self.LKM)):
                    if j in ind(f.t):
                        new_p = places[j].intersection(f.end)
                        new_lkm.update(new_p)
                    else:
                        m = list(max(self.C[j],f.t))[0]
                        new_p = places[j].intersection(self.LKM[m])
                        new_lkm.update(new_p) 

            self.LKM[i] = new_lkm
        
    def update_counter(self,f):
        n = len(self.C)

        for i in range(n):
            m = list(max(self.C[i],f.t))[0]

            for c_relation in self.C[i]:
                k = c_relation[0].player
                l = c_relation[2].player
                self.C[i].remove(c_relation)

                if c_relation[1] == "<" and k not in ind(f.t):
                    c_relation = (c_relation[0], "<", c_relation[2])
                elif k in ind(f.t) and l in ind(f.t):
                    c_relation = (c_relation[0], "=", c_relation[2])
                elif c_relation[1] == "=" and k not in ind(f.t) and l not in ind(f.t):
                    c_relation = (c_relation[0], "=", c_relation[2])
                elif i in ind(f.t) and k in ind(f.t) and l not in ind(f.t):
                    c_relation = (c_relation[2], "<", c_relation[0])
                elif i in ind(f.t) and k not in ind(f.t) and l in ind(f.t):
                    c_relation = (c_relation[0], "<", c_relation[2])
                elif c_relation[1] == "=" and i not in ind(f.t) and k not in ind(f.t) and l in ind(f.t):
                    for c_k_m_relation in self.C[i]:
                        if c_k_m_relation[1] == "=" and ((c_k_m_relation[0].player == k and c_k_m_relation[2].player == m) or (c_k_m_relation[0].player == m and c_k_m_relation[2].player == k)):
                            c_relation = (c_relation[0], "=", c_relation[2])
                            break
                        elif c_k_m_relation[1] == "<" and c_k_m_relation[0].player == k and c_k_m_relation[2].player == m:
                            c_relation = (c_relation[0], "<", c_relation[2])
                            break
                elif c_relation[1] == "=" and i not in ind(f.t) and k in ind(f.t) and l not in ind(f.t):
                    for c_l_m_relation in self.C[i]:
                        if c_l_m_relation[1] == "=" and ((c_l_m_relation[0].player == l and c_l_m_relation[2].player == m) or (c_l_m_relation[0].player == m and c_l_m_relation[2].player == l)):
                            c_relation = (c_relation[0], "=", c_relation[2])
                            break
                        elif c_l_m_relation[1] == "<" and c_l_m_relation[0].player == l and c_l_m_relation[2].player == m:
                            c_relation = (c_relation[2], "<", c_relation[0])
                            break
                elif c_relation[1] == "<" and i not in ind(f.t) and k in ind(f.t) and l not in ind(f.t):
                    for c_l_m_relation in self.C[i]:
                        if c_l_m_relation[1] == "=" and ((c_l_m_relation[0].player == l and c_l_m_relation[2].player == m) or (c_l_m_relation[0].player == m and c_l_m_relation[2].player == l)):
                            c_relation = (c_relation[0], "=", c_relation[2])
                            break
                        elif c_l_m_relation[1] == "<" and c_l_m_relation[0].player == l and c_l_m_relation[2].player == m:
                            c_relation = (c_relation[2], "<", c_relation[0])
                            break
                        elif c_l_m_relation[1] == "<" and c_l_m_relation[0].player == m and c_l_m_relation[2].player == l:
                            c_relation = (c_relation[0], "<", c_relation[2])
                            break

                self.C[i].add(c_relation)

    def __copy__(self):
        return MemState(self.LKM,self.C)

    def __deepcopy(self,memo):
        return MemState(copy.deepcopy(self.LKM,self.C,memo))

    def __repr__(self):
        return "%s,%s" % (self.LKM,self.C)
    
    def __repr__(self):
        return "%s,%s" % (self.LKM,self.C)

class Flow:
    def __init__(self,flow):
        flow = flow.strip()
        t = flow.split(":")[0]
        p = flow.split(":")[1].strip()
        start = p.split("->")[0].strip()
        start = start.split(",")
        end = p.split("->")[1].strip()
        end = end.split(",")
        self.t = t
        self.start = frozenset(start)
        self.end = frozenset(end)

def max(counterclass,t):
    indices = ind(t)

    for relation in counterclass:
        if relation[0].player in indices and relation[2].player in indices and relation[1] == "<": 
            indices.remove(relation[0].player)

    return indices

def ind(t):
    players = set()
    players = set(player for player in system_indices.union(environment_indices) if t in transitions[player])
    
    if False:
        for f in flows:
            if t == f.t:
                for i in range(len(places)):
                    if len(places[i].intersection(f.start)) > 0:
                        players.add(i)

    return players

def next_memstate(memstate):
    for f in flows:
        if f.start.issubset(omega(memstate)):
            # check for every system player who fires that transition
            # if it enables this transition
            players = set(player for player in system_indices if player in ind(f.t))
            not_enabled = False
            
            for player in players:
                place = set(f.start.intersection(places[player])).pop()
                cs = (f.t,place)

                if len(cs) > 0 and cs in commitmentset:
                    continue
    
                cs = (f.t,place,frozenset(memstate.LKM[player]))

                if  len(cs) > 0 and cs in commitmentset:
                    continue

                not_enabled = True
                break

            if not_enabled == False:
                already_there = False
                new_memstate = copy.deepcopy(memstate)
                new_memstate.update(f)
                ltscsmem.add_edge(memstate,new_memstate,f.t)

                # terminate if memory state is already in reachability graph
                states = [(state.LKM,state.C) for state in ltscsmem.states if omega(state) == omega(new_memstate)]
                state = (new_memstate.LKM,new_memstate.C)
                already_there = set(s[0] == state[0] for s in states)

                if not already_there:
                    ltscsmem.add_state(new_memstate)
                    next_memstate(new_memstate)
                
        
def ext_memstate(memstate):
    for f in flows:
        t_with_lkm = set((f.t,frozenset(memstate.LKM[i])) for i in ind(f.t))
        system_transitions = set(t for player in system_indices for t in transitions[player])

        if (f.t in commitmentset or f.t not in system_transitions or not t_with_lkm.isdisjoint(commitmentset)) and f.start.issubset(omega(memstate)):
            already_there = False
            new_memstate = copy.deepcopy(memstate)
            new_memstate.update(f)
            ltscsmem.add_edge(memstate,new_memstate,f.t)

            # terminate if memory state is already in reachability graph
            states = [(state.LKM,state.C) for state in ltscsmem.states if omega(state) == omega(new_memstate)]
            state = (new_memstate.LKM,new_memstate.C)
            already_there = set(s[0] == state[0] for s in states)

            if not already_there:
                ltscsmem.add_state(new_memstate)
                next_memstate(new_memstate)

def find_reachable_markings(marking):
    for f in flows:
        if f.start.issubset(marking):
            new_marking = marking.copy()

            for p in marking.intersection(f.start):
                player_p = {}
                new_marking.remove(p)

                for pp in places:
                    if p in pp:
                        player_p = pp
                        break
                new_p = f.end.intersection(player_p)
                new_marking.update(new_p)

            if frozenset(new_marking) not in reachable:
                reachable.add(frozenset(new_marking))
                find_reachable_markings(new_marking)

def past(x):
    xs = {x}
    rslt = set()

    for f in flows:
        if x == f.t:
            for p in f.start:
                rslt.add(p)
                rslt.update(past(p))
        elif xs.issubset(f.end):
            rslt.add(f.t)
            rslt.update(past(f.t))

    return rslt

def omega(memstate):
    marking = set()

    for i in range(len(memstate.LKM)):
        p = memstate.LKM[i].intersection(places[i])
        marking.update(p)
    return frozenset(marking)

def init_counters(n):
    counterclasses = []
    for i in range(n):
        counterclass = set()
        for k in range(n):
            for l in range(k+1,n):
                counterclass.add((Counter(i,k),"=",Counter(i,l)))
        counterclasses.append(counterclass)

    return counterclasses

ltscsmem = ReachabilityGraph()

def main(argv):
    start = time.time()
    input_file = config.input_file
    output_file = config.output_file
    log_level = config.log_level

    try:
        opts, args = getopt.getopt(argv,"i:o:s:",["in=","out="])
    except getopt.GetoptError:
        print('Error due to wrong command line arguments!')
        sys.exit(2)

    for opt, arg in opts:
        if opt in ('-i', '--in'):
            input_file = arg
        elif opt in ('-o', '--out'):
            output_file = arg

    net_file = open(input_file,"r")
    net_lines = net_file.readlines()

    t_flag = False
    p_flag = False
    flow_flag = False
    init_flag = False
    bad_flag = False
    strategy_flag = False

    for line in net_lines:
        if line != "\n":
            if line.strip() == ".places":
                p_flag = True
                t_flag = False 
                flow_flag = False
                init_flag = False
                bad_flag = False
                strategy_flag = False
                continue
            if line.strip() == ".transitions":
                p_flag = False
                t_flag = True 
                flow_flag = False
                init_flag = False
                bad_flag = False
                strategy_flag = False
                continue
            elif line.strip() == ".flows":
                p_flag = False
                t_flag = False 
                flow_flag = True
                init_flag = False
                bad_flag = False
                strategy_flag = False
                continue
            elif line.strip() == ".initial_marking":
                p_flag = False
                t_flag = False 
                flow_flag = False
                init_flag = True
                bad_flag = False
                strategy_flag = False
                continue
            elif line.strip() == ".bad_markings":
                p_flag = False
                t_flag = False 
                flow_flag = False
                init_flag = False
                bad_flag = True
                strategy_flag = False
                continue
            elif line.strip() == ".strategy":
                p_flag = False
                t_flag = False 
                flow_flag = False
                init_flag = False
                bad_flag = False
                strategy_flag = True
                continue

            if p_flag:
                place = line.strip().split(":")[0]
                player = line.strip().split(":")[1]
                player_type = line.strip().split(":")[2]

                while int(player) >= len(places):
                    places.append(set())

                places[int(player)].add(place)

                if player_type == "s":
                   system_indices.add(int(player)) 
                else:
                   environment_indices.add(int(player))
                continue

            if t_flag:
                transition = line.strip().split(":")[0]
                players = line.strip().split(":")[1]
                players = players.split(",")

                while int(player)+1 >= len(transitions):
                    transitions.append(set())
                
                for player in players:
                    transitions[int(player)].add(transition)
                continue

            if flow_flag:
                flow = line.strip()
                f = Flow(flow)
                flows.add(f)
                continue
   
            if init_flag:
                initial.update(line.strip().split(","))
                continue

            if bad_flag:
                bad = set(line.strip().split(","))
                bad_markings.add(frozenset(bad))
                continue
            
            if strategy_flag:
                cs = line.strip().split(":")
                t = cs[0]
                p = cs[1]
                if len(cs) == 3:
                    lkm = frozenset(cs[2].strip().split(","))
                    commitmentset.add((t,p,lkm))
                else:
                    commitmentset.add((t,p))
    
    n = len(system_indices) + len(environment_indices)
    initials = []
    for i in range(n):
        initials.append(copy.deepcopy(initial))

    counters = init_counters(n)
    
    reachable.add(frozenset(initial))
    find_reachable_markings(initial)

    print("system players: ", system_indices)
    print("environment players: ", environment_indices)

    s0 = MemState(initials,counters)
    ltscsmem.add_state(s0)
    next_memstate(s0)
    
    ltscsmem.check_safety(bad_markings)
    ltscsmem.check_determinism()
    ltscsmem.check_deadlock_avoiding()
    
    for state in ltscsmem.states:
        if log_level == 0:
            print(state)
        elif log_level == 1:
            print(omega(state))
        elif log_level == 2:
            print(state.LKM)

    end = time.time()
    print("Time : ", end - start)

if __name__ == "__main__":
    main(sys.argv[1:])
