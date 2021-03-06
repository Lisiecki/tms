# input Petri game with strategy and output path for reachability graph
game = 3

if game == 0:
    input_file = "nets/same_decision_loop-net.apt"
    output_file = "nets/same_decision_loop-lts.apt"

if game == 1:
    input_file = "nets/concurrent_machines-net.apt"
    output_file = "nets/concurrent_machines-lts.apt"

if game == 2:
    input_file = "nets/document_work_flow-net.apt"
    output_file = "nets/document_work_flow-lts.apt"

if game == 3:
    input_file = "nets/selfreconfiguring_robots-net.apt"
    output_file = "nets/selfreconfiguring_robots-lts.apt"

# 0 := log memory states (gets VERY large for more than 2 players)
# 1 := log only markings (use this if reachability graph becomes very large!)
# 2 := log only last known markings (if you want to search for a strategy that uses the last known markings manually, then use this)
log_level = 1
