# input Petri game with strategy and output path for reachability graph
game = 0

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

# 0 := print memory states, 1 := print only markings
# use 1 if memory states become unreadable
log_level = 1
