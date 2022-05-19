from minH import trace_inference

#initialize
T = trace_inference("workspace/test/", "test")

# queries: 7\sqsubseteq 6, 7\sqsubseteq 5
subsumption_pairs =[['7', '6'], ['7', '5']]

# traing_complete set
result, s_a_pre, goal_id = T.trace_inference_rules(subsumption_pairs)
# result is dictionary: conclusion->[premise set 1, premise set 2, ...]
# s_a_pre: answer literals
# id of queries in subsumption_pairs
# Note that if there are several subsumptions, then the result will be integrated all together

