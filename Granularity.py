import numpy as np
import AND_conversion as AND
import OR_conversion as OR
from Grouping_Recorder import GroupingRecorder
from scipy.cluster.hierarchy import dendrogram
import matplotlib.pyplot as plt
import random
### Cause_Con conversion
def make_values_continuous(d):
    # Get unique values sorted
    unique_sorted_values = sorted(set(d.values()))
    # Map each value to its new value (index in the sorted list)
    value_to_index = {value: index for index, value in enumerate(unique_sorted_values)}
    # Update the dictionary with new values
    return {k: value_to_index[v] for k, v in d.items()}


def adjust_to_continuous(input_dict):
    # Extract unique values from the dictionary and sort them
    unique_values = sorted(set(input_dict.values()))
    
    # Create a mapping from original to new, continuous values
    value_mapping = {}
    for i, value in enumerate(unique_values):
        value_mapping[value] = i
    
    # Adjust the dictionary using the mapping
    adjusted_dict = {k: value_mapping[v] for k, v in input_dict.items()}
    
    return adjusted_dict
def group_cause_con_nodes(adj_matrix, grouped_nodes, ungrouped, already_grouped, recorder):
    n = len(adj_matrix[-1])
    grouped_set = set()
    count= 0
    for i in already_grouped:
        if isinstance(i, list):  # Check if the element is a list
            for j in i:
                grouped_set.add(j)
        else:
            grouped_set.add(i)
    
    

    # Iterate through the matrix to find cause_con connections and group nodes
    for i in range(n):
        if i in grouped_set:
            continue

        for j in range(i + 1, n):
            cause_con = []
            if j in grouped_set:
                continue
            
            # Check if nodes i and j with a cause_con relationship
            if adj_matrix[-1][i][j] > 0 or adj_matrix[-1][j][i] > 0:
                cause_con = [j]
            if cause_con:
                grouped_nodes.append((i, j))
                grouped_set.add(i)
                grouped_set.add(j)
                count +=1
                recorder.record(i, j, 'new_group_id')  
                
                break

    if count > 0:
        # Update ungrouped nodes
        ungrouped -= grouped_set
    return grouped_nodes, list(ungrouped)

def flatten_grouped_nodes(grouped_nodes):
    flattened = []
    for item in grouped_nodes:
        if isinstance(item, tuple):
            flattened.extend(item)
        else:
            flattened.append(item)
    return flattened  
 
def Cause_Con_Conversion(original_matrix, adj_matrix, grouped_nodes, ungrouped, already_grouped, node_mapping,recorder,final_order_grouped,final_node_dic):
    print("already_grouped: "+ str(already_grouped))
    grouped_nodes, ungrouped = group_cause_con_nodes(adj_matrix, grouped_nodes, ungrouped, already_grouped,recorder)
    print('getting_cause_con_grouped_nodes: ' + str(grouped_nodes))
    print('getting_cause_con_ungrouped_nodes: ' + str(ungrouped))
    if len(grouped_nodes) == 0:
        
        return adj_matrix, grouped_nodes, ungrouped, already_grouped, set(ungrouped), node_mapping,final_order_grouped,[],final_node_dic
    n = len(adj_matrix[0])
    
    
    grouped_node_count = len(grouped_nodes)
    check_grouped = []
    for i in grouped_nodes:
        check_grouped.append(i)
    new_n = n - grouped_node_count  # Decrease size for each grouped pair
    stored_matrix = np.copy(adj_matrix[-1])
    original = np.copy(adj_matrix[0])
    # Create a mapping from old to new node indices                         
    
    flattened_grouped_nodes = flatten_grouped_nodes(grouped_nodes)
    new_index = 0
    new_new_index = 0
    already_count = []
    record = 0
    node_mapping_new = {}
    first = 0
    
    if len(already_grouped) == 0:
        while check_grouped:
            selected_tuple = random.choice(check_grouped)
            check_grouped.remove(selected_tuple)
            final_order_grouped.append(selected_tuple)
            n = len(adj_matrix[-1])
            if first == 0:
                for j in selected_tuple:
                    node_mapping_new[j] = new_new_index // 2 
                    new_new_index += 1
                    
                    
                    already_count.append(j)
                not_grouped_index = max(node_mapping_new.values())+1
            elif first != 0:
                for j in selected_tuple:
                    min_value = min(selected_tuple)
                    new_min= node_mapping_new[min_value]
                    
                    node_mapping_new[j] = new_min
            first+=1
            
            for i in range(n):  
                if i not in selected_tuple and i not in already_count:
                    if i not in node_mapping_new.keys():
                        
                        node_mapping_new[i] = not_grouped_index
                        not_grouped_index +=1
            
            node_mapping_new = dict(sorted(node_mapping_new.items(), key=lambda item: item[1]))
                        
            node_mapping_new = adjust_to_continuous(node_mapping_new)
            inputdic = node_mapping_new.copy()
            
            final_node_dic.append(inputdic)
                        
           
            discrete_matrix_len =  n - 1
            
            new_adj_matrix = np.zeros((discrete_matrix_len, discrete_matrix_len))
           
            
            n = len(stored_matrix)
            for i in range(n):
                new_i = node_mapping_new[i]
                
                for j in range(n):
                    new_j = node_mapping_new[j]
                    
                    
                    if stored_matrix[i][j] > 0:
                        if new_i != new_j:
                        #for k in range(n):
                         #   if adj_matrix[i][k] > 1:
                          #      check_list.append((i,k))
                        # Sum the weights to the new matrix and subtract 1
                            new_adj_matrix[new_i][new_j] = stored_matrix[i][j]
                        
            
            adj_matrix.append(new_adj_matrix)
                            
            
        node_mapping = node_mapping_new
        
        
                            
                   
        '''
        for i in range(n):
            new_i = node_mapping[i]
            for j in range(n):
                new_j = node_mapping[j]
                if adj_matrix[i][j] > 0:
                    count = 0
                    node_id_casuing_other = []
                    for k in range(n):
                        if adj_matrix[j][k] > 0:
                            count += 1
                            node_id_casuing_other.append(k)
                    print('count: ' + str(count))
                    if count == 0:
                        if new_i != new_j:
                            new_adj_matrix[new_i][new_j] = max(new_adj_matrix[new_i][new_j], adj_matrix[i][j] - 1)
                    if count > 0:
                        if new_i != new_j:
                            for m in node_id_casuing_other:
                                new_m = node_mapping[m]
                                new_adj_matrix[new_j][new_m] = max(new_adj_matrix[new_j][new_m], adj_matrix[j][m] - 1)
                                new_adj_matrix[new_i][new_j] = max(new_adj_matrix[new_i][new_j], adj_matrix[i][j] - 1, 1)
   '''
    add_on_1 = []
    count = 0
    node_mapping_final = node_mapping.copy()
    if len(already_grouped) > 0:
        while check_grouped:
            selected_tuple = random.choice(check_grouped)
            check_grouped.remove(selected_tuple)
            final_order_grouped.append(selected_tuple)
            n = len(adj_matrix[-1])
            min_value = min(selected_tuple)
            
            for j in selected_tuple:
                if count == 0:
                    
                    keys_for_value = [key for key, value in node_mapping_final.items() if value == j]
                    for key in keys_for_value:
                    
                        node_mapping[key] = min_value
                    count += 1
                elif count != 0:
                    keys_for_value = [key for key, value in node_mapping_final.items() if value == j]
                    min_key = 0
                    for key, value in node_mapping_final.items():
                        if value == min_value:
                            min_key = key
                   
                    for key in keys_for_value:
                        
                        node_mapping[key] = node_mapping[min_key]
            
            #node_mapping = dict(sorted(node_mapping.items(), key=lambda item: item[1]))
            
            node_mapping = adjust_to_continuous(node_mapping)
            inputdic = node_mapping.copy()
            
            final_node_dic.append(inputdic)
            discrete_matrix_len =  n - 1
            new_adj_matrix = np.zeros((discrete_matrix_len, discrete_matrix_len))
           
            
            
            n = len(original)
            
            for i in range(n):
                new_i = node_mapping[i]
                neww_i = node_mapping_final[i]
                for j in range(n):
                    new_j = node_mapping[j]
                    neww_j = node_mapping_final[j]
                    
                    if stored_matrix[neww_i][neww_j] > 0:
                        if new_i != new_j:
                        #for k in range(n):
                         #   if adj_matrix[i][k] > 1:
                          #      check_list.append((i,k))
                        # Sum the weights to the new matrix and subtract 1
                            new_adj_matrix[new_i][new_j] = stored_matrix[neww_i][neww_j]
                        
            
            adj_matrix.append(new_adj_matrix)
                            
            
      
        
        
        
    '''
        n = len(original_matrix[-1])
        add_on = []
        for value_to_remove in flattened_grouped_nodes:
            for i in node_mapping.keys():
                if node_mapping[i] == value_to_remove:
                    add_on.append(i)
            node_mapping_final = {k: v for k, v in node_mapping.items() if v != value_to_remove}
        print(add_on)
        print(node_mapping_final)
        
      
        node_index = []
        record = 10000000000000
        add_on_1 = add_on
        add_on_list = [(add_on[i], add_on[i+1]) if i + 1 < len(add_on) else (add_on[i],) for i in range(0, len(add_on), 2)]
        print("!!!!!!!" + str(add_on_list))
        count = 0
        for i in add_on_list:
            for j in i:
                node_mapping_final[j] = min(list(grouped_nodes[count]))
                print(node_mapping_final)
            count += 1
                
        
        print(add_on_list)
        sorted_items = sorted(node_mapping_final.items())
        node_mapping_final = dict(sorted_items)
        node_mapping_final = dict(sorted(node_mapping_final.items(), key=lambda item: item[1]))
        print(node_mapping_final)
        node_mapping_final = adjust_to_continuous(node_mapping_final)
        
        '''
    '''
        new_values = {}
        current_value = 0
        for key, value in node_mapping_final:
            
            if value not in new_values:
                new_values[value] = current_value
                current_value += 1
        
        final_map = {key: new_values[value] for key, value in node_mapping_final}
        node_mapping = final_map
        '''
    '''
        
        new_adj_matrix = np.zeros((new_n, new_n))
        count1 = 100000000
        already_grouped = flatten_grouped_nodes(already_grouped)
        print(node_mapping_final)
        print(already_grouped)
        print(node_mapping)
        for i in range(n):
            new_i = node_mapping_final[i]
            neww_i = node_mapping[i]
            count = 0
            if new_i in already_grouped:
                for j in range(n):
                    new_j = node_mapping_final[j]
                    neww_j = node_mapping[j]
                    if stored_matrix[neww_i][neww_j] != 0:
                        
                        new_adj_matrix[new_i][new_j] = stored_matrix[neww_i][neww_j]
            if new_i not in already_grouped:
                for j in range(n):
                    neww_j = node_mapping[j]
                    new_j = node_mapping_final[j]
                    if stored_matrix[neww_i][neww_j] > 0:
                        # Sum the weights to the new matrix and subtract 1
                        count+=1
                        
                        
                           
                        new_adj_matrix[new_i][new_j] = stored_matrix[neww_i][neww_j]
                        for grouped_tuple in check_grouped:
                            
                            if neww_i in grouped_tuple:
                                
                                adj_matrix.append(new_adj_matrix)
                                count1 = check_grouped.index(grouped_tuple)
                                
                        if count1 != 100000000:
                            check_grouped.pop(count1)
                            
                        count1 = 100000000
        '''

    for new_adj_matrix in adj_matrix[1:]:    
        for i in range(len(new_adj_matrix)):
            for j in range(len(new_adj_matrix)):    
                if new_adj_matrix[i][j] > 0 and new_adj_matrix[j][i] > 0:
                    if new_adj_matrix[i][j] >= new_adj_matrix[j][i]:
                        new_adj_matrix[j][i] = 0
                    if new_adj_matrix[i][j] < new_adj_matrix[j][i]:
                        new_adj_matrix[i][j] = 0
    
    final_grouped_nodes = set()
    final_ungrouped = set()
    I_want = []
    for k in flattened_grouped_nodes:
    
        I_want.append(k)
    if len(already_grouped) == 0:
        for m in flattened_grouped_nodes:
        
            final_grouped_nodes.add(node_mapping[m])
        for j in ungrouped:
            final_ungrouped.add(node_mapping[j])
    if len(already_grouped) != 0:
        for m in flattened_grouped_nodes:
            keys = [key for key, value in node_mapping_final.items() if value == m]
            for keys in keys:
                final_grouped_nodes.add(node_mapping[keys])
        for j in already_grouped:
            keys = [key for key, value in node_mapping_final.items() if value == j]
            for keys in keys:
                final_grouped_nodes.add(node_mapping[keys])
        for j in ungrouped:
            keys = [key for key, value in node_mapping_final.items() if value == j]
            for keys in keys:
                final_ungrouped.add(node_mapping[keys])
        
    
    grouped_nodes.append(already_grouped)
    
    for new_adj_matrix in adj_matrix[1:]:
        for i in range(len(new_adj_matrix)):
            for j in range(len(new_adj_matrix)):
                if i == j and new_adj_matrix[i][j] > 0:
                    new_adj_matrix[i][j] = 0
                if new_adj_matrix[i][j] > 1:
                    count = new_adj_matrix[i][j]
                    count1 = 0
                    for k in range(len(new_adj_matrix)):
                        count1 += new_adj_matrix[k][j]
                    if count1 == count:
                        new_adj_matrix[i][j] = 1
    
   
    final_node_dic_1 = {key: value for key, value in node_mapping.items()}
    return adj_matrix, grouped_nodes, ungrouped,list(final_grouped_nodes), final_ungrouped, final_node_dic_1, final_order_grouped,I_want,final_node_dic
        
        

    
def create_linkage_matrix(grouping_operations, total_initial_nodes):
    linkage_data = []
    # This assumes the highest node ID in your operations is the last initial node
    # The next cluster ID starts from the next integer
    next_cluster_id = total_initial_nodes
        
    for operation in grouping_operations:
        node1_id, node2_id, _ = operation
            
        # Map node IDs directly for initial nodes and clusters
        if node1_id >= total_initial_nodes:
            idx1 = next_cluster_id  # Assign new cluster ID if not an initial node
            next_cluster_id += 1
        else:
            idx1 = node1_id  # Use the node ID directly if it's an initial node
            
        if node2_id >= total_initial_nodes:
            idx2 = next_cluster_id  # Assign new cluster ID if not an initial node
            next_cluster_id += 1
        else:
            idx2 = node2_id  # Use the node ID directly if it's an initial node
            
        # Record the merge
        # Note: Using len(linkage_data)+1 as the distance to increment with each merge
        linkage_data.append([idx1, idx2, len(linkage_data)+1, 2])
        
    return np.array(linkage_data, dtype=float)     
    


def running_granularity(method_list, adjacency_matrix ,final_order_grouped):
    
    n= len(adjacency_matrix[-1])
    original_matrix = np.copy(adjacency_matrix)
    grouped_nodes = []
    already_grouped= []
    node_mapping = {}
    ungrouped = set(range(n))
    
    node_mapping_list = []
    final_order = []
    final_grouped = []
    final_node_dic=[]
    
    method_dic = {'AND':lambda: AND.AND_Gate_Conversion(original_matrix, adjacency_matrix, grouped_nodes, ungrouped, already_grouped, node_mapping,recorder,final_order_grouped,final_node_dic),
                  'Cause_Con': lambda: Cause_Con_Conversion(original_matrix, adjacency_matrix, grouped_nodes, ungrouped, already_grouped, node_mapping,recorder,final_order_grouped,final_node_dic),
                  'OR': lambda: OR.OR_Gate_Conversion(original_matrix, adjacency_matrix, grouped_nodes, ungrouped, already_grouped, node_mapping,recorder,final_order_grouped,final_node_dic)}
    
    
   
        # Adjust to include the first method in method_list if it was previously skipped unintentionally
    
    times = 0
    
    
    for method_name in method_list:
        times += 1
        method = method_dic[method_name]
        
        # Proceed if there are more than one ungrouped nodes
        
        adjacency_matrix, original_grouped_nodes, original_ungrouped, already_grouped, ungrouped, node_mapping,final_order_grouped,I_want,final_node_dic= method_dic[method_name]()  # Expecting method returns updated matrix and any changes
        
        
        node_mapping_list.append(final_node_dic)
        final_grouped.append(final_order_grouped)
        final_order_grouped = []
        final_node_dic=[]
        
        # Assuming changes is a boolean or similar indicating if the method altered the matrix
        print(f"Conversion {method_name} applied, resulting in new adjacency matrix and groupings.")
        
        #print(recorder.grouping_operations)
        # Optionally, here update recorder with changes
        # recorder.record(...)
        grouped_nodes = []
       


        
    #total_nodes = max(max(pair[:2]) for pair in recorder.grouping_operations) + 1
    #print(recorder.grouping_operations)
    #print(total_nodes)
    #linkage_matrix = create_linkage_matrix(recorder.grouping_operations, total_nodes)
    #dendrogram(linkage_matrix)
    
    #plt.title('Network Merges Dendrogram')
    #plt.xlabel('Node or Group ID')
    #plt.ylabel('Distance or Merge Order')
    #plt.show()  # This wil
    if len(ungrouped)>1:
        consistency = 0
        return adjacency_matrix, recorder, consistency,final_grouped,node_mapping_list
    print('Finalized one round of granularity reduction.')
    consistency = 1
    return adjacency_matrix, recorder, consistency, final_grouped , node_mapping_list
  
        

# Example usage
adj_matrix = [np.array([
    [0, 0, 1, 0, 0, 3],
    [0, 0, 1, 0, 0, 2],
    [0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 3],
    [0, 0, 0, 0, 0, 0]
])]
method_list = ['AND','OR','Cause_Con']
#recorder = GroupingRecorder()
recorder = GroupingRecorder()
for i in range(2):
    running_granularity(method_list, adj_matrix,[])




def remove_empty_lists_from_nested_list(nested_list, iterations=5):
    """
    Iterates a specified number of times over a nested list structure and removes any empty sublists.

    Parameters:
    - nested_list: The nested list structure to be modified.
    - iterations: The number of times to perform the empty list removal process.
    """
    for _ in range(iterations):
        for outer_list in nested_list:
            # Iterate over a copy of the list to safely remove items
            for i in range(len(outer_list) - 1, -1, -1):
                if not outer_list[i]:  # Check if the sublist is empty
                    del outer_list[i] 

'''
b = [[{0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 7: 6},
      {0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 1, 6: 4, 7: 5}, 
      {0: 0, 1: 0, 2: 1, 3: 2, 4: 2, 5: 1, 6: 3, 7: 4},
      {0: 0, 1: 0, 2: 1, 3: 2, 4: 2, 5: 1, 6: 3, 7: 3}], 
     [{}, {0: 0, 1: 0, 2: 1, 3: 2}, {0: 0, 1: 0, 2: 1, 3: 1}],
     [{},{},{0:0, 1:0}]]

a = [[[0, 1], [1, 4], [2, 3], [3, 4]], [[], [0, 1], [2, 3]], [[],[],[0,1]]]  

cluster = [[[(11, 13), (33, 34), (0, 3), (22, 23), (16, 17), (20, 21), (18, 19), (26, 27), (5, 6), (2, 4), (9, 10), 
             (7, 8), (31, 32), (24, 25), (14, 15), (28, 29)], [], [(2, 7)]], 
           [[(0, 1), (16, 17), (13, 14), (6, 8), (9, 10), (11, 12), (4, 5)], [(2, 5)], []], 
           [[(4, 8), (0, 3), (6, 7)], [(3, 4)], []], 
           [[(4, 5), (0, 1)], [], []], 
           [[], [(0, 3)], [(1, 2)]]]
dic = [[[{11: 0, 13: 0, 0: 1, 1: 2, 2: 3, 3: 4, 4: 5, 5: 6, 6: 7, 7: 8, 8: 9, 9: 10, 10: 11, 12: 12, 14: 13, 15: 14, 16: 15, 17: 16, 18: 17, 19: 18, 20: 19, 21: 20, 22: 21, 23: 22, 24: 23, 25: 24, 26: 25, 27: 26, 28: 27, 29: 28, 30: 29, 31: 30, 32: 31, 33: 32, 34: 33}, {11: 0, 13: 0, 0: 1, 1: 2, 2: 3, 3: 4, 4: 5, 5: 6, 6: 7, 7: 8, 8: 9, 9: 10, 10: 11, 12: 12, 14: 13, 15: 14, 16: 15, 17: 16, 18: 17, 19: 18, 20: 19, 21: 20, 22: 21, 23: 22, 24: 23, 25: 24, 26: 25, 27: 26, 28: 27, 29: 28, 30: 29, 31: 30, 32: 31, 33: 32, 34: 32}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 12: 11, 14: 12, 15: 13, 16: 14, 17: 15, 18: 16, 19: 17, 20: 18, 21: 19, 22: 20, 23: 21, 24: 22, 25: 23, 26: 24, 27: 25, 28: 26, 29: 27, 30: 28, 31: 29, 32: 30, 33: 31, 34: 31}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 12: 11, 14: 12, 15: 13, 16: 14, 17: 15, 18: 16, 19: 17, 20: 18, 21: 19, 22: 20, 23: 20, 24: 21, 25: 22, 26: 23, 27: 24, 28: 25, 29: 26, 30: 27, 31: 28, 32: 29, 33: 30, 34: 30}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 12: 11, 14: 12, 15: 13, 16: 14, 17: 14, 18: 15, 19: 16, 20: 17, 21: 18, 22: 19, 23: 19, 24: 20, 25: 21, 26: 22, 27: 23, 28: 24, 29: 25, 30: 26, 31: 27, 32: 28, 33: 29, 34: 29}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 12: 11, 14: 12, 15: 13, 16: 14, 17: 14, 18: 15, 19: 16, 20: 17, 21: 17, 22: 18, 23: 18, 24: 19, 25: 20, 26: 21, 27: 22, 28: 23, 29: 24, 30: 25, 31: 26, 32: 27, 33: 28, 34: 28}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 12: 11, 14: 12, 15: 13, 16: 14, 17: 14, 18: 15, 19: 15, 20: 16, 21: 16, 22: 17, 23: 17, 24: 18, 25: 19, 26: 20, 27: 21, 28: 22, 29: 23, 30: 24, 31: 25, 32: 26, 33: 27, 34: 27}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 12: 11, 14: 12, 15: 13, 16: 14, 17: 14, 18: 15, 19: 15, 20: 16, 21: 16, 22: 17, 23: 17, 24: 18, 25: 19, 26: 20, 27: 20, 28: 21, 29: 22, 30: 23, 31: 24, 32: 25, 33: 26, 34: 26}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 4, 5: 5, 6: 5, 7: 6, 8: 7, 9: 8, 10: 9, 12: 10, 14: 11, 15: 12, 16: 13, 17: 13, 18: 14, 19: 14, 20: 15, 21: 15, 22: 16, 23: 16, 24: 17, 25: 18, 26: 19, 27: 19, 28: 20, 29: 21, 30: 22, 31: 23, 32: 24, 33: 25, 34: 25}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 8, 12: 9, 14: 10, 15: 11, 16: 12, 17: 12, 18: 13, 19: 13, 20: 14, 21: 14, 22: 15, 23: 15, 24: 16, 25: 17, 26: 18, 27: 18, 28: 19, 29: 20, 30: 21, 31: 22, 32: 23, 33: 24, 34: 24}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 12: 8, 14: 9, 15: 10, 16: 11, 17: 11, 18: 12, 19: 12, 20: 13, 21: 13, 22: 14, 23: 14, 24: 15, 25: 16, 26: 17, 27: 17, 28: 18, 29: 19, 30: 20, 31: 21, 32: 22, 33: 23, 34: 23}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 12: 7, 14: 8, 15: 9, 16: 10, 17: 10, 18: 11, 19: 11, 20: 12, 21: 12, 22: 13, 23: 13, 24: 14, 25: 15, 26: 16, 27: 16, 28: 17, 29: 18, 30: 19, 31: 20, 32: 21, 33: 22, 34: 22}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 12: 7, 14: 8, 15: 9, 16: 10, 17: 10, 18: 11, 19: 11, 20: 12, 21: 12, 22: 13, 23: 13, 24: 14, 25: 15, 26: 16, 27: 16, 28: 17, 29: 18, 30: 19, 31: 20, 32: 20, 33: 21, 34: 21}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 12: 7, 14: 8, 15: 9, 16: 10, 17: 10, 18: 11, 19: 11, 20: 12, 21: 12, 22: 13, 23: 13, 24: 14, 25: 14, 26: 15, 27: 15, 28: 16, 29: 17, 30: 18, 31: 19, 32: 19, 33: 20, 34: 20}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 12: 7, 14: 8, 15: 8, 16: 9, 17: 9, 18: 10, 19: 10, 20: 11, 21: 11, 22: 12, 23: 12, 24: 13, 25: 13, 26: 14, 27: 14, 28: 15, 29: 16, 30: 17, 31: 18, 32: 18, 33: 19, 34: 19}, {11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 12: 7, 14: 8, 15: 8, 16: 9, 17: 9, 18: 10, 19: 10, 20: 11, 21: 11, 22: 12, 23: 12, 24: 13, 25: 13, 26: 14, 27: 14, 28: 15, 29: 15, 30: 16, 31: 17, 32: 17, 33: 18, 34: 18}], 
        [], [{11: 0, 13: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 12: 2, 14: 7, 15: 7, 16: 8, 17: 8, 18: 9, 19: 9, 20: 10, 21: 10, 22: 11, 23: 11, 24: 12, 25: 12, 26: 13, 27: 13, 28: 14, 29: 14, 30: 15, 31: 16, 32: 16, 33: 17, 34: 17}]], 
       [[{0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 7: 6, 8: 7, 9: 8, 10: 9, 11: 10, 12: 11, 13: 12, 14: 13, 15: 14, 16: 15, 17: 16}, {0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 7: 6, 8: 7, 9: 8, 10: 9, 11: 10, 12: 11, 13: 12, 14: 13, 15: 14, 16: 15, 17: 15}, {0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 7: 6, 8: 7, 9: 8, 10: 9, 11: 10, 12: 11, 13: 12, 14: 12, 15: 13, 16: 14, 17: 14}, {0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 8: 5, 7: 6, 9: 7, 10: 8, 11: 9, 12: 10, 13: 11, 14: 11, 15: 12, 16: 13, 17: 13}, {0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 8: 5, 7: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 10, 14: 10, 15: 11, 16: 12, 17: 12}, {0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 8: 5, 7: 6, 9: 7, 10: 7, 11: 8, 12: 8, 13: 9, 14: 9, 15: 10, 16: 11, 17: 11}, {0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 3, 6: 4, 8: 4, 7: 5, 9: 6, 10: 6, 11: 7, 12: 7, 13: 8, 14: 8, 15: 9, 16: 10, 17: 10}], [{0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 3, 6: 4, 8: 4, 7: 2, 9: 5, 10: 5, 11: 6, 12: 6, 13: 7, 14: 7, 15: 8, 16: 9, 17: 9}], []], 
       [[{4: 0, 8: 0, 0: 1, 1: 2, 2: 3, 3: 4, 5: 5, 6: 6, 7: 7, 9: 8}, {4: 0, 8: 0, 0: 1, 3: 1, 1: 2, 2: 3, 5: 4, 6: 5, 7: 6, 9: 7}, {4: 0, 8: 0, 0: 1, 3: 1, 1: 2, 2: 3, 5: 4, 6: 5, 7: 5, 9: 6}], [{4: 0, 8: 0, 0: 1, 3: 1, 1: 2, 2: 3, 5: 3, 6: 4, 7: 4, 9: 5}], []], 
       [[{4: 0, 5: 0, 0: 1, 1: 2, 2: 3, 3: 4}, {4: 0, 5: 0, 0: 1, 1: 1, 2: 2, 3: 3}], [], []], 
       [[], [{0: 0, 3: 0, 1: 1, 2: 2}], [{0: 0, 3: 0, 1: 1, 2: 1}]]]
#step 0
dic2 = [[dic22 for sublist in outerlist for dic22 in sublist] for outerlist in dic]
'''
def merge_inner_dicts(nested_list):
    # Function to merge dictionaries
    def merge_dicts(dict_list):
        merged_dict = {}
        for d in dict_list:
            merged_dict.update(d)
        return merged_dict
    
    # Recursively navigate through the list to find and merge dictionaries at the deepest level
    def process_list(current_list):
        # Base case: If the current list contains dictionaries, merge them
        if all(isinstance(item, dict) for item in current_list):
            return [merge_dicts(current_list)]
        
        # Recursive case: Process each item in the current list
        return [process_list(item) if isinstance(item, list) else item for item in current_list]
    
    return process_list(nested_list)


def transfer_to_previous(cluster,dic):
    new_cluster = []
    remove_empty_lists_from_nested_list(cluster)
    remove_empty_lists_from_nested_list(dic)
    for i, target_dic_group in zip(cluster, dic):
        three_party = []
        three_party.append(i[0])
        for j in range(1,len(i)):
            if len(i[j]) == 0:
                continue
            elif len(i[j]) != 0:
                new_group_nodes = []
                for count in range(len(i[j])):
                    keys = [key for key, value in target_dic_group[j][count].items() if value == i[j][count][0]]
                    new_group_nodes.append(keys)
                three_party.append(new_group_nodes)
        new_cluster.append(three_party)
    print(new_cluster)
    return new_cluster
 # step 1                   
#aaa = transfer_to_previous(cluster,dic)
#print(aaa)

def find_innermost_groups(nested_list):
    innermost_groups = []

    def find_groups(current_list, current_depth, target_depth):
        if current_depth == target_depth:
            innermost_groups.append(current_list)
            return
        
        for item in current_list:
            if isinstance(item, list):
                find_groups(item, current_depth + 1, target_depth)

    def max_depth(lst, depth=0):
        if not isinstance(lst, list) or not lst:
            return depth
        return max(max_depth(item, depth + 1) for item in lst)

    target_depth = max_depth(nested_list) - 1
    find_groups(nested_list, 0, target_depth)

    return innermost_groups

def modify_and_reform(nested_list,target_dic_new):
    def modify_list(inner_list):
        new = []
        
        for wrong_nodes in inner_list:
            if isinstance(wrong_nodes, int):
                new_keys = [key for key, value in target_dic_new.items() if value == wrong_nodes]
                if len(new_keys) == 1:
                    for i in new_keys:
                        new.append(i)
                if len(new_keys) != 1:
                    new.append(new_keys)
            if isinstance(wrong_nodes, list):
                
                neww = modify_and_reform(wrong_nodes,target_dic_new)
                new.append(neww)
        return new

    def deep_modify(current_list):
        print("modify: " + str(current_list))
        for i in range(len(current_list)):
            if isinstance(current_list[i], list):  # Check if it's a list
                # Modify if it's an innermost list by checking if its first element is not a list
                if not isinstance(current_list[i][0], list):
                    current_list[i] = modify_list(current_list[i])
                else:
                    # Recurse if it's not an innermost list
                    deep_modify(current_list[i])
            if isinstance(current_list[i], int):
                new = []
                new_keys = [key for key, value in target_dic_new.items() if value == current_list[i]]
                if len(new_keys) == 1:
                    for k in new_keys:
                        current_list[i] = k
                if len(new_keys) != 1:
                    new.append(new_keys)
            
                    current_list[i] = new
                print("sdas" + str(current_list))
                
                
        
            
        

    # Start the recursive modification process
    deep_modify(nested_list)
    return nested_list

def final_Step(cluster, dic):
    new_cluster = []
    remove_empty_lists_from_nested_list(cluster)
    remove_empty_lists_from_nested_list(dic)
    cluster_0 = []
    cluster_0.append(cluster[0][0])
    cc = 0
    
    final_append_1 = []
    final_append = []
    for OR_Cause in cluster[0][1::]:
        target_dic_1 = dic[0][cc][-1]
        
        
        for grouped in OR_Cause:
            changed_nodes = []
            for nodes in grouped:
                changed = [key for key, value in target_dic_1.items() if value == nodes]
                
                for i in changed:
                    changed_nodes.append(i)
            final_append_1.append(changed_nodes)
            
        cluster_0.append(final_append_1)
        final_append_1 = []
        cc += 1
    new_cluster.append(cluster_0)
    for i in range(1,len(cluster)):
        
        
        
        target_dic = dic[i-1][-1][-1]
        final_cluster = []
        for and_or_cause in cluster[i]:
            if and_or_cause == cluster[i][0]:
                three_party = []
                for grouped_nodes in and_or_cause:
                    
                    layer = i
                    new_group_nodes = []
                    new_group_dic = {}
                    for nodes in grouped_nodes:
                        keys = [key for key, value in target_dic.items() if value == nodes]
                        new_group_nodes.append(keys)
                        new_group_dic[nodes] = keys
                    
                    
                    while layer != 1:
                        new_new_group = []
                        newly_group = []
                        target_dic_new = dic[layer-2][-1][-1]
                        double_list = []
                        new_group_nodes = modify_and_reform(new_group_nodes,target_dic_new)
                        print('new ' + str(new_group_nodes))
                        '''
                        for j in new_group_nodes:
                            new_group_nodes_split = find_innermost_groups(j)
                            
                            print("split" + str(new_group_nodes_split))
                            for wrong_nodes_group in new_group_nodes_split:
                                for wrong_nodes in wrong_nodes_group:
                                    new_keys = [key for key, value in target_dic_new.items() if value == wrong_nodes]
                                
                                    new_new_group.append(new_keys)
                                    print(new_new_group)
                            double_list.append(new_new_group)
                            print("double_list" + str(double_list))
                            new_new_group= []
                        newly_group.append(double_list)
                            
                        new_group_nodes = newly_group
                        print("new_group_nodes11" + str(new_group_nodes))
                        '''
                        layer -= 1
                    print(222222)
                    print(str(i) + str(new_group_nodes))
                        ##correction
                    correct_group = []
                    correct = []
                    if i != 1:
                        
                        three_party.append(new_group_nodes)
                        
                    if i == 1:
                        three_party.append(new_group_nodes)
            if and_or_cause != cluster[i][0]:
                three_party = []
                target_dic_new = {}
                index = cluster[i].index(and_or_cause)
                for grouped_nodes in and_or_cause:
                    
                    layer = i
                    grouped_nodes = list(grouped_nodes)
                    new_group_dic = {}
                    
                        
                    count_inner_three = index - 1
                    new_target_dic = dic[i][count_inner_three][-1]
                    new_new_group = []
                    newly_group = []
                    
                    double_list = []
                    grouped_nodes = modify_and_reform(grouped_nodes,new_target_dic)
                    
                    print("first_layer: " + str(grouped_nodes))
                    while layer != 0:
                        if layer == 1:
                            target_dic_new = dic[0][-1][-1]
                        if layer != 1:
                            target_dic_new = dic[layer-1][-1][-1]
                    
                        grouped_nodes = modify_and_reform(grouped_nodes,target_dic_new)
                        
                        print("third_layer: " + str(grouped_nodes))
                        
                        layer -= 1
                        
                    
                    ##correction
                    correct_group = []
                    correct = []
                    if i != 1:
                    
                        three_party.append(grouped_nodes)
                    
                    if i == 1:
                        three_party.append(grouped_nodes)
            final_cluster.append(three_party)
        new_cluster.append(final_cluster)
    print(new_cluster)
            
            
    return new_cluster
#step 2
#bbb = final_Step(aaa,dic)


def tuples_to_lists(obj):
    if isinstance(obj, tuple):
        return list(obj)  # Convert tuple to list
    elif isinstance(obj, list):
        return [tuples_to_lists(item) for item in obj]  # Recursively apply to each item
    return obj
test_1 = [[[(0, 3), (2, 4), (5, 6), (7, 8), (9, 10), (11, 13), (14, 15), (16, 17), (18, 19), (20, 21), (22, 23), (24, 25), (26, 27), (28, 29), (31, 32), (33, 34)], [], [(2, 8)]], [[(0, 10), (1, 4), (5, 6), (7, 9), (11, 12), (13, 14), (15, 17)], [(4, 6)], [(3, 9)]], [[(0, 1), (2, 5), (6, 7)], [], [(2, 5)]], [[(0, 1)], [], []], [[], [], [(0, 1)]]]
test_1_dic = [[{31: 0, 32: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 11: 7, 13: 7, 12: 8, 14: 9, 15: 9, 16: 10, 17: 10, 18: 11, 19: 11, 20: 12, 21: 12, 22: 13, 23: 13, 24: 14, 25: 14, 26: 15, 27: 15, 28: 16, 29: 16, 30: 17, 33: 18, 34: 18}, {31: 0, 32: 0, 0: 1, 3: 1, 1: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 11: 7, 13: 7, 12: 8, 14: 9, 15: 9, 16: 10, 17: 10, 18: 11, 19: 11, 20: 12, 21: 12, 22: 13, 23: 13, 24: 14, 25: 14, 26: 15, 27: 15, 28: 16, 29: 16, 30: 17, 33: 18, 34: 18}, {31: 0, 32: 0, 0: 1, 3: 1, 1: 2, 12: 2, 2: 3, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 6, 10: 6, 11: 7, 13: 7, 14: 8, 15: 8, 16: 9, 17: 9, 18: 10, 19: 10, 20: 11, 21: 11, 22: 12, 23: 12, 24: 13, 25: 13, 26: 14, 27: 14, 28: 15, 29: 15, 30: 16, 33: 17, 34: 17}], [{7: 0, 9: 0, 0: 1, 10: 1, 1: 2, 4: 2, 2: 3, 3: 4, 5: 5, 6: 5, 8: 6, 11: 7, 12: 7, 13: 8, 14: 8, 15: 9, 17: 9, 16: 10}, {7: 0, 9: 0, 0: 1, 10: 1, 1: 2, 4: 2, 2: 3, 3: 4, 8: 4, 5: 5, 6: 5, 11: 6, 12: 6, 13: 7, 14: 7, 15: 8, 17: 8, 16: 9}, {7: 0, 9: 0, 0: 1, 10: 1, 1: 2, 4: 2, 2: 3, 16: 3, 3: 4, 8: 4, 5: 5, 6: 5, 11: 6, 12: 6, 13: 7, 14: 7, 15: 8, 17: 8}], [{6: 0, 7: 0, 0: 1, 1: 1, 2: 2, 5: 2, 3: 3, 4: 4, 8: 5}, {6: 0, 7: 0, 0: 1, 1: 1, 2: 2, 5: 2, 3: 3, 4: 4, 8: 5}, {6: 0, 7: 0, 0: 1, 1: 1, 2: 2, 5: 2, 3: 3, 8: 3, 4: 4}], [{1: 0, 2: 0, 0: 1, 3: 2, 4: 3}, {1: 0, 2: 0, 0: 1, 3: 2, 4: 3}, {1: 0, 2: 0, 0: 1, 3: 2, 4: 3}], [{}, {}, {0: 0, 1: 0, 2: 1, 3: 2}]]
#step 4
'''
converted_structure = tuples_to_lists(bbb)
print(converted_structure)
clusters_levels = [[[0, 1], [2, 5], [3, 4], [6, 7]],[[],[[0,1],[2,5]], [[3, 4], [6, 7]]],[[],[[[0,1],[2,5]],[[3,4], [6,7]]]]]
     '''   


def list_to_tuple(obj):
    """
    Recursively convert lists to tuples, including nested lists.
    Unpack single-item lists to avoid nested single-item tuples.
    """
    if isinstance(obj, list):
        # Convert the list items recursively
        converted = tuple(list_to_tuple(item) for item in obj)
        # If the converted tuple has only one item, unpack it
        if len(converted) == 1:
            return converted[0]
        else:
            return converted
    else:
        return obj

def extract_third_layer(nested_list):
    current_item = nested_list
    depth = 0  # Initialize depth
    # Loop until the third layer is reached
    while isinstance(current_item, list) and depth < 3:
        if len(current_item) == 0:  # Check if the current list is empty to avoid an IndexError
            break
        current_item = current_item[0]  # Update current_item to its first element
        depth += 1  # Increment depth after moving down a layer
    return current_item


def construct_linkage_matrix(original_dic, original_cluster, cluster_dic, linkage_matrix):
    layer = 1
    count = -1
    for keys in original_dic[0][0]:
        cluster_dic[keys] = keys
    
    for three_party in original_cluster:
        record = layer/len(original_cluster)
        
        for cluster in three_party:
            for grouped_nodes in cluster:
                
                
                if len(grouped_nodes) != 0:
                    
                    cluster_dic[list_to_tuple(grouped_nodes)] = max(cluster_dic.values()) + 1
                    
                    if len(grouped_nodes) > 1 and len(grouped_nodes) <=2:
                        print(grouped_nodes)
                        if list_to_tuple(grouped_nodes[0]) not in cluster_dic.keys():
                            cluster_dic[list_to_tuple(grouped_nodes[0])] = max(cluster_dic.values()) + 1
                        if list_to_tuple(grouped_nodes[1]) not in cluster_dic.keys():
                            cluster_dic[list_to_tuple(grouped_nodes[1])] = max(cluster_dic.values()) + 1
                        linkage_matrix.append([cluster_dic[list_to_tuple(grouped_nodes[0])],cluster_dic[list_to_tuple(grouped_nodes[1])],record,len(grouped_nodes)])
                    if len(grouped_nodes) == 1:
                        print(grouped_nodes)
                        
                        target_element = extract_third_layer(grouped_nodes)

                        if isinstance(target_element, int):
                            continue
                        if len(target_element) == 1:
                            continue
                        linkage_matrix.append([cluster_dic[list_to_tuple(target_element[0])],cluster_dic[list_to_tuple(target_element[1])],record,len(grouped_nodes)]) 
        layer+=1
    
    count11 = 1
    flattened_list = [item for sublist in linkage_matrix for item in sublist]
    
    print(cluster_dic)
    return linkage_matrix




distance_increment = 1.0

# Function to flatten nested lists
def flatten(list_of_lists):
    for item in list_of_lists:
        if isinstance(item, list):
            yield from flatten(item)
        else:
            yield item

# Process each level of clustering

def plot_dendrogram(cluster, dic, timee):
    dic2 = [[dic22 for sublist in outerlist for dic22 in sublist] for outerlist in dic]
    #aaa = transfer_to_previous(cluster,dic)
    bbb = final_Step(cluster,dic)
    converted_structure = tuples_to_lists(bbb)
    linkage_matrix = construct_linkage_matrix(dic2,converted_structure,{},[])
    
    print(linkage_matrix)
    
    plt.figure(figsize=(10, 7))  # You can adjust the figure size as needed
    dendrogram(linkage_matrix)
    
    # Save the figure with a specified dpi for resolution
    plt.savefig(f'dendrogram_plot_{timee}.png', dpi=300)
    
    # Close the plot to ensure it does not interfere with any future plots
    plt.close()
    
    '''
# Convert to numpy array with dtype=float
linkage_matrix = np.array(linkage_matrix, dtype=float)
dendrogram(linkage_matrix)
'''

# Process each level of clusters

        
# Ensure all entries are floats and convert to a numpy array
#linkage_matrix = np.array(linkage_matrix, dtype=float)

#print(linkage_matrix)

# Applying the transformation
'''
linkage_matrix = np.array([
    [0, 1, 0.1, 1],  # Merge nodes 0 and 1 -> forms cluster 6
    [2, 3, 0.1, 2],  # Merge nodes 2 and 3 -> forms cluster 7
    [4, 7, 0.2, 3],  # Merge node 4 with cluster 7 (nodes 2 and 3) -> forms cluster 8
    [6, 8, 0.2, 4],  # Merge cluster 6 (nodes 0 and 1) with cluster 8 (nodes 2, 3, 4) -> forms cluster 9
    [5, 9, 0.2, 5],  # Merge node 5 with cluster 9 (nodes 0, 1, 2, 3, 4) -> final structure
], dtype=float)
'''

# Generate the dendrogram
 # Optional: Adjust figure size
#dendrogram(linkage_matrix)

#plt.title('Network Merges Dendrogram')
#plt.xlabel('Node or Group ID')
#plt.ylabel('Distance or Merge Order')
#plt.show()  # This will display the plot
