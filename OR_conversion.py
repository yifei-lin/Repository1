import random
import numpy as np
from Grouping_Recorder import GroupingRecorder
import pandas as pd
def find_completely_isolated_nodes(adj_matrix):
    completely_isolated_indices = []
    for i in range(len(adj_matrix)):
        # Check if the row and column at index i are all zeros
        if all(value == 0 for value in adj_matrix[i]) and all(adj_matrix[j][i] == 0 for j in range(len(adj_matrix))):
            completely_isolated_indices.append(i)
    return completely_isolated_indices   
#### AND gate conversion
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
def flatten_grouped_nodes(grouped_nodes):
    flattened = []
    for item in grouped_nodes:
        if isinstance(item, tuple):
            flattened.extend(item)
        else:
            flattened.append(item)
    return flattened  

def group_OR_gate_nodes(adj_matrix, grouped_nodes, ungrouped, already_grouped, recorder):
    
    n = len(adj_matrix[-1])
    
    grouped_set = set()
    count = 0
    
    for i in already_grouped:
        if isinstance(i, list):  # Check if the element is a list
            for j in i:
                grouped_set.add(j)
        else:
            grouped_set.add(i)

    # Iterate through the matrix to find OR gate connections and group nodes
    for i in range(n):
        if i in grouped_set:
            continue

        for j in range(i + 1, n):
            if j in grouped_set:
                continue
            
            # Check if both nodes i and j point to the same node with OR relationship
            common_targets = [k for k in range(n) if adj_matrix[-1][i][k] == 1 and adj_matrix[-1][j][k] == 1]
            if common_targets:
                grouped_nodes.append((i, j))
                grouped_set.add(i)
                grouped_set.add(j)
                recorder.record(i, j, 'new_group_id')
                count+=1# Record the operation
                break

    # Update ungrouped nodes
    if count > 0:
        ungrouped -= grouped_set
    
    
    return grouped_nodes, list(ungrouped)

def OR_Gate_Conversion(original_matrix, adj_matrix, grouped_nodes, ungrouped, already_grouped, node_mapping, recorder,final_order_grouped,final_node_dic):
    print("already_grouped: "+ str(already_grouped))

    previous_grouped = already_grouped.copy()
    grouped_nodes, ungrouped = group_OR_gate_nodes(adj_matrix, grouped_nodes, ungrouped, already_grouped, recorder)
    
    print('getting_OR_grouped_nodes: ' + str(grouped_nodes))
    print('getting_OR_ungrouped_nodes: ' + str(ungrouped))
    if len(grouped_nodes) == 0:
        
        return adj_matrix, grouped_nodes, ungrouped, already_grouped, set(ungrouped), node_mapping,final_order_grouped,[], final_node_dic
    
    n = len(adj_matrix[0])
    stored_matrix = np.copy(adj_matrix[-1])
    original = np.copy(adj_matrix[0])
    
    grouped_node_count = len(grouped_nodes)
    check_grouped = []
    for i in grouped_nodes:
        check_grouped.append(i)
    new_n = n - grouped_node_count  # Decrease size for each grouped pair

    # Create a mapping from old to new node indices                         
    
    new_index = 0
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
            
            
            n = len(original)
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
            length = len(find_completely_isolated_nodes(new_adj_matrix))
            if length > 0:
                
                print('here is 0 nodes: ' + str(find_completely_isolated_nodes(new_adj_matrix)))
                print(node_mapping)
                df1 = pd.DataFrame(new_adj_matrix)
                df2 = pd.DataFrame(stored_matrix)
                excel_file_path = 'adjacency_matrix_okok.xlsx'
                excel_writer = pd.ExcelWriter(excel_file_path, engine='openpyxl')
                
                # Write the DataFrame to two sheets within the same Excel file
                df1.to_excel(excel_writer, sheet_name='Sheet1', index=False, header=False)
                df2.to_excel(excel_writer, sheet_name='Sheet2', index=False, header=False)


                excel_writer.save()
            
        node_mapping = node_mapping_new
    
                            
                   
                
                    
                
                   
       
            
            #if len(check_list) != 0:
             #   print(111111)
              #  for j in range(n):
               #     new_j = node_mapping[j]
                #    
                 #   if adj_matrix[i][j] > 1:
                  #      print(i,j)
                  #      new_adj_matrix[new_i][new_j] = min(new_adj_matrix[new_i][new_j], adj_matrix[i][j] - 1)
                   #     print(adj_matrix[i][j] - 1)
                        
            #check = 0
        
    node_mapping_final = node_mapping.copy()
   
    add_on_1 = []
    count = 0
    if len(already_grouped) > 0:
        
        while check_grouped:
            selected_tuple = random.choice(check_grouped)
            check_grouped.remove(selected_tuple)
            final_order_grouped.append(selected_tuple)
            n = len(adj_matrix[-1])
            min_value = min(selected_tuple) #28
           
            for j in selected_tuple: #(28,31)
                if count == 0:
                    
                    keys_for_value = [key for key, value in node_mapping_final.items() if value == j]
                    for key in keys_for_value:
                    
                        node_mapping[key] = min_value
                    count += 1
                elif count != 0:
                    keys_for_value = [key for key, value in node_mapping_final.items() if value == j] # 34,36
                    min_key = 0 #36
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
            length = len(find_completely_isolated_nodes(new_adj_matrix))
            length_2 = len(find_completely_isolated_nodes(stored_matrix))
            if length_2 > 0:
                                
                print('here is 0 nodes: ' + str(find_completely_isolated_nodes(stored_matrix)))
                print(node_mapping)
                df1 = pd.DataFrame(new_adj_matrix)
                df2 = pd.DataFrame(stored_matrix)
                excel_file_path = 'adjacency_matrix_okok_1.xlsx'
                excel_writer = pd.ExcelWriter(excel_file_path, engine='openpyxl')
                
                # Write the DataFrame to two sheets within the same Excel file
                df1.to_excel(excel_writer, sheet_name='Sheet1', index=False, header=False)
                df2.to_excel(excel_writer, sheet_name='Sheet2', index=False, header=False)


                excel_writer.save()
                
            if length > 0:
                
                print('here is 0 nodes: ' + str(find_completely_isolated_nodes(new_adj_matrix)))
                print(node_mapping)
                df1 = pd.DataFrame(new_adj_matrix)
                df2 = pd.DataFrame(stored_matrix)
                excel_file_path = 'adjacency_matrix_okok.xlsx'
                excel_writer = pd.ExcelWriter(excel_file_path, engine='openpyxl')
                
                # Write the DataFrame to two sheets within the same Excel file
                df1.to_excel(excel_writer, sheet_name='Sheet1', index=False, header=False)
                df2.to_excel(excel_writer, sheet_name='Sheet2', index=False, header=False)


                excel_writer.save()
        
        
        '''
        count1 = 100000000
        n = len(original_matrix[-1])
        add_on = []
        for value_to_remove in flattened_grouped_nodes:
            for i in node_mapping.keys():
                if node_mapping[i] == value_to_remove:
                    add_on.append(i)
                    
            node_mapping_final = {k: v for k, v in node_mapping.items() if v != value_to_remove}
       
        node_index = []
        
        print(add_on)
        add_on_1 = add_on
        add_on_list = [(add_on[i], add_on[i+1]) if i + 1 < len(add_on) else (add_on[i],) for i in range(0, len(add_on), 2)]

        print("!!!!!!!" + str(add_on_list))
        count = 0
        for i in add_on_list:
            for j in i:
                node_mapping_final[j] = min(list(grouped_nodes[count]))
            count += 1
                
        print(node_mapping_final)
        print(add_on_list)
        sorted_items = sorted(node_mapping_final.items())
        node_mapping_final = dict(sorted_items)
        node_mapping_final = dict(sorted(node_mapping_final.items(), key=lambda item: item[1]))
        node_mapping_final = adjust_to_continuous(node_mapping_final)
        #node_mapping_final = make_values_continuous(node_mapping_final)
        #print(node_mapping_final)
        '''
        '''
        new_values = {}
        current_value = 0
        for key, value in node_mapping_final:
            print(key,value)
            if value not in new_values:
                new_values[value] = current_value
                current_value += 1
        print(new_values)
        
        final_map = {key: new_values[value] for key, value in node_mapping_final}
        print(final_map)
        '''
         
        '''
        new_adj_matrix = np.zeros((new_n, new_n))
        already_grouped = flatten_grouped_nodes(already_grouped)   
        print(node_mapping_final)
        print(already_grouped)
        print(node_mapping)
        n = len(original_matrix[-1])
        for i in range(n):
            new_i = node_mapping_final[i]
            neww_i = node_mapping[i]
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
                    if stored_matrix[neww_i][neww_j] == 1:
                    
                        if new_i != new_j:
                            new_adj_matrix[new_i][new_j] = stored_matrix[neww_i][neww_j]
                    
                    if stored_matrix[neww_i][neww_j] > 1:
                        if new_i != new_j:
                            new_adj_matrix[new_i][new_j] = stored_matrix[neww_i][neww_j]
                    for grouped_tuple in check_grouped:
                        if neww_i in grouped_tuple:
                                
                            adj_matrix.append(new_adj_matrix)
                            count1 = check_grouped.index(grouped_tuple)
                                
                        if count1 != 100000000:
                            check_grouped.pop(count1)
                        count1 = 100000000
            '''
            
        
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
        for k in already_grouped:
            keys = [key for key, value in node_mapping_final.items() if value == k]
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
    return adj_matrix, grouped_nodes, ungrouped, list(final_grouped_nodes), final_ungrouped, final_node_dic_1, final_order_grouped,I_want,final_node_dic