from tkinter import *
from tkinter import filedialog
import networkx as nx
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
from PIL import Image
from scipy.integrate import simps
from scipy.stats import skew
import xlsxwriter
import re
import tkinter as tk
import matplotlib
from datetime import datetime
from tqdm import tqdm
import seaborn as sns; sns.set_theme(color_codes=True)
import copy
from mpl_toolkits.axes_grid1 import make_axes_locatable
import random
from networkx.readwrite import json_graph
import json
from collections import OrderedDict

matplotlib.use('TkAgg')

from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg


class Matrix():
    def __init__(self, excel_name, node_weight: dict, node_ID: dict):
        """
        Construct an adjacency matrix with node_id,node_weight saved.

        Parameters:
        excel_name: A string shows the file needs to be read.
        node_weight: An emtpy Dictionary at initial, contains nodes weighting info.
        node_ID: An emtpy Dictionary at initial, contains nodes ID.
        """
        self._excel_name = excel_name
        self._node_weight = node_weight
        self._node_ID = node_ID
        self._df = self.read_sheet(self._excel_name)
        self._gather_list = []
        self._adjacency_matrix = []
        self._removed_nodes = []
        self.gcm()
        

    def read_sheet(self, file_name, skiprows=0):
        """(pd.dataframe): Returns the first sheet of the excel file"""
        ## Read the input excel sheet with file_name given and return a dataframe.
        ## Pandas in use
        df = pd.read_excel(file_name, skiprows=skiprows)
        return df
    
    def update_matrix(self,adjacency_matrix):
        self._adjacency_matrix = adjacency_matrix
        
    def update_node_weight(self,node_weight):
        self._node_weight = node_weight
        
    def update_node_ID(self,node_ID):
        self._node_ID = node_ID
        
    def update_gather_list(self,gather_list):
        self._gather_list = gather_list
        
    def update_removed_nodes(self,removed_nodes):
        self._removed_nodes = removed_nodes

    def checkSame(self, nodeName, dictionaryName):
        """(Boolean): Returns true while nodeName's lower cases equals any keys inside input dictionary.
                      Returns false while no matches.
        """
        for i in dictionaryName.keys():
            if nodeName.lower() == i.lower():
                return True
        return False

    def splitWeight(self, nodeWeight, node, weight, bracketOR, bracketAND):
        """ Split input node string and weight them.

        Parameters:
            nodeWeight (Dictionary): Contains Node elements correspond to their node_ID
            node (String): Excel block elements contains node element (Usually contains more than one node element)
            weight (Int): Initial set to zero.
            bracketOR(Int): Initial set to zero.
            bracketAND(Int): Initial set to zero.
        """
        if ' AND ' not in node and ' OR ' not in node:
            if '(' in node and ')' not in node:
                nodesDeviation = node.split('(')[1]
                nodeWeight[nodesDeviation] = weight
            elif ')' in node and '(' not in node:
                nodesDeviation = node.split(')')[0]
                nodeWeight[nodesDeviation] = weight
            elif '(' in node and ')' in node:
                nodesDeviation = node.split('(')[1]
                nodesDDeviation = nodesDeviation.split(')')[0]
                nodeWeight[nodesDDeviation] = weight
            else:
                nodeWeight[node] = weight
        if ' OR ' in node:
            if bracketOR == 0:
                ## split OR outside brackets
                a = re.split(r' OR \s*(?![^()]*\))', node)
                for i in a:
                    self.splitWeight(nodeWeight, i, weight, bracketOR + 1, bracketAND)
            elif bracketOR > 0:
                if '(' not in node:
                    nodesDeviation = node.split(' OR ')
                    for j in nodesDeviation:
                        self.splitWeight(nodeWeight, j, weight, bracketOR, bracketAND)
                else:
                    ## split AND outside brackets
                    a = re.split(r' AND \s*(?![^()]*\))', node)
                    for i in a:
                        if '(' in i:
                            nodesDeviation = i.split('(')[1]
                            nodesDDeviation = nodesDeviation.split(')')[0]
                            self.splitWeight(nodeWeight, nodesDDeviation, weight + len(a) - 1, bracketOR + 1,
                                             bracketAND + 1)
                        else:
                            self.splitWeight(nodeWeight, i, weight + len(a) - 1, bracketOR + 1, bracketAND + 1)
        if ' AND ' in node and ' OR ' not in node:
            if bracketAND == 0:
                ## split AND outside brackets
                a = re.split(r' AND \s*(?![^()]*\))', node)
                if len(a) == 1:
                    self.splitWeight(nodeWeight, str(a), weight, bracketOR, bracketAND + 1)
                else:
                    for i in a:
                        self.splitWeight(nodeWeight, i, weight + len(a) - 1, bracketOR, bracketAND + 1)
            elif bracketAND == 1:
                nodesDeviation = node.split(' AND ')
                for j in nodesDeviation:
                    self.splitWeight(nodeWeight, j, weight + len(nodesDeviation) - 1, bracketOR, bracketAND)

    def splitID(self, node, bracketOR, bracketAND,splitID_recursion_count=0):
        """ Split input node string and number them.

        Parameters:
            node (String): Excel block elements contains node element (Usually contains more than one node element)
            bracketOR(Int): Initial set to zero.
            bracketAND(Int): Initial set to zero.
        """
        if splitID_recursion_count>100:
            print("SplitID() node: {}".format(node))
            raise NameError("splitID() Recursion Error")
        count = 0
        if 'AND' not in node and 'OR' not in node:
            if '(' in node and ')' not in node:
                nodesDeviation = node.split('(')[1]
                if not self.checkSame(nodesDeviation, self._node_ID):
                    self._node_ID[nodesDeviation] = count + len(self._node_ID)
                    count += 1

            elif ')' in node and '(' not in node:
                nodesDeviation = node.split(')')[0]
                if not self.checkSame(nodesDeviation, self._node_ID):
                    self._node_ID[nodesDeviation] = count + len(self._node_ID)
                    count += 1

            elif '(' in node and ')' in node:
                nodesDeviation = node.split('(')[1]
                nodesDDeviation = nodesDeviation.split(')')[0]
                if not self.checkSame(nodesDDeviation, self._node_ID):
                    self._node_ID[nodesDDeviation] = count + len(self._node_ID)
                    count += 1

            else:
                if not self.checkSame(node, self._node_ID):
                    a = len(self._node_ID)
                    self._node_ID[node] = count + a
                    count += 1

        if 'OR' in node:
            if bracketOR == 0:
                ## split OR outside brackets
                a = re.split(r' OR \s*(?![^()]*\))', node)
                for i in a:
                    self.splitID(i, bracketOR + 1, bracketAND,splitID_recursion_count+1)
            elif bracketOR == 1:
                nodesDeviation = node.split(' OR ')
                for j in nodesDeviation:
                    self.splitID(j, bracketOR, bracketAND,splitID_recursion_count+1)
        if 'AND' in node and 'OR' not in node:
            if bracketAND == 0:
                ## split AND outside brackets
                a = re.split(r' AND \s*(?![^()]*\))', node)
                if len(a) == 1:
                    self.splitID(str(a), bracketOR, bracketAND + 1,splitID_recursion_count+1)
                else:
                    for i in a:
                        self.splitID(i, bracketOR, bracketAND + 1,splitID_recursion_count+1)
            elif bracketAND == 1:
                nodesDeviation = node.split(' AND ')
                for j in nodesDeviation:
                    self.splitID(j, bracketOR, bracketAND,splitID_recursion_count+1)

    def splitIDD(self, node_IDD, node, bracketOR, bracketAND):
        """ Split input node string and number them.

        Parameters:
            node_IDD(Dictionary): Node elements correspond to their IDs (Rows)
            node (String): Excel block elements contains node element (Usually contains more than one node element)
            bracketOR(Int): Initial set to zero.
            bracketAND(Int): Initial set to zero.
        """
        count = 0
        if 'AND' not in node and 'OR' not in node:
            if '(' in node and ')' not in node:
                nodesDeviation = node.split('(')[1]
                if not self.checkSame(nodesDeviation, node_IDD):
                    node_IDD[nodesDeviation] = count + len(node_IDD)
                    count += 1

            elif ')' in node and '(' not in node:
                nodesDeviation = node.split(')')[0]
                if not self.checkSame(nodesDeviation, node_IDD):
                    node_IDD[nodesDeviation] = count + len(node_IDD)
                    count += 1

            elif '(' in node and ')' in node:
                nodesDeviation = node.split('(')[1]
                nodesDDeviation = nodesDeviation.split(')')[0]
                if not self.checkSame(nodesDDeviation, node_IDD):
                    node_IDD[nodesDDeviation] = count + len(node_IDD)
                    count += 1

            else:
                if not self.checkSame(node, node_IDD):
                    node_IDD[node] = count + len(node_IDD)
                    count += 1

        if 'OR' in node:
            if bracketOR == 0:
                ## split OR outside brackets
                a = re.split(r' OR \s*(?![^()]*\))', node)
                for i in a:
                    self.splitIDD(node_IDD, i, bracketOR + 1, bracketAND)
            elif bracketOR == 1:
                nodesDeviation = node.split(' OR ')
                for j in nodesDeviation:
                    self.splitIDD(node_IDD, j, bracketOR, bracketAND)
        if 'AND' in node and 'OR' not in node:
            if bracketAND == 0:
                ## split AND outside brackets
                a = re.split(r' AND \s*(?![^()]*\))', node)
                if len(a) == 1:
                    self.splitIDD(node_IDD, str(a), bracketOR, bracketAND + 1)
                else:
                    for i in a:
                        self.splitIDD(node_IDD, i, bracketOR, bracketAND + 1)
            elif bracketAND == 1:
                nodesDeviation = node.split(' AND ')
                for j in nodesDeviation:
                    self.splitIDD(node_IDD, j, bracketOR, bracketAND)

    def gatherNode(self, list_cus, causeNode, times):
        """ Create the input 'list_cus' as a list storing node relations.
            This list is mainly used for nodes elmination.

        Parameters:
            list_cus(List): Initial empty list, with [a,b] showing a cause b.
            causeNode (String): Excel block elements contains node element (Usually contains more than one node element)
            times(Int): Initial set to zero.
        """
        list_1 = []
        list_22 = []
        if '(' not in causeNode and ')' not in causeNode:
            if 'AND' in causeNode:
                a = causeNode.split(' AND ')
                for i in a:
                    list_1.append(i)
                list_cus.append(list_1)
            elif 'OR' in causeNode:
                a = causeNode.split(' OR ')
                for i in a:
                    list_1.append(i)
                    list_cus.append(list_1)
                    list_1 = []
            else:
                list_1.append(causeNode)
                list_cus.append(list_1)
        if '(' in causeNode:
            ## split OR outside brackets
            a = re.split(r' OR \s*(?![^()]*\))', causeNode)
            if len(a) == 1:
                for x in a:
                    if 'OR' in x:
                        ## split AND outside brackets
                        b = re.split(r' AND \s*(?![^()]*\))', causeNode)
                        for i in b:
                            nodesDeviation = i.split('(')[1]
                            nodesDDeviation = nodesDeviation.split(')')[0]
                            if 'OR' in nodesDDeviation:
                                c = nodesDDeviation.split(' OR ')
                                for j in c:
                                    list_22.append(j)
                                list_1.append(list_22)
                                list_22 = []
                                
                            elif 'AND' in nodesDDeviation:
                                c = nodesDDeviation.split(' AND ')
                                for j in c:
                                    list_1.append(j)
                            else:
                                list_1.append(nodesDDeviation)
                        list_cus.append(list_1)
                    else:
                        ## split AND outside brackets
                        b = re.split(r' AND \s*(?![^()]*\))', x)
                        for y in b:
                            nodesDeviation = y.split('(')[1]
                            nodesDDeviation = nodesDeviation.split(')')[0]
                            if 'AND' in nodesDDeviation:
                                c = nodesDDeviation.split(' AND ')
                                for z in c:
                                    list_1.append(z)
                            else:
                                list_1.append(nodesDDeviation)
                        list_cus.append(list_1)
            elif len(a) != 1:
                if times == 0:
                    for i in a:
                        self.gatherNode(list_cus, i, times + 1)
                else:
                    if '(' in i:
                        nodesDeviation = i.split('(')[1]
                        nodesDDeviation = nodesDeviation.split(')')[0]
                        self.gatherNode(list_cus, nodesDDeviation, times)
                    else:
                        list_1.append(i)
                        list_cus.append(list_1)

    def deleteNode(self, node_no: list):
        """ Delete the node inside the node_no from adjacency matrix.

        Parameters:
            node_no(List): Nodes waited to be eliminated.
        """
        
        gather_list_two = self._gather_list.copy()
        if len(node_no) == 0:
            self._gather_list = gather_list_two
            G = nx.DiGraph(directed=True)
            
            print("[{}] started get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
            for i in range(len(self._adjacency_matrix)):
                for j in range(len(self._adjacency_matrix)):
                    weight=int(self._adjacency_matrix[i][j])
                    if weight>0:
                        
                        G.add_edge(str(i), str(j),weight=weight)
            
            print("[{}] finished get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
            print(len(G))
            
        else:
            
            for j in range(len(self._adjacency_matrix)):
                ##The relations showing nodes point to the eliminated node should be removed.
                self._adjacency_matrix[j][int(node_no[0])] = 0
                #print(self._adjacency_matrix)
            for mid_lis in self._gather_list:
                mid_list = copy.deepcopy(mid_lis)
                
                if all(isinstance(item, int) for item in mid_list[0]):
                   
                    if int(node_no[0]) in mid_list[0]:
                        print(1234)
                        nodes_in_and_gate = set(mid_list[0])  # Set of nodes in the AND gate
                        target_node = mid_list[1]  # The target node connected by the AND gate
                        print(nodes_in_and_gate)
                        all_and_gates = [item for item in self._gather_list if isinstance(item[0], list) and len(item[0]) > 1]
                        other_and_gates_pointing = [gate for gate in all_and_gates if mid_list[1] == gate[1] and mid_list != gate]
                        
                        # Remove the connection between nodes in the AND gate and the target node
                        for node in nodes_in_and_gate:
                            if isinstance(node, int) and node == int(node_no[0]):
                                self._adjacency_matrix[node][target_node] = 0
                            elif isinstance(node, list):
                                for list_item in node:
                                    if list_item == int(node_no[0]):
                                        self._adjacency_matrix[list_item][target_node] = 0

                        # Remove the nodes in the AND gate if they are not in any other AND gate pointing to the same target node
                        nodes_to_remove = nodes_in_and_gate.copy()
                        if len(other_and_gates_pointing) == 0:
                            for i in nodes_in_and_gate:
                                self._adjacency_matrix[i][target_node] = 0
                        for item in other_and_gates_pointing:
                            for i in nodes_in_and_gate:
                                if i != target_node and i not in item[0]:
                                    
                                    self._adjacency_matrix[i][target_node] = 0
                        node_no.append(mid_list[1])
                        gather_list_two.remove(mid_list)

                else:
                    
                    #print('2nd')
                    #print(self._gather_list)
                    
                    if int(node_no[0]) in mid_list[0]:
                        print(222222222222222)
                        for i in mid_list[0]:
                            if isinstance(i, int):
                                self._adjacency_matrix[i][mid_list[1]] = 0
                            if isinstance(i, list):
                                for list_item in i:
                                    self._adjacency_matrix[list_item][mid_list[1]] = 0
                        ## The relations showing nodes caused by eliminated nodes should also be removed.
                        node_no.append(mid_list[1])
                        gather_list_two.remove(mid_list)
                    elif int(node_no[0]) not in mid_list[0]:
                        print(222222233333332222222)
                        for kk in mid_list[0]:
                            
                            if isinstance(kk, list):
                                if len(kk) == 0:
                                    node_no.append(mid_list[1])
                                    gather_list_two.remove(mid_list)
                                    break
                                else:
                                    for list_item_1 in kk:
                                        if list_item_1 == int(node_no[0]):
                                           
                                            self._adjacency_matrix[list_item_1][mid_list[1]] = 0
                                            
                                            index_mid_list = self._gather_list.index(mid_list)
                                            aaa = copy.deepcopy(kk)
                                            cc = copy.deepcopy(mid_list[0].index(kk))
                                            mid_list[0].remove(aaa)
                                            
                                            aaa.remove(list_item_1)
                                            mid_list[0].insert(cc, aaa)
                                           
                                            self._gather_list[index_mid_list] = mid_list
                                        
            node_no.pop(0)
             
            for mid_list in gather_list_two:
                for node_check in node_no:
                    if mid_list[1] == node_check:
                        node_no.remove(node_check)
            self._gather_list = gather_list_two
            print(self._gather_list)
            self.deleteNode(node_no)

    def gcm(self):
        """ Create the Adjacency Matrix."""
        df = self._df
        name = []
        for col in list(df.columns):
            name.append(col)
        df = df[[name[0], name[1], name[2]]]
        for index, row in df.iterrows():
            
            try:
                if row[name[0]] != 'None':
                    self.splitID(row[name[0]].rstrip(), 0, 0)
                if row[name[1]] != 'None':
                    self.splitID(row[name[1]].rstrip(), 0, 0)
                if row[name[2]] != 'None':
                    self.splitID(row[name[2]].rstrip(), 0, 0)
            except:
                print(index)
                print(name[0])
                print(row[name[0]])
                print(name[1])
                print(row[name[1]])
                print(name[2])
                print(row[name[2]])
                raise NameError("Gordon")
                
        ## Set initial size of the adjacency matrix.
        adjacency_matrix = np.zeros((len(self._node_ID), len(self._node_ID)))
        for index, row in df.iterrows():

            ## The second column and the first column
            node_Weight1 = {}
            node_IDD1 = {}
            list_cus = []

            ##Get node weight
            self.splitWeight(node_Weight1, row[name[1]].rstrip(), 1, 0, 0)
            ##Get node ID
            self.splitIDD(node_IDD1, row[name[0]].rstrip(), 0, 0)
            ##split node for delete_node function
            self.gatherNode(list_cus, row[name[1]].rstrip(), 0)
            count = 0
            count1 = 0
            
            for a in list_cus:
                for b in a:
                    if isinstance(b, str):
                        for k in self._node_ID.keys():
                            if b.lower() == k.lower():
                                a[count] = self._node_ID[k]
                                count += 1
                    elif isinstance(b, list):
                        for kk in b:
                            for k in self._node_ID.keys():
                                if isinstance(kk, str):
                                    if kk.lower() == k.lower():
                                        
                                        a[count][count1] = self._node_ID[k]
                                      
                                        count1 += 1
                                    
                        count += 1
                        count1 = 0
                count = 0
            ## Create the relationship list (gather_list) mainly used for nodes elimination
            for aa in node_IDD1.keys():
                for bb in self._node_ID.keys():
                    if aa.lower() == bb.lower():
                        cc = self._node_ID[bb]
                        for xx in list_cus:
                            list_2 = [xx, cc]
                            self._gather_list.append(list_2)
            ## start creating adjacency matrix
            for i in node_Weight1.keys():
                for k in self._node_ID.keys():
                    if i.lower() == k.lower():
                        x = self._node_ID[k]
                        for j in node_IDD1.keys():
                            for l in self._node_ID.keys():
                                if j.lower() == l.lower():
                                    y = self._node_ID[l]
                                    adjacency_matrix[x, y] = node_Weight1[i]

            ## The first column and the third column
            node_Weight2 = {}
            node_IDD2 = {}
            list_cus_1 = []
            self.splitWeight(node_Weight2, row[name[0]].rstrip(), 1, 0, 0)
            self.splitIDD(node_IDD2, row[name[2]].rstrip(), 0, 0)
            self.gatherNode(list_cus_1, row[name[0]].rstrip(), 0)
            count = 0
            for a in list_cus_1:
                for b in a:
                    for k in self._node_ID.keys():
                        if isinstance(b, str):
                            if b.lower() == k.lower():
                                a[count] = self._node_ID[k]
                                count += 1
                        elif b is list:
                            for kk in b:
                                if isinstance(kk, str):
                                    if kk.lower() == k.lower():
                                        a[count] = self._node_ID[k]
                                        count += 1
                                else:
                                    a[count] = self._node_ID[k]
                                    count+=1
                count = 0
            ## Create the relationship list (gather_list) mainly used for nodes elimination
            for aa in node_IDD2.keys():
                for bb in self._node_ID.keys():
                    if aa.lower() == bb.lower():
                        cc = self._node_ID[bb]
                        for xx in list_cus_1:
                            list_2 = [xx, cc]
                            self._gather_list.append(list_2)
            ## start creating adjacency matrix
            for m in node_Weight2.keys():
                for o in self._node_ID.keys():
                    if m.lower() == o.lower():
                        u = self._node_ID[o]
                        for n in node_IDD2.keys():
                            for p in self._node_ID.keys():
                                if n.lower() == p.lower():
                                    v = self._node_ID[p]
                                    adjacency_matrix[u, v] = node_Weight2[m]
        self._adjacency_matrix = adjacency_matrix
        print(self._gather_list)
        

    def adjacency_matrix(self):
        return self._adjacency_matrix
    
    def change_matrix(self, matrix):
        self._adjacency_matrix = matrix

    def get_gather_list(self):
        return self._gather_list

    def get_node_ID(self):
        return self._node_ID


class digraphPlot(tk.Canvas, tk.Frame):

    def __init__(self, master, delete_node=[], node_weight={}, node_ID={}):
        """
        Construct a view from a Matrix.
        Parameters:
        master (tk.Widget): Widget within which the frame is placed.
        delete_node(list): An emtpy list at initial, contains nodes need to be deleted.
        node_weight(Dictionary): An emtpy Dictionary at initial, contains nodes weighting info.
        node_ID(Dictionary): An emtpy Dictionary at initial, contains nodes ID.
        """
        super().__init__(master)

        self._node_weight = node_weight
        self._node_ID = node_ID
        self._delete_node = delete_node
        self._master = master
        self._excel_name = self.load_excel()
        print("[{}] Creating adjacency Matrix".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
        self._adjacency_matrix = self._matrix.adjacency_matrix()
        self._node_ID = self._matrix.get_node_ID()
        self._digraph_normal = self.get_Digraph()
        self._digraph_normal_nocolor = self.get_Digraph_Nocolor()
        self._pos = nx.nx_agraph.graphviz_layout(self._digraph_normal)
        self.add_menu()
        self._frame_one = tk.Frame(self._master, bg='grey', width=3000, height=1800)
        self._frame_one.pack(side=tk.LEFT, expand=1, anchor=tk.W)
        self.plot_Digraph_initial()
        self._frame_two = tk.Frame(self._master, bg='grey')
        self._frame_two.pack()
        
        self.options = ["Degree", "In_Degree", "Out_Degree", "Strength", "In_Strength", "Out_Strength", "Eigenvector", 
                                 "In_Closeness", "Out_Closeness", "Betweenness", "Relative_Likelihood", "Causal_Contribution"]
        self._frame_two = tk.Frame(self._master, bg='grey')
        self._frame_two.pack()
        self.add_button()
        self.clicked = StringVar()
        self.clicked.set("Degree")
        drop = OptionMenu( self._frame_two , self.clicked , *self.options)
        drop.config(width=100)
        drop.pack()
        button_colormap = Button( self._frame_two , text = "colormap" , command = self.show_colormap, width=100).pack()
        button_plot_colormap_total = Button(self._frame_two, text="plot_colormap_total", command=self.plot_colormap_total,width=100).pack()
        button_distribution = Button( self._frame_two , text = "distribution" , command = self.show_distribution, width=100).pack()
        button_robustness = Button( self._frame_two , text = "robustness_connected_remaining", command = self.show_robustness_connected, width=100).pack()
        button_robustness_remaining = Button( self._frame_two , text = "robustness_total_remaining", command = self.show_robustness_remaining, width=100).pack()
        print("[{}] add_button()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        
        self._entry = tk.Entry(self._frame_two, font=60, relief='flat', width=100, bg="#33B5E5")
        self._entry.pack()
        self._entry.focus_set()
        self._buttonEntry = tk.Button(self._frame_two, text="Remove", width=100)
        self._buttonEntry.bind("<Button-1>", lambda evt: self.entryValueRemove())
        self._buttonEntry.pack()
        self._entry_1 = tk.Entry(self._frame_two, font=60, relief='flat', width=100, bg="grey")
        self._entry_1.pack()
        self._entry_1.focus_set()
        self._buttonEntry_1 = tk.Button(self._frame_two, text="Subgraph_causal_scenarios", width=100)
        self._buttonEntry_1.bind("<Button-1>", lambda evt: self.get_causal_consequence_subgraph())
        self._buttonEntry_1.pack()
        button_random = Button( self._frame_two , text = "Random_Robustness", command = self.start_random_robustness, width=100).pack()
        button_total_robustness_remaining = Button( self._frame_two , text = "Total_Robustness_Remaining", command = self.start_total_robustness_remaining, width=100).pack()
        button_total_robustness_connected = Button( self._frame_two , text = "Total_Robustness_Connected", command = self.start_total_robustness_connected, width=100).pack()
        self._chosen_metric_for_optimal = ('Degree','In Degree', 'Out Degree', 'In Closeness', 'Out Closeness', 'Betweenness', 'In Strength', 'Out Strength', 'Strength')
        button_robustness_for_all = Button(self._frame_two, text = "Robustness for all metrics", command = self.robustness_remaining_all, width = 100).pack()
        button_robustness_for_all_descending = Button(self._frame_two, text = "Robustness for all metrics descending", command = self.robustness_remaining_all_descending_order_metric, width = 100).pack()
        button_find_optimal = Button( self._frame_two , text = "Start Optimal", command = self.start_optimal, width=100).pack()
        button_toy_network = Button( self._frame_two , text = "Toy network", command = self.toy_network_abstraction, width=100).pack()
        self._largest_component = []
        self._deleted_node = []
        self._node_neighbor = self.neighbor_of_nodes()
        self._number_of_remaining_nodes = []
        self._largest_connected_component = []
        self._node_left = []
        self._total_node = []
        for j in range(0, len(self._digraph_normal)):
            self._total_node.append(j)
        self._d = {"Number of Removed Nodes":self._total_node}
        self._df = pd.DataFrame(data=self._d)
        
        
        #self.json()
        #data = json_graph.node_link_data(self._digraph_normal)
        #with open('graph.json', 'w') as outfile:
         #   outfile.write(str(data).replace("'", '"'))
        
        print("\n[{}] finished digraphPlot init()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        
        
        
    def json(self):
        with open('graph.json', 'r') as f:
            data = f.read()
        graph = json.loads(data)
        betweenness = nx.betweenness_centrality(self._digraph_normal, normalized=True,weight="weight")
        degree = dict(self._digraph_normal.degree)
        for i in range(len(self._digraph_normal)):
            graph["nodes"][i]["degree"] = degree[graph["nodes"][i]["id"]]
            graph["nodes"][i]["betweenness"] = betweenness[graph["nodes"][i]["id"]]
            graph["nodes"][i]["meaning"] = list(self._node_ID.keys())[list(self._node_ID.values()).index(int(graph["nodes"][i]["id"]))]
        
        with open('output.json', 'w') as f:
            json.dump(graph, f)
    def get_color(self,k):
		# Yifei's original colour list
        color_list = ['red','blue','green','yellow','black','purple','grey','orange','fuchsia','olive','cyan','brown']
		
        # 12 Qualitative Colours from Color Brewer
		# https://colorbrewer2.org/#type=qualitative&scheme=Paired&n=12
        # color_list=['#a6cee3','#1f78b4','#b2df8a','#33a02c','#fb9a99','#e31a1c','#fdbf6f','#ff7f00','#cab2d6','#6a3d9a','#ffff99','#b15928']
        
        # Use CSS Colors
        # color_list=list(mcolors.CSS4_COLORS.keys())
        
        if k>=len(color_list):
            k=len(color_list)-1
        return(color_list[k])
    
    def add_menu(self):
        """Add the menu function in the master widget."""
        menubar = tk.Menu(self._master)
        self._master.config(menu=menubar)
        filemenu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label='File', menu=filemenu)
        filemenu.add_command(label='Load Excel', command=self.re_excel)
        filemenu.add_command(label='Save Matrix', command=self.save_matrix)
        filemenu.add_command(label='Quit', command=self.quit)

        self._filename = None

    def load_excel(self):
        """Select the excel file under same direction with this file"""
        self._filename = filedialog.askopenfilename(filetypes=[("Excel or CSV files", ".xlsx .xls .csv")])
        # If file exists
        if self._filename:
            self._master.title(self._filename)
            self._excel_name = self._filename
            return self._filename
        
    
    def robustness_remaining_all_descending_order_metric(self):
        options = ["Strength", "In Strength", "Out Strength", "Degree", 
                   "Betweenness", "Out Degree", "In Degree", "In Closeness", "Out Closeness"]
        a = []
        metric = ''
        number_of_remaining_nodes = len(self._digraph_normal)
        for i in options:
            stored_matrix = self._adjacency_matrix.copy()
            stored_node_ID = copy.deepcopy(self._node_ID)
            stored_node_weight = copy.deepcopy(self._node_weight)
            stored_node_left = self._node_left
            if i == "Degree":
                a = self._digraph_normal.degree
                a = list(a)
                a.sort(key=lambda x: x[-1], reverse=True)
            if i == "Betweenness":
                b = nx.betweenness_centrality(self._digraph_normal, normalized=True,weight="weight")
                a = [(k, v) for k, v in b.items()]
                a.sort(key=lambda x: x[-1], reverse=True)
            if i == "In Degree":
                a = self._digraph_normal.in_degree
                a = list(a)
                a.sort(key=lambda x: x[-1], reverse=True)
            if i == "Out Degree":
                a = self._digraph_normal.out_degree
                a = list(a)
                a.sort(key=lambda x: x[-1], reverse=True)
            if i == "Strength":
                instrength = self.det_instrength()
                outstrength = self.det_outstrength()
                b = self.det_strength(instrength, outstrength)
                a = [(k, v) for k, v in b.items()]
                a.sort(key=lambda x: x[-1], reverse=True)
            if i == "In Strength":
                b = self.det_instrength()
                a = [(k, v) for k, v in b.items()]
                a.sort(key=lambda x: x[-1], reverse=True)
            if i == "Out Strength":
                b = self.det_outstrength()
                a = [(k, v) for k, v in b.items()]
                a.sort(key=lambda x: x[-1], reverse=True)
            if i == "In Closeness":
                b = nx.closeness_centrality(self._digraph_normal, distance="weight")
                a = [(k, v) for k, v in b.items()]
                a.sort(key=lambda x: x[-1], reverse=True)
            if i == "Out Closeness":
                b = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight")
                a = [(k, v) for k, v in b.items()]
                a.sort(key=lambda x: x[-1], reverse=True)
                
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            while len(self._digraph_normal) != 0:
                for node_metric in a:
                    name = node_metric[0]
                    
                    self._delete_node.append(int(name))
                    self._matrix.deleteNode(self._delete_node)
                    self._adjacency_matrix = self._matrix.adjacency_matrix()
                    self._node_neighbor = self.neighbor_of_nodes()
                    self._digraph_normal = self.get_Digraph()
                    if number_of_remaining_nodes == len(self._digraph_normal):
                        continue
                    else:
                        number_of_remaining_nodes = len(self._digraph_normal)
                        self._number_of_remaining_nodes.append(len(self._digraph_normal))
                        self._deleted_node.append(name)
                        self._delete_node = []
        
                
            fig1, sub1 = plt.subplots()
            a = []
            for k in range(len(self._deleted_node)+1):
                a.append(k)
            sub1.plot(a, self._number_of_remaining_nodes)
            y = np.array(self._number_of_remaining_nodes)
            area = int(simps(y, x=np.array(a)))
            sub1.text(20, 150, 'The area under curve is ' + str(area))
            sub1.set_title('Nodes elimination follows order of ' + i)
            sub1.set_xlabel('Number of Removed Nodes')
            sub1.set_ylabel('Number of Remaining Nodes')
            fig1.savefig('Robustness_' + i + '_Remaining_Nodes_Descending.png')
            
            workbook = xlsxwriter.Workbook('Robustness_' + i + '_Remaining_Nodes_Descending.xlsx')
            worksheet_robustness = workbook.add_worksheet('Robustness')
            worksheet_robustness.write("A1", "No. of Nodes")
            worksheet_robustness.write("B1", "Number of Remaining Nodes " + i)
            worksheet_robustness.write("C1", "Area Under Curve " + i)
            row,row2=2,1
            for c in self._deleted_node:
                worksheet_robustness.write(row,0, str(c))
                row+=1
            for d in self._number_of_remaining_nodes:
                worksheet_robustness.write(row2,1, str(d))
                row2+=1
            worksheet_robustness.write(1,2, str(area))
            workbook.close()
            arealist = [area]
            for c in range(len(self._total_node)-1):
                arealist.append(None)
            for e in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
                self._number_of_remaining_nodes.append(None)
            d = {"Number of Remaining Nodes " + i:self._number_of_remaining_nodes,"Area Under Curve " + i: arealist}
            df = pd.DataFrame(data=d)
            self._df = pd.concat([self._df, df], axis=1)
            
            self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_ID = self._matrix.get_node_ID()
            self._digraph_normal_nocolor = self.get_Digraph_Nocolor()
            self._digraph_normal = self.get_Digraph()
            self._number_of_remaining_nodes = []
            self._deleted_node = []
        
        
        self._df.to_excel("Robustness_Total_Descending_Order.xlsx")
        loc1 = ("Robustness_Total_Descending_Order.xlsx")
        excel_data = pd.read_excel(loc1)
        fig, axes= plt.subplots(figsize=(15,8))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Betweenness'], color='g',marker="X", markersize=4, markerfacecolor="red", markeredgecolor="black", linewidth=1.5, label='Betweenness: ' + str(int(excel_data['Area Under Curve Betweenness'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Degree'], color='k',linewidth=1.5,  marker="o", markersize=4, markerfacecolor="None", label='Degree:: '+ str(int(excel_data['Area Under Curve Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Strength'], color='m',  linewidth=1.5,  marker="D", markersize=4, markerfacecolor="None",label='Strength: '+ str(int(excel_data['Area Under Curve Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Degree'], color='y', linewidth=1.5, marker="s", markersize=4, markerfacecolor="blue", markeredgecolor="yellow", label='In Degree: '+ str(int(excel_data['Area Under Curve In Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Strength'], color='b',linewidth=1.5,  marker="P", markersize=4, markerfacecolor="None", label='In Strength: '+ str(int(excel_data['Area Under Curve In Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Closeness'], color='tab:pink',linewidth=1.5,  marker="1", markersize=4, markerfacecolor="None",label='In Closeness: '+ str(int(excel_data['Area Under Curve In Closeness'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Degree'], color='tab:purple', linewidth=1.5, marker=(5,2), markersize=4, markerfacecolor="None",label='Out Degree: '+ str(int(excel_data['Area Under Curve Out Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Strength'], color='c', linewidth=1.5,marker="2", markersize=4, markerfacecolor="None", label='Out Strength: '+ str(int(excel_data['Area Under Curve Out Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Closeness'], color='tab:olive',linewidth=1.5,  marker="v", markersize=4, markerfacecolor="None",label='Out Closeness: '+ str(int(excel_data['Area Under Curve Out Closeness'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Betweenness Degree'], linestyle="dashed",marker="^", markersize=4, markerfacecolor="None", linewidth=1.5, label='Betweenness + Degree: ' + str(int(excel_data['Area Under Curve Degree Betweenness'][0])))
        ##plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Total Combined'],   linestyle="dotted",marker="h", markersize=4, markerfacecolor="None",linewidth=1.5, label='Total Combined: ' + str(int(excel_data['Area Under Curve Total Combined'][0])))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Betweenness'], color='g', marker='.', markersize=10,label='Betweenness Area Under Curve: ' + str(excel_data['Area Under Curve Betweenness'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Degree'], color='tab:purple', marker = '1', markersize=10,label='Degree Area Under Curve: '+ str(excel_data['Area Under Curve Degree'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Strength'], color='m', marker = 'x', markersize=10,label='Strength Area Under Curve: '+ str(excel_data['Area Under Curve Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Degree'], color='y', marker = 4,markersize=10,label='In Degree Area Under Curve: '+ str(excel_data['Area Under Curve In Degree'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Strength'], color='b', marker = 6,markersize=10,label='In Strength Area Under Curve: '+ str(excel_data['Area Under Curve In Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Closeness'], color='tab:pink', marker = '|',markersize=10,label='In Closeness Area Under Curve: '+ str(excel_data['Area Under Curve In Closeness'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Out Degree'], color='k', marker = '2',markersize=10,label='Out Degree Area Under Curve: '+ str(excel_data['Area Under Curve Out Degree'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Out Strength'], color='c', marker = '+',markersize=10,label='Out Strength Area Under Curve: '+ str(excel_data['Area Under Curve Out Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Out Closeness'], color='tab:olive', marker = '*',markersize=10,label='Out Closeness Area Under Curve: '+ str(excel_data['Area Under Curve Out Closeness'][0]))
        plt.xlabel("Number of Removed Nodes",fontsize=16)
        plt.xticks(fontsize = 14)
        plt.yticks(fontsize = 14)
        plt.ylabel("Number of Remaining Nodes",fontsize=16)
        plt.legend(fontsize="medium", title = "Metric: Area Under Curve", title_fontsize = 'large')
        plt.savefig("Robustness_Total.png", dpi=1000,bbox_inches='tight')
        
                
        
    def robustness_remaining_all(self):
        metric_remove_method_dic = {"Betweenness": self.delete_by_Betweenness_remaining,
                                    "Degree": self.delete_by_degree_remaining,
                                    "In Degree": self.delete_by_In_degree_remaining,
                                    "Out Degree": self.delete_by_Out_degree_remaining,
                                    "Strength": self.delete_by_Strength_remaining,
                                    "In Strength": self.delete_by_In_Strength_remaining,
                                    "Out Strength": self.delete_by_Out_Strength_remaining,
                                    "In Closeness": self.delete_by_Closeness_remaining,
                                    "Out Closeness": self.delete_by_Out_Closeness_remaining,
                                    "Betweenness Degree": self.delete_by_Betweenness_Degree_remaining,
                                    "Total Combined": self.start_optimal}
        options = [ "Betweenness","Degree", "In Degree", "Out Degree", "Strength", "In Strength", "Out Strength", "In Closeness", "Out Closeness", "Total Combined"]
        for i in options:
            stored_matrix = self._adjacency_matrix.copy()
            stored_node_ID = copy.deepcopy(self._node_ID)
            stored_node_weight = copy.deepcopy(self._node_weight)
            stored_node_left = self._node_left
            if i in metric_remove_method_dic.keys():
                metric_remove_method_dic[i]()
            self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_ID = self._matrix.get_node_ID()
            self._digraph_normal_nocolor = self.get_Digraph_Nocolor()
            self._digraph_normal = self.get_Digraph()
            self._number_of_remaining_nodes = []
            self._deleted_node = []

        self._df.to_excel("Robustness_Total.xlsx")
        loc1 = ("Robustness_Total.xlsx")
        excel_data = pd.read_excel(loc1)
        fig, axes= plt.subplots(figsize=(15,8))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Betweenness'], color='g', linewidth=1.5, label='Betweenness: ' + str(int(excel_data['Area Under Curve Betweenness'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Degree'], color='k',linewidth=1.5,   label='Degree:: '+ str(int(excel_data['Area Under Curve Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Strength'], color='m',  linewidth=1.5,  label='Strength: '+ str(int(excel_data['Area Under Curve Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Degree'], color='y', linewidth=1.5, label='In Degree: '+ str(int(excel_data['Area Under Curve In Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Strength'], color='b',linewidth=1.5,   label='In Strength: '+ str(int(excel_data['Area Under Curve In Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Closeness'], color='tab:pink',linewidth=1.5,  label='In Closeness: '+ str(int(excel_data['Area Under Curve In Closeness'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Degree'], color='tab:purple', linewidth=1.5,label='Out Degree: '+ str(int(excel_data['Area Under Curve Out Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Strength'], color='c', linewidth=1.5, label='Out Strength: '+ str(int(excel_data['Area Under Curve Out Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Closeness'], color='tab:olive',linewidth=1.5, label='Out Closeness: '+ str(int(excel_data['Area Under Curve Out Closeness'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Betweenness Degree'], linestyle="dashed", linewidth=1.5, label='Betweenness + Degree: ' + str(int(excel_data['Area Under Curve Betweenness Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Total Combined'],   linestyle="dotted",linewidth=1.5, label='Total Combined: ' + str(int(excel_data['Area Under Curve Total Combined'][0])))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Riemaining Nodes Betweenness'], color='g', marker='.', markersize=10,label='Betweenness Area Under Curve: ' + str(excel_data['Area Under Curve Betweenness'][0]))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Degree'], color='tab:purple', marker = 'x', markersize=10,label='Degree Area Under Curve: '+ str(excel_data['Area Under Curve Degree'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Strength'], color='m', marker = 'x', markersize=10,label='Strength Area Under Curve: '+ str(excel_data['Area Under Curve Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Degree'], color='y', marker = 4,markersize=10,label='In Degree Area Under Curve: '+ str(excel_data['Area Under Curve In Degree'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Strength'], color='b', marker = 6,markersize=10,label='In Strength Area Under Curve: '+ str(excel_data['Area Under Curve In Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Closeness'], color='tab:pink', marker = '|',markersize=10,label='In Closeness Area Under Curve: '+ str(excel_data['Area Under Curve In Closeness'][0]))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Degree'], color='k', marker = '*',markersize=10,label='Out Degree Area Under Curve: '+ '17.0')
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Out Strength'], color='c', marker = '+',markersize=10,label='Out Strength Area Under Curve: '+ str(excel_data['Area Under Curve Out Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Out Closeness'], color='tab:olive', marker = '*',markersize=10,label='Out Closeness Area Under Curve: '+ str(excel_data['Area Under Curve Out Closeness'][0]))
        plt.xlabel("Number of Removed Nodes",fontsize=16)
        plt.xticks(fontsize = 14)
        plt.yticks(fontsize = 14)
        plt.ylabel("Number of Remaining Nodes",fontsize=16)
        plt.legend(fontsize="medium", title = "Metric: Area Under Curve", title_fontsize = 'large')
        plt.savefig("Robustness_Total.png", dpi=1000,bbox_inches='tight')
        
        
                
        
        
    def start_total_robustness_remaining(self):
        #loc1 = ("Total_Robustness_Remaining_1.xlsx")
        loc1 = ("Robustness_Trans_AMC.xlsx")
        excel_data = pd.read_excel(loc1)
        fig, axes= plt.subplots(figsize=(15,8))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Betweenness'], color='g',marker="X", markersize=4, markerfacecolor="red", markeredgecolor="black", linewidth=1.5, label='Betweenness: ' + str(int(excel_data['Area Under Curve Betweenness'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Degree'], color='k',linewidth=1.5,  marker="o", markersize=4, markerfacecolor="None", label='Degree:: '+ str(int(excel_data['Area Under Curve Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Strength'], color='m',  linewidth=1.5,  marker="D", markersize=4, markerfacecolor="None",label='Strength: '+ str(int(excel_data['Area Under Curve Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Degree'], color='y', linewidth=1.5, marker="s", markersize=4, markerfacecolor="blue", markeredgecolor="yellow", label='In Degree: '+ str(int(excel_data['Area Under Curve In Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Strength'], color='b',linewidth=1.5,  marker="P", markersize=4, markerfacecolor="None", label='In Strength: '+ str(int(excel_data['Area Under Curve In Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Closeness'], color='tab:pink',linewidth=1.5,  marker="1", markersize=4, markerfacecolor="None",label='In Closeness: '+ str(int(excel_data['Area Under Curve In Closeness'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Degree'], color='tab:purple', linewidth=1.5, marker=(5,2), markersize=4, markerfacecolor="None",label='Out Degree: '+ str(int(excel_data['Area Under Curve Out Degree'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Strength'], color='c', linewidth=1.5,marker="2", markersize=4, markerfacecolor="None", label='Out Strength: '+ str(int(excel_data['Area Under Curve Out Strength'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Closeness'], color='tab:olive',linewidth=1.5,  marker="v", markersize=4, markerfacecolor="None",label='Out Closeness: '+ str(int(excel_data['Area Under Curve Out Closeness'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Betweenness Degree'], linestyle="dashed",marker="^", markersize=4, markerfacecolor="None", linewidth=1.5, label='Betweenness + Degree: ' + str(int(excel_data['Area Under Curve Degree Betweenness'][0])))
        plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Total Combined'],   linestyle="dotted",marker="h", markersize=4, markerfacecolor="None",linewidth=1.5, label='Total Combined: ' + str(int(excel_data['Area Under Curve Total Combined'][0])))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Betweenness'], color='g', marker='.', markersize=10,label='Betweenness Area Under Curve: ' + str(excel_data['Area Under Curve Betweenness'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Degree'], color='tab:purple', marker = '1', markersize=10,label='Degree Area Under Curve: '+ str(excel_data['Area Under Curve Degree'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Strength'], color='m', marker = 'x', markersize=10,label='Strength Area Under Curve: '+ str(excel_data['Area Under Curve Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Degree'], color='y', marker = 4,markersize=10,label='In Degree Area Under Curve: '+ str(excel_data['Area Under Curve In Degree'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Strength'], color='b', marker = 6,markersize=10,label='In Strength Area Under Curve: '+ str(excel_data['Area Under Curve In Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes In Closeness'], color='tab:pink', marker = '|',markersize=10,label='In Closeness Area Under Curve: '+ str(excel_data['Area Under Curve In Closeness'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Out Degree'], color='k', marker = '2',markersize=10,label='Out Degree Area Under Curve: '+ str(excel_data['Area Under Curve Out Degree'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Out Strength'], color='c', marker = '+',markersize=10,label='Out Strength Area Under Curve: '+ str(excel_data['Area Under Curve Out Strength'][0]))
        #plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Nodes Out Closeness'], color='tab:olive', marker = '*',markersize=10,label='Out Closeness Area Under Curve: '+ str(excel_data['Area Under Curve Out Closeness'][0]))
        plt.xlabel("Number of Removed Nodes",fontsize=10)
        plt.xticks(fontsize = 8)
        plt.yticks(fontsize = 8)
        plt.ylabel("Number of Remaining Nodes",fontsize=10)
        plt.legend(fontsize="small", title = "Metric: Area Under Curve")
        plt.savefig("Robustness_Trans_AMC.png", dpi=1000,bbox_inches='tight')
        
    
        
    def start_total_robustness_connected(self):
        loc1 = ("Total_Robustness_Connected.xlsx")
        excel_data = pd.read_excel(loc1)
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component Betweenness'], color='g', marker='.', markersize=10,label='Betweenness Area Under Curve: ' + str(excel_data['Area Under Curve Betweenness'][0]))
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component Degree'], color='tab:purple', marker = '1', markersize=10,label='Degree Area Under Curve: '+ str(excel_data['Area Under Curve Degree'][0]))
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component Strength'], color='m', marker = 'x', markersize=10,label='Strength Area Under Curve: '+ str(excel_data['Area Under Curve Strength'][0]))
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component In Degree'], color='y', marker = 4,markersize=10,label='In Degree Area Under Curve: '+ str(excel_data['Area Under Curve In Degree'][0]))
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component In Strength'], color='b', marker = 6,markersize=10,label='In Strength Area Under Curve: '+ str(excel_data['Area Under Curve In Strength'][0]))
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component In Closeness'], color='tab:pink', marker = '|',markersize=10,label='In Closeness Area Under Curve: '+ str(excel_data['Area Under Curve In Closeness'][0]))
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component Out Degree'], color='k', marker = '2',markersize=10,label='Out Degree Area Under Curve: '+ str(excel_data['Area Under Curve Out Degree'][0]))
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component Out Strength'], color='c', marker = '+',markersize=10,label='Out Strength Area Under Curve: '+ str(excel_data['Area Under Curve Out Strength'][0]))
        plt.plot(excel_data['Number of removed Nodes'], excel_data['Number of Remaining Largest Component Out Closeness'], color='tab:olive', marker = '*',markersize=10,label='Out Closeness Area Under Curve: '+ str(excel_data['Area Under Curve Out Closeness'][0]))
        plt.title("Robustness Analysis",fontsize=22)
        plt.xlabel("Number of Removed Nodes",fontsize=18)
        plt.xticks(fontsize = 15)
        plt.yticks(fontsize = 15)
        plt.ylabel("Size of Largest Connected Component",fontsize=18)
        plt.legend(fontsize=22)
        plt.savefig("total_robustness_Connected.png", dpi=500, pad_inches=0)
        
    
        
    def start_optimal(self):
        c=0
        count = -1
        name = ''
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        
        while len(self._digraph_normal_nocolor) != 0:
            self._number_of_remaining_nodes.append(len(self._digraph_normal_nocolor))
            chosen_metric_actions = {'Degree':self._digraph_normal_nocolor.degree,
                                           'In Degree': self._digraph_normal_nocolor.out_degree,
                                           'Out Degree': self._digraph_normal_nocolor.in_degree,
                                           'In Closeness':nx.closeness_centrality(self._digraph_normal_nocolor,distance="weight"),
                                           'Out Closeness': nx.closeness_centrality(self._digraph_normal_nocolor.reverse(),distance="weight"),
                                           'Betweenness': nx.betweenness_centrality(self._digraph_normal_nocolor,normalized=True,weight="weight"),
                                           'In Strength':self.det_instrength(),
                                           'Out Strength': self.det_outstrength(),
                                           'Strength': self.det_strength_1()}
            name_node = []
            for i in self._chosen_metric_for_optimal:
                a = chosen_metric_actions.get(i)
                c+=1
                if c < 4:
                        
                    for j in a:
                        if j[1] > count:
                            count = j[1]
                            name = j[0]
                elif c >=4:
                    for k in a:
                        if a[k] > count:
                            count = a[k]
                            name = k
                name_node.append(name)
                name = ''
                count=-1
          
            '''
            CopyOfMatrix = type('CopyOfMatrix', self._matrix.__bases__, dict(self._matrix.__dict__))
            stored_matrix = copy.deepcopy(self._matrix._adjacency_matrix)
            stored_node_weight = copy.deepcopy(self._matrix._node_weight)
            stored_node_ID = copy.deepcopy(self._matrix._node_ID)
            stored_gather_list = copy.deepcopy(self._matrix._gather_list)
            '''
         
            Number_of_Remaining_Nodes_Each = {}
            self._matrix = None
            for chosen_node in name_node:
            
                self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
                for i in self._deleted_node:
                    self._matrix.deleteNode([int(i)])
                self._adjacency_matrix = self._matrix.adjacency_matrix()
                self._node_ID = self._matrix.get_node_ID()
                self._digraph_normal_nocolor = self.get_Digraph_Nocolor()
                self._digraph_normal = self.get_Digraph()
                self._matrix.deleteNode([int(chosen_node)])
                self._adjacency_matrix = self._matrix.adjacency_matrix()
                self._node_ID = self._matrix.get_node_ID()
                self._digraph_normal_nocolor = self.get_Digraph_Nocolor()
                self._digraph_normal = self.get_Digraph()
                Number_of_Remaining_Nodes_Each[int(chosen_node)] = len(self._digraph_normal_nocolor)
                
                '''
                self._matrix.update_matrix(stored_matrix)
                self._matrix.update_node_weight(stored_node_weight)
                self._matrix.update_node_ID(stored_node_ID)
                self._matrix.update_gather_list(stored_gather_list)
                '''
            self._matrix = None
            maxgradient = 1000000000
            Node_need = 0
            
            for node_ID in Number_of_Remaining_Nodes_Each.keys():
                if Number_of_Remaining_Nodes_Each.get(node_ID) <= maxgradient:
                    maxgradient = Number_of_Remaining_Nodes_Each.get(node_ID)
                    Node_need = node_ID
            #if Node_need == 67:
             #   print(Number_of_Remaining_Nodes_Each)
             #   print(name_node)
             #   aa = self.det_instrength()
             #   print(aa)
             #   break
            
            
            self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
            for i in self._deleted_node:
                self._matrix.deleteNode([int(i)])
            self._matrix.deleteNode([Node_need])
            self._deleted_node.append(str(Node_need))
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_ID = self._matrix.get_node_ID()
            self._digraph_normal_nocolor = self.get_Digraph_Nocolor()
            self._digraph_normal = self.get_Digraph()
           
            
            
            c=0
            maxgradient = None
            Number_of_Remaining_Nodes_Each = None
            
            if len(self._digraph_normal_nocolor) == 0:
                    break
                
            
        self._number_of_remaining_nodes.append(0)
        number_of_remaining_nodes = []
        for i in self._number_of_remaining_nodes:
            number_of_remaining_nodes.append(i)
        
        node_total = pd.Series(self._total_node, name='first_column')
        remaining_total = pd.Series(self._number_of_remaining_nodes,name='second_column')
        if len(self._number_of_remaining_nodes) < len(self._total_node):
            for i in range(len(self._total_node)-len(self._number_of_remaining_nodes)):
                self._number_of_remaining_nodes.append(0)
        randomarray = {'first_column':self._total_node,
                       'second_column':self._number_of_remaining_nodes}
        df = pd.DataFrame(randomarray)
        df1 = pd.concat([node_total, remaining_total], axis=1)
        
        
            
        ### Store line to figure
       
        y=  df['second_column']
        x1 = df['first_column']
        y_1 = df1['second_column']
        x1_1 = df1['first_column']
        area = int(simps(y, x=np.array(x1)))
        workbook = xlsxwriter.Workbook('Robustness_Total_Combined_Metrics'+ str(area) +'.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Removed Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes")
        row,row2=2,1
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        workbook.close()
        plt.plot(x1_1, y_1, color = 'r', label = "Combined Metrics, Area Under Curve: " + str(area))
        plt.title("Robustness_Total_Combined_Metrics")
        plt.xlabel("Number of Removed Nodes")
        plt.ylabel("Number of Remaining Nodes")
        plt.legend()
        plt.show()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(number_of_remaining_nodes)):
            number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Total Combined":number_of_remaining_nodes,"Area Under Curve Total Combined": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def get_Digraph_Nocolor_1(self, matrix):
        """ Return the directed graph structure from the adjacency matrix"""
        G = nx.DiGraph(directed=True)
        
        print("[{}] started get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        for i in range(len(matrix)):
            for j in range(len(matrix)):
                weight=int(matrix[i][j])
                if weight>0:
                    
                    G.add_edge(str(i), str(j),weight=weight)
        
        print("[{}] finished get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        return G
    
    
    
    
    def toy_network_Barabasi_Albert_model(self):
        
        degree_centrality = self._digraph_normal.degree()
        in_degree_centrality = nx.in_degree_centrality(self._digraph_normal)
        out_degree_centrality = nx.out_degree_centrality(self._digraph_normal)
        betweenness_centrality = nx.betweenness_centrality(self._digraph_normal, normalized=True, weight="weight")
        in_closeness_centrality = nx.closeness_centrality(self._digraph_normal, distance = "weight")
        out_closeness_centrality = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight")
        orig_graph = self._digraph_normal
        
        selected_nodes = random.sample(orig_graph.nodes(), 30)

        # Construct a new graph with the same degree sequence as the selected nodes
        degrees = [d for n, d in orig_graph.degree(selected_nodes)]
        toy_graph = nx.configuration_model(degrees)

        # Remove parallel edges and self-loops
        toy_graph = nx.Graph(toy_graph)
        node_mapping = {i: selected_nodes[i] for i in range(30)}
        print(toy_graph.nodes)
        print(selected_nodes)
        # Copy the node attributes and edge weights from the original graph
        for u, v in toy_graph.edges():
            if orig_graph.has_edge(node_mapping[u], node_mapping[v]):
                toy_graph[u][v]['weight'] = orig_graph[node_mapping[u]][node_mapping[v]]['weight']

        #    Plot the degree distributions


        orig_degrees = [d for n, d in orig_graph.degree()]
        toy_degrees = [d for n, d in toy_graph.degree()]

        fig, ax = plt.subplots()
        ax.hist(orig_degrees, bins=range(max(orig_degrees)+2), alpha=0.5, label='Original')
        ax.hist(toy_degrees, bins=range(max(toy_degrees)+2), alpha=0.5, label='Toy')
        ax.set_xlabel('Degree')
        ax.set_ylabel('Frequency')
        ax.legend()
        plt.show()
        self._digraph_normal = toy_graph





               
    
    def toy_network_abstraction(self):
        
        degree_centrality = nx.degree_centrality(self._digraph_normal)
        in_degree_centrality = nx.in_degree_centrality(self._digraph_normal)
        out_degree_centrality = nx.out_degree_centrality(self._digraph_normal)
        betweenness_centrality = nx.betweenness_centrality(self._digraph_normal, normalized=True, weight="weight")
        in_closeness_centrality = nx.closeness_centrality(self._digraph_normal, distance = "weight")
        out_closeness_centrality = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight")
        
        ###Choose the top 30 nodes with high betweenness
        
        sorted_nodes = sorted(degree_centrality, 
                              key=degree_centrality.get, reverse=True)
        nodes = sorted_nodes[:30]
        top_nodes = [node for node in nodes]
       
        
        ###Create toy digraph with 30 nodes
    
        '''new_digraph = nx.DiGraph()'''
        
        ### Create toy subgraph
        
        new_digraph = self._digraph_normal.subgraph(top_nodes)
        
        ### Record NodeID
        
        node_mapping = {i: node for i, node in enumerate(new_digraph.nodes)}
        
        New_digraph = nx.relabel_nodes(new_digraph, node_mapping)
        
              
        '''
        for node in nodes:
            new_digraph.add_node(node, 
                                 degree_centrality = degree_centrality[node],
                                 in_degree_centrality=in_degree_centrality[node], 
                                 out_degree_centrality=out_degree_centrality[node], 
                                 betweenness_centrality=betweenness_centrality[node])
                                 
        for u, v, data in self._digraph_normal.edges(data=True):
            if u in nodes and v in nodes:
                new_digraph.add_edge(u, v, weight=data['weight'])
        '''
        '''
        H_new = nx.DiGraph()
        for node, original_node in node_mapping.items():
            H_new.add_node(original_node)
        for u, v in new_digraph.edges:
            H_new.add_edge(node_mapping[u], node_mapping[v])
        '''
        
        ### Filter the nodes that present in origianl network but not in toy network
        
        orignal_nodes = set(self._digraph_normal.nodes())
        toy_nodes = set(New_digraph.nodes())
        common_nodes = orignal_nodes & toy_nodes
        
        ### Degree
        
        
        
        original_degree = self._digraph_normal.degree
        toy_degree = New_digraph.degree
        
        original_degree = {node: original_degree[node] for node in common_nodes}
        toy_degree = {node: toy_degree[node] for node in common_nodes}
        print(original_degree)
        print(toy_degree)
        degree_difference = {node: original_degree[node] - toy_degree[node] for node in original_degree}

        ### Plot degree difference
        '''
        plt.bar(degree_difference.keys(), degree_difference.values())
        plt.xlabel("Node ID")
        plt.ylabel("Difference in Degree Centrality")
        plt.show()
        '''
        
        aa= {node: self._digraph_normal.degree[node] for node in orignal_nodes}
        
        ### Plot degree distribution for original and toy network
        
        plt.hist(list(aa.values()), bins=20, color='blue', alpha=0.5)
        plt.xlabel("Degree")
        plt.ylabel("Frequency")
        plt.title("Degree Distribution of the Original Network")
        plt.show()
        
        plt.hist(list(toy_degree.values()), bins=20, color='orange', alpha=0.5)
        plt.xlabel("Degree")
        plt.ylabel("Frequency")
        plt.title("Degree Distribution of the Original Network")
        plt.show()
        
        plt.legend(["Original network - only nodes within toy network", "Toy network"])
        '''
        
        ### Betweenness
        
        original_betweenness = betweenness_centrality
        toy_betweenness = nx.betweenness_centrality(New_digraph, normalized=True, weight="weight")
        
        original_betweenness = {node: original_betweenness[node] for node in common_nodes}
        toy_betweenness = {node: toy_betweenness[node] for node in common_nodes}
        print(original_betweenness)
        print(toy_betweenness)
        betweenness_difference = {node: original_betweenness[node] - toy_betweenness[node] for node in original_betweenness}

        ### Plot degree difference
        
        plt.bar(betweenness_difference.keys(), betweenness_difference.values())
        plt.xlabel("Node ID")
        plt.ylabel("Difference in Betweenness Centrality")
        plt.show()
        
        
        aa= {node: betweenness_centrality[node] for node in orignal_nodes}
        
        ### Plot degree distribution for original and toy network
        
        plt.hist(list(aa.values()), bins=20, color='blue', alpha=0.5)
        plt.xlabel("Betweenness")
        plt.ylabel("Frequency")
        plt.title("Betweenness Distribution of the Original Network")
        
        plt.show()
        
        plt.hist(list(toy_betweenness.values()), bins=20, color='orange', alpha=0.5)
        plt.xlabel("Betweenness")
        plt.ylabel("Frequency")
        plt.title("Betweenness Distribution of the Original Network")
       
        plt.show()
        
        plt.legend(["Original network", "Toy network"])
        '''
        
    
        
        
    
    def start_random_robustness(self):
        """Monte Carlo simulation"""
        
        stored_matrix = self._adjacency_matrix.copy()
        stored_node_ID = copy.deepcopy(self._node_ID)
        stored_node_weight = copy.deepcopy(self._node_weight)
        stored_node_left = self._node_left
        for i in range(0, len(self._adjacency_matrix)):
            self._node_left.append(i)
        area = 30000
        a=0
        times = 0
        for i in range(4):
            ### keep run until the simulation time has reached
            
            while len(self.get_Digraph_Nocolor()) != 0:
                print(len(self._node_left))
                nodeID = int(np.random.choice(self._node_left, size=1))
                nodeID_list = [nodeID]
                self._node_left.remove(nodeID)
                self._number_of_remaining_nodes.append(len(self._digraph_normal_nocolor))
                self._matrix.deleteNode(nodeID_list)
                self._delete_node.append(nodeID)
                self._adjacency_matrix = self._matrix.adjacency_matrix()
                final_left_nodes = [k for i in self._node_left for j in self._node_left for k in (i,j) if self._adjacency_matrix[i][j] != 0]
                final_left_nodes = list(set(final_left_nodes))
                self._node_left = final_left_nodes
                final_left_nodes = None
                nodeID_list = None
                nodeID = None
                self._digraph_normal_nocolor = self.get_Digraph_Nocolor()
                if len(self._digraph_normal_nocolor) == 0:
                    break
                
            
            self._number_of_remaining_nodes.append(0)
            node_total = pd.Series(self._total_node, name='first_column')
            remaining_total = pd.Series(self._number_of_remaining_nodes,name='second_column')
            if len(self._number_of_remaining_nodes) < len(self._total_node):
                for i in range(len(self._total_node)-len(self._number_of_remaining_nodes)):
                    self._number_of_remaining_nodes.append(0)
            randomarray = {'first_column':self._total_node,
                                'second_column':self._number_of_remaining_nodes}
            df = pd.DataFrame(randomarray)
            df1 = pd.concat([node_total, remaining_total], axis=1)
            
            ### Store line to figure
            a += 1
            y=  df['second_column']
            x1 = df['first_column']
            y_1 = df1['second_column']
            x1_1 = df1['first_column']
            area1 = int(simps(y, x=np.array(x1)))
            if area > area1:
                area = area1
                workbook = xlsxwriter.Workbook('Robustness_Random_Remaining_Nodes'+ str(area) +'.xlsx')
                worksheet_robustness = workbook.add_worksheet('Robustness')
                worksheet_robustness.write("A1", "No. of Nodes")
                worksheet_robustness.write("B1", "Number of Remaining Nodes")
                row,row2=2,1
                for i in self._deleted_node:
                    worksheet_robustness.write(row,0, str(i))
                    row+=1
                for j in self._number_of_remaining_nodes:
                    worksheet_robustness.write(row2,1, str(j))
                    row2+=1
                workbook.close()
            self._delete_node = []
            if a == 1999:
                plt.plot(x1_1, y_1, color = 'r', label = "Monte Carlo Simulation, least area under curve: " + str(area), alpha=0.25)
            if a != 1999:
                plt.plot(x1_1, y_1, color = 'r', alpha=0.25)
            randomarray=None
            node_total = None
            remaining_total = None
            df=None
            df1=None
            y=None
            x1=None
            y_1=None
            x1_1=None
            area1=None
            self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_ID = self._matrix.get_node_ID()
            self._digraph_normal_nocolor = self.get_Digraph_Nocolor()
            print(len(self._digraph_normal))
            
            self._number_of_remaining_nodes = []
            for i in range(0, len(self._adjacency_matrix)):
                self._node_left.append(i)
            print("run for" + str(times) + "times")
            times += 1
            print(df1)
        plt.title("Monte Carlo Simulation Izok 2000 times")
        plt.xlabel("Number of Removed Nodes")
        plt.ylabel("Number of Remaining Nodes")
        plt.legend()
        plt.show()
            
            
    def re_excel(self):
        """Select another excel file under same direction with this file
           Create Matrix, Redraw the frame and canvas.
        """
        filename = filedialog.askopenfilename()
        self._frame_one.destroy()
        self._frame_two.destroy()
        self._matrix = Matrix(filename, self._node_ID, self._node_weight)
        self._adjacency_matrix = self._matrix.adjacency_matrix()
        self._digraph_normal = self.get_Digraph()
        self._pos = nx.nx_agraph.graphviz_layout(self._digraph_normal)
        self._frame_one = tk.Frame(self._master, bg='grey', width=3000, height=1800)
        self._frame_one.pack(side=tk.LEFT, expand=1, anchor=tk.W)
        self.plot_Digraph_initial()
        self._frame_two = tk.Frame(self._master, bg='grey')
        self._frame_two.pack()
        self.options = ["Degree", "In_Degree", "Out_Degree", "Strength", "In_Strength", "Out_Strength", "Eigenvector", 
                                 "In_Closeness", "Out_Closeness", "Betweenness", "Relative_Likelihood", "Causal_Contribution"]
        self._frame_two = tk.Frame(self._master, bg='grey')
        self._frame_two.pack()
        self.add_button()
        self.clicked = StringVar()
        self.clicked.set("Degree")
        drop = OptionMenu( self._frame_two , self.clicked , *self.options)
        drop.config(width=100)
        drop.pack()
        button_colormap = Button( self._frame_two , text = "colormap" , command = self.show_colormap, width=100).pack()
        button_distribution = Button( self._frame_two , text = "distribution" , command = self.show_distribution, width=100).pack()
        button_robustness = Button( self._frame_two , text = "robustness_connected_remaining", command = self.show_robustness_connected, width=100).pack()
        button_robustness_remaining = Button( self._frame_two , text = "robustness_total_remaining", command = self.show_robustness_remaining, width=100).pack()
        print("[{}] add_button()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        
        self._entry = tk.Entry(self._frame_two, font=60, relief='flat', width=100, bg="#33B5E5")
        self._entry.pack()
        self._entry.focus_set()
        self._buttonEntry = tk.Button(self._frame_two, text="Remove", width=100)
        self._buttonEntry.bind("<Button-1>", lambda evt: self.entryValueRemove())
        self._buttonEntry.pack()
        self._largest_component = []
        self._deleted_node = []
        self._node_neighbor = self.neighbor_of_nodes()
        self._number_of_remaining_nodes = []
        self._largest_connected_component = []
        
    def show_colormap(self):
        if self.clicked.get() == "Degree":
            self.plot_ColorMap(self.get_dict(self._digraph_normal.degree()), 'Degree')
        elif self.clicked.get() == "In_Degree":
            self.plot_ColorMap(self.get_dict(self._digraph_normal.in_degree()), 'In_Degree')
        elif self.clicked.get() == "Out_Degree":
            self.plot_ColorMap(self.get_dict(self._digraph_normal.out_degree()), 'Out_Degree')
        elif self.clicked.get() == "Strength":
            instrength_1 = self.det_instrength()
            outstrength_1 = self.det_outstrength()
            strength_1 = self.det_strength(instrength_1, outstrength_1)
            self.plot_ColorMap(strength_1, 'Strength')
        elif self.clicked.get() == "In_Strength":
            self.plot_ColorMap(self.det_instrength(), 'In_Strength')
        elif self.clicked.get() == "Out_Strength":
            self.plot_ColorMap(self.det_outstrength(), 'Out_Strength')
        elif self.clicked.get() == "Eigenvector":
            self.plot_ColorMap_eigen(nx.eigenvector_centrality(self._digraph_normal, max_iter=600), 'Eigenvector')
        elif self.clicked.get() == "In_Closeness":
            self.plot_ColorMap(nx.closeness_centrality(self._digraph_normal), 'In_Closeness')
        elif self.clicked.get() == "Out_Closeness":
            self.plot_ColorMap(nx.closeness_centrality(self._digraph_normal.reverse()), 'Out_Closeness')
        elif self.clicked.get() == "Betweenness":
            self.plot_ColorMap(nx.betweenness_centrality(self._digraph_normal),'Betweenness')
        elif self.clicked.get() == "Relative_Likelihood":
            self.plot_ColorMap(self.det_relative_likelihood(), 'Relative_Likelihood')
        elif self.clicked.get() == "Causal_Contribution":
            self.plot_ColorMap(self.det_causal_contribution(), 'Causal_Contribution')
            
    def show_distribution(self):
        if self.clicked.get() == "Degree":
            Indegree = self.det_indegree()
            Outdegree = self.det_outdegree()
            Degree = self.det_degree(Indegree, Outdegree)
            self.plot_distribution(Degree, 1, "Degree_Distribution")
        elif self.clicked.get() == "In_Degree":
            Indegree = self.det_indegree()
            self.plot_distribution(Indegree, 2,"In_Degree_Distribution")
        elif self.clicked.get() == "Out_Degree":
            Outdegree = self.det_outdegree()
            self.plot_distribution(Outdegree, 3,"Out_Degree_Distribution")
            
        elif self.clicked.get() == "Strength":
            strength_list = []
            instrength_1 = self.det_instrength()
            outstrength_1 = self.det_outstrength()
            strength_1 = self.det_strength(instrength_1, outstrength_1)
            for i in range(len(strength_1)):
                strength_list.append(strength_1.get(str(i)))
            self.plot_distribution(strength_list, 8, "Strength_Distribution")
            
        elif self.clicked.get() == "In_Strength":
            instrength_list = []
            instrength_1 = self.det_instrength()
            for i in range(len(instrength_1)):
                instrength_list.append(instrength_1.get(str(i)))
            self.plot_distribution(instrength_list, 9, "In_Strength_Distribution")
            
        elif self.clicked.get() == "Out_Strength":
            outstrength_list = []
            outstrength_1 = self.det_instrength()
            for i in range(len(outstrength_1)):
                outstrength_list.append(outstrength_1.get(str(i)))
            self.plot_distribution(outstrength_list, 10, "Out_Strength_Distribution")
            
        elif self.clicked.get() == "Eigenvector":
            Eigenvector_Centrality_values = []
            self.plot_distribution(self.det_eigenvector_one(Eigenvector_Centrality_values), 5, "Eigenvector_Distribution")
        elif self.clicked.get() == "In_Closeness":
            In_closeness_centrality_values = []
            self.plot_distribution(self.det_in_closeness_one(In_closeness_centrality_values), 4, "In_Closeness_Distribution")
        elif self.clicked.get() == "Out_Closeness":
            Out_closeness_centrality_values = []
            self.plot_distribution(self.det_out_closeness_one(Out_closeness_centrality_values), 7, "In_Closeness_Distribution")
        elif self.clicked.get() == "Betweenness":
            betweenness_values = []
            self.plot_distribution(self.det_betweenness_one(betweenness_values), 6, "Betweenness_Distribution")
            
        elif self.clicked.get() == "Relative_Likelihood":
            relative_likelihood_list = []
            relative_likelihood = self.det_relative_likelihood()
            for i in range(len(relative_likelihood)):
                relative_likelihood_list.append(relative_likelihood.get(str(i)))
            self.plot_distribution(relative_likelihood_list, 11, 'Relative_Likelihood')
            
        elif self.clicked.get() == "Causal_Contribution":
            Causal_Contribution_list = []
            Causal_Contribution = self.det_causal_contribution()
            for i in range(len(Causal_Contribution)):
                Causal_Contribution_list.append(Causal_Contribution.get(str(i)))
            self.plot_distribution(Causal_Contribution_list, 12, 'Causal_Contribution')
            
    def show_robustness_connected(self):
        if self.clicked.get() == "Degree":
            self.delete_by_degree_connected()
        elif self.clicked.get() == "In_Degree":
            self.delete_by_In_degree_connected()
        elif self.clicked.get() == "Out_Degree":
            self.delete_by_Out_degree_connected()
        elif self.clicked.get() == "Strength":
            self.delete_by_Strength_connected()
        elif self.clicked.get() == "In_Strength":
            self.delete_by_In_Strength_connected()
        elif self.clicked.get() == "Out_Strength":
            self.delete_by_Out_Strength_connected()
        elif self.clicked.get() == "Eigenvector":
            self.delete_by_Eigenvector_connected()
        elif self.clicked.get() == "In_Closeness":
            self.delete_by_Closeness_connected()
        elif self.clicked.get() == "Out_Closeness":
            self.delete_by_Out_Closeness_connected()
        elif self.clicked.get() == "Betweenness":
            self.delete_by_Betweenness_connected()
        elif self.clicked.get() == "Relative_Likelihood":
            self.delete_by_relative_likelihood_connected()
        elif self.clicked.get() == "Causal_Contribution":
            self.delete_by_causal_contribution_connected()
            
    def show_robustness_remaining(self):
        if self.clicked.get() == "Degree":
            self.delete_by_degree_remaining()
        elif self.clicked.get() == "In_Degree":
            self.delete_by_In_degree_remaining()
        elif self.clicked.get() == "Out_Degree":
            self.delete_by_Out_degree_remaining()
        elif self.clicked.get() == "Strength":
            self.delete_by_Strength_remaining()
        elif self.clicked.get() == "In_Strength":
            self.delete_by_In_Strength_remaining()
        elif self.clicked.get() == "Out_Strength":
            self.delete_by_Out_Strength_remaining()
        elif self.clicked.get() == "Eigenvector":
            self.delete_by_Eigenvector_remaining()
        elif self.clicked.get() == "In_Closeness":
            self.delete_by_Closeness_remaining()
        elif self.clicked.get() == "Out_Closeness":
            self.delete_by_Out_Closeness_remaining()
        elif self.clicked.get() == "Betweenness":
            self.delete_by_Betweenness_remaining()
        elif self.clicked.get() == "Relative_Likelihood":
            self.delete_by_relative_likelihood_remaining()
        elif self.clicked.get() == "Causal_Contribution":
            self.delete_by_causal_contribution_remaining() 
            
    def save_matrix(self):
        if self._filename is None:
            filename = filedialog.asksaveasfilename(filetypes=[("Text file", ".txt")])
            if filename:
                self._filename = filename
        if self._filename:
            self._master.title(self._filename)
            np.savetxt(self._filename, self._adjacency_matrix, fmt="%d", delimiter=",")

        a = self._matrix.get_node_ID()
        res = dict((v,k) for k,v in a.items())
        df_IDs = pd.DataFrame.from_dict(res,orient='index',columns=['Description'])
        df_IDs.to_csv(filename + "_lookup.csv")
    
    def quit(self):
        """Execute the program"""
        self._master.destroy()

    def get_dict(self, list1):
        output = dict([(i[0], i[1]) for i in list1])
        return output

    def get_Digraph(self):
        """ Return the directed graph structure from the adjacency matrix"""
        G = nx.DiGraph(directed=True)
        self._adjacency_matrix = self._matrix.adjacency_matrix()
        print("[{}] started get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        for i in range(len(self._adjacency_matrix)):
            for j in range(len(self._adjacency_matrix)):
                weight=int(self._adjacency_matrix[i,j])
                if weight>0:
                    color = self.get_color(weight-1)
                    G.add_edge(str(i), str(j), color=color,weight=weight)
        
        print("[{}] finished get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        return G
    
    def get_Digraph_Nocolor(self):
        """ Return the directed graph structure from the adjacency matrix"""
        G = nx.DiGraph(directed=True)
        
        print("[{}] started get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        self._adjacency_matrix = self._matrix.adjacency_matrix()
        for i in range(len(self._adjacency_matrix)):
            for j in range(len(self._adjacency_matrix)):
                weight=int(self._adjacency_matrix[i][j])
                if weight>0:
                    
                    G.add_edge(str(i), str(j),weight=weight)
        
        print("[{}] finished get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        return G

    def plot_Digraph_initial(self):
        """ Plot the directed graph structure on the canvas"""
        fig = plt.figure(figsize=(6, 6), dpi=200)

        plt.axis('off')
        plt.subplots_adjust(top=1, bottom=0, right=1, left=0,
                            hspace=0, wspace=0)
        pos = nx.nx_agraph.graphviz_layout(self._digraph_normal)
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {'font_size': 3, 'font_color': 'white', 'node_color': 'black', 'node_size': 50,
                   'style': 'solid',
                   'width': 0.3
                   }
        nx.draw_networkx(self._digraph_normal, pos, edge_color=colors, arrows=True, arrowsize=2.5,
                         **options)
        plt.margins(0, 0)
        plt.savefig("initial_Digraph.png", dpi=500, pad_inches=0)
        print("[{}] Created: initial_Digraph.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        for widget in self._frame_one.winfo_children():
            widget.destroy()
        canvas = FigureCanvasTkAgg(fig, master=self._frame_one)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.LEFT, fill=None, expand=tk.YES)

    def plot_ColorMap(self, measures, measure_name):
        """ Plot the colormap structure (Degree, In-degree, Out-degree, Betweenness, Closeness) on the canvas"""
        fig = plt.figure(figsize=(6, 6), dpi=200)
        plt.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {'font_size': 3, 'font_color': 'black', 'node_color': 'gray', 'node_size': 50, 'style': 'solid',
                   'width': 0.3}
        nx.draw_networkx(self._digraph_normal, self._pos, edge_color=colors, arrows=True, arrowsize=2, **options)

        cmap = plt.get_cmap('coolwarm', 9)
        cmap.set_under('gray')
        
        for i,j in list(measures.items()):
            if j == 0:
                del measures[i]
        raw = list(measures.values())
        nodes = nx.draw_networkx_nodes(self._digraph_normal, self._pos, node_size=50, cmap=cmap,
                                       node_color=raw,
                                       nodelist=measures.keys())
        min = 10000
        max1 = 0

        if len(raw) == 0:
            max1 = 0
        elif len(raw) != 0:
            max1= max(raw)
        for i in measures.values():
            if i < min and i != 0:
                min = i
        nodes.set_norm(mcolors.SymLogNorm(linthresh=1, linscale=0.05, vmin=min, vmax=max1))
        plt.margins(0, 0)
        plt.title(measure_name)
        total = max1-min
        pad = []
        for i in range(10):
            pad.append(min)
            min = min + total/10
        cbar = plt.colorbar(nodes, shrink=0.2)
        cbar.ax.tick_params(labelsize=3)
        plt.axis('off')
        plt.savefig(measure_name + ".png", dpi=1000, pad_inches=0)
        print("[{}] Created: {}".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S"),measure_name + ".png"))
        for widget in self._frame_one.winfo_children():
            widget.destroy()
        canvas = FigureCanvasTkAgg(fig, master=self._frame_one)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.LEFT, fill=None, expand=tk.YES)
        
    def plot_colormap_total(self):
       
        img1 = Image.open("In_Degree.png")
        img2 = Image.open("Out_Degree.png")
        #img3 = Image.open("In_Strength.png")
        #img4 = Image.open("Out_Strength.png")
        #img5 = Image.open("Strength.png")
        #img6 = Image.open("Betweenness.png")
        #img7 = Image.open("In_Closeness.png")
        #img8 = Image.open("Out_Closeness.png")
        fig, (ax_1, ax_2) = plt.subplots(nrows=1, ncols=2,
                           figsize=(16,9))
    
        ax_1.set_title('In Degree Colormap')
        ax_1.imshow(img1)
        ax_1.axis('off')

        ax_2.set_title('Out Degree Colormap')
        ax_2.imshow(img2)
        ax_2.axis('off')
    
        #ax_4.set_title('In Strength Colormap')
        #ax_4.imshow(img3)
        #ax_4.axis('off')
        
        #ax_4.set_title('Out Strength Colormap')
        #ax_4.imshow(img3)
        #ax_4.axis('off')
        
        #ax_3.set_title('In Strength Colormap')
        #ax_3.imshow(img3)
        #ax_3.axis('off')
        
        #ax_4.set_title('Out Strength Colormap')
        #ax_4.imshow(img3)
        #ax_4.axis('off')
        
        #ax_3.set_title('In Strength Colormap')
        #ax_3.imshow(img3)
        #ax_3.axis('off')
        
        #ax_4.set_title('Out Strength Colormap')
        #ax_4.imshow(img3)
        #ax_4.axis('off')
    
        plt.savefig("Colormap_Total_1" + ".png", dpi=800, pad_inches=0)
        
        
        
    def plot_ColorMap_eigen(self, measures, measure_name):
        """ Plot the colormap structure (Eigenvector) on the canvas"""
        fig = plt.figure(figsize=(6, 6), dpi=200)
        plt.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {'font_size': 3, 'font_color': 'white', 'node_color': 'black', 'node_size': 50, 'style': 'solid',
                   'width': 0.3}
        nx.draw_networkx(self._digraph_normal, self._pos, edge_color=colors, arrows=True, arrowsize=2, **options)

        cmap = plt.get_cmap('coolwarm', 9)
        cmap.set_under('gray')
        nodes = nx.draw_networkx_nodes(self._digraph_normal, self._pos, node_size=50, cmap=cmap,
                                       node_color=list(measures.values()),
                                       nodelist=measures.keys())
        min = 1
        max = 0
        for i in measures.values():
            if i > max:
                max = i
            if i < min:
                min = i
        nodes.set_norm(mcolors.SymLogNorm(linthresh=1, linscale=1, vmin=0, vmax=0.001))
        plt.margins(0, 0)
        plt.title(measure_name)
        cbar = plt.colorbar(nodes, shrink=0.2)
        cbar.ax.tick_params(labelsize=5)
        plt.axis('off')
        plt.savefig(measure_name + ".png", dpi=800, pad_inches=0)
        print("[{}] Created: {}".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S"),measure_name + ".png"))
        for widget in self._frame_one.winfo_children():
            widget.destroy()
        canvas = FigureCanvasTkAgg(fig, master=self._frame_one)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.LEFT, fill=None, expand=tk.YES)

    def openImage(self, fileName):
        f = Image.open(fileName)
        f.show()

    def neighbor_of_nodes(self):
        """(Distionary): Returns node_ID as keys and pointing nodes as values in list structure"""
        nodes = {}
        for i in range(len(self._adjacency_matrix)):
            node_neighbor = []
            for neighbor, value in enumerate(self._adjacency_matrix[i]):
                if value != 0:
                    node_neighbor.append(neighbor)
            if len(node_neighbor) != 0:
                nodes[i] = node_neighbor
        return nodes

    def new(self, saved_list, component, index):
        """ Delete the node inside the node_no from adjacency matrix.

        Parameters:
            saved_list(List): Initial empty list, store pointed nodes need to be recursive to add to connected component.
            component(List): Initial empty list, store final connected nodes as a component.
            index(Int): Index of node in node_neighbor dictionary.
        """
        if len(self._node_neighbor) == 0:
            return
        else:
            saved_list.append(list(self._node_neighbor.keys())[index])
            saved_list.extend(self._node_neighbor[list(self._node_neighbor.keys())[index]])
            saved_list = list(dict.fromkeys(saved_list))
            del self._node_neighbor[list(self._node_neighbor.keys())[index]]
            if len(self._node_neighbor) == 0:
                saved_list = list(dict.fromkeys(saved_list))
                if saved_list not in component:
                    component.append(saved_list)
            else:
                for i in list(self._node_neighbor.keys()):
                    for j in self._node_neighbor[i]:
                        ## Both incident nodes and being pointed nodes are connected component
                        if i in saved_list:
                            saved_list = list(dict.fromkeys(saved_list))
                            self.new(saved_list, component, list(self._node_neighbor.keys()).index(i))
                            break

                        elif j in saved_list:
                            saved_list = list(dict.fromkeys(saved_list))
                            self.new(saved_list, component, list(self._node_neighbor.keys()).index(i))
                            break

                    saved_list = list(dict.fromkeys(saved_list))
                    if saved_list not in component:
                        saved_list = list(dict.fromkeys(saved_list))
                        component.append(saved_list)
                    if len(self._node_neighbor) < 1:
                        break

                saved_list = []
                self.new(saved_list, component, 0)
                
### Find removed nodes

    def find_removed_nodes(self, original_matrix, reduced_matrix):
        removed = []
        for i in range(original_matrix.shape[0]):
            if (np.sum(original_matrix[i]) != 0 or np.sum(original_matrix[:, i]) != 0) and (np.sum(reduced_matrix[i]) == 0 and np.sum(reduced_matrix[:, i]) == 0):
                removed.append(i)
        return removed

                
### Robustness of network focusing on number of remaining nodes   
    def delete_by_degree_remaining(self):
        """
        Delete all the nodes by the descending order of value of degree.
        """
        count = -1
        name = ''
        a = self._digraph_normal.degree
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        component = []
        
        while len(a) != 0:
            for i in a:
                if i[1] > count:
                    count = i[1]
                    name = i[0]
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            
            count = -1
            name = ''
            a = self._digraph_normal.degree
        fig1, sub1 = plt.subplots()
        a = []
       
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of degree')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_Degree_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        workbook = xlsxwriter.Workbook('Robustness_Degree_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Degree")
        worksheet_robustness.write("C1", "Area Under Curve Degree")
        row,row2=2,1
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        worksheet_robustness.write(1,2, str(area))
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Degree":self._number_of_remaining_nodes,"Area Under Curve Degree": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
       
        
    def delete_by_degree_remaining_new(self):
        """
        Delete all the nodes by the descending order of value of degree.
        """
        count = -1
        total_length = copy.deepcopy(len(self._digraph_normal))
        name = ''
        a = self._digraph_normal.degree
        component = []
        while len(a) != 0:
            for i in a:
                if i[1] > count:
                    count = i[1]
                    name = i[0]
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(round(self._digraph_normal.number_of_nodes()/total_length,3))
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = self._digraph_normal.degree
        fig1, sub1 = plt.subplots()
        a = [0]
        for i in range(1,len(self._deleted_node)+1):
            a.append(round(i/total_length,3))
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        print(a)
        print(self._number_of_remaining_nodes)
        print(total_length)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of degree')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_Degree_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        workbook = xlsxwriter.Workbook('Robustness_Degree_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Degree")
        worksheet_robustness.write("C1", "Area Under Curve Degree")
        row,row2=2,1
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        worksheet_robustness.write(1,2, str(area))
        workbook.close()
        
    def delete_by_Out_degree_remaining(self):
        """ Delete all the nodes by the descending order of value of Out Degree."""
        count = 0
        name = ''
        a = self._digraph_normal.out_degree
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        component = []
        print(a)
        while len(a) != 0:
            for i in a:
                if i[1] > count:
                    count = i[1]
                    name = i[0]
            print(name)
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = 0
            name = ''
            a = self._digraph_normal.out_degree
            print(len(a))
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Out_Degree')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_Out_Degree_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Out_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Out_Degree_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Out Degree")
        worksheet_robustness.write("C1", "Area Under Curve Out Degree")
        row,row2=2,1
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        worksheet_robustness.write(1,2, str(area))
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Out Degree":self._number_of_remaining_nodes,"Area Under Curve Out Degree": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def delete_by_In_degree_remaining(self):
        """ Delete all the nodes by the descending order of value of In Degree."""
        count = 0
        name = ''
        a = self._digraph_normal.in_degree
        component = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        while len(a) != 0:
            for i in a:
                if i[1] > count:
                    count = i[1]
                    name = i[0]
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = 0
            name = ''
            a = self._digraph_normal.in_degree
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        print(a)
        print(self._number_of_remaining_nodes)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of In_Degree')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_In_Degree_Remaining_Nodes.png')
        print("[{}] Created: Robustness_In_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_In_Degree_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes In Degree")
        worksheet_robustness.write("C1", "Area Under Curve In Degree")
        row,row2=2,1
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        worksheet_robustness.write(1,2, str(area))    
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes In Degree":self._number_of_remaining_nodes,"Area Under Curve In Degree": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
        
    def delete_by_Closeness_remaining(self):
        """ Delete all the nodes by the descending order of value of In_Closeness."""
        count = -1
        name = ''
        cc = 0
        aa = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        a = nx.closeness_centrality(self._digraph_normal, distance="weight")
        component = []
        while len(a) != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = nx.closeness_centrality(self._digraph_normal, distance="weight")
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of In_Closeness')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_In_Closeness_Remaining_Nodes.png')
        print("[{}] Created: Robustness_In_Closeness_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_In_Closeness_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes In Closeness")
        worksheet_robustness.write("C1", "Area Under Curve In Closeness")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes In Closeness":self._number_of_remaining_nodes,"Area Under Curve In Closeness": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def delete_by_Out_Closeness_remaining(self):
        """ Delete all the nodes by the descending order of value of Closeness."""
        count = -1
        name = ''
        cc = 0
        aa = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        a = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight")
        component = []
        while len(a) != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight")
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Out_Closeness')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_Out_Closeness_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Out_Closeness_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Out_Closeness_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of remaining nodes Out Closeness")
        worksheet_robustness.write("C1", "Area Under Curve Out Closeness")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Out Closeness":self._number_of_remaining_nodes,"Area Under Curve Out Closeness": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def delete_by_Eigenvector_remaining(self):
        """ Delete all the nodes by the descending order of value of Eigenvector."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = nx.eigenvector_centrality(self._digraph_normal, tol=1e-03)
        component = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = nx.eigenvector_centrality(self._digraph_normal, tol=1e-03)
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Eigenvector')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remainig Nodes')
        fig1.savefig('Robustness_Eigenvector_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Eigenvector_Remain.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Eigenvector_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Eigenvector")
        worksheet_robustness.write("C1", "Area Under Curve Eigenvector")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
        
    def delete_by_Betweenness_remaining(self):
        """ Delete all the nodes by the descending order of value of Betweenness."""
        count = -1
        name = ''
        a = nx.betweenness_centrality(self._digraph_normal, normalized=True,weight="weight")
        component = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        cc = 0
        aa = []
        while len(a) != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            cc = 0
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = nx.betweenness_centrality(self._digraph_normal, normalized=True,weight="weight")
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Betweenness')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_Betweenness_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Betweenness_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Betweenness_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Betweenness")
        worksheet_robustness.write("C1", "Area Under Curve Betweenness")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Betweenness":self._number_of_remaining_nodes,"Area Under Curve Betweenness": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def delete_by_Betweenness_Degree_remaining(self):
        """ Delete all the nodes by the descending order of value of Betweenness."""
        count_first_40 = 0
        count = -1
        name = ''
        a = nx.betweenness_centrality(self._digraph_normal, normalized=True,weight="weight")
        component = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        cc = 0
        aa = []
        while len(a) != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            cc = 0
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            count_first_40 += 1
            a = nx.betweenness_centrality(self._digraph_normal, normalized=True,weight="weight")
            if count_first_40 == 37:
                break
        b = self._digraph_normal.degree
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        component = []
        
        while len(b) != 0:
       
            for i in b:
                if i[1] > count:
                    count = i[1]
                    name = i[0]
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            
            count = -1
            name = ''
            b = self._digraph_normal.degree
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Betweenness + Degree')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_Betweenness_Degree_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Betweenness_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Betweenness_Degree_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Betweenness Degree")
        worksheet_robustness.write("C1", "Area Under Curve Betweenness Degree")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Betweenness Degree":self._number_of_remaining_nodes,"Area Under Curve Betweenness Degree": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def delete_by_Strength_remaining(self):
        """ Delete all the nodes by the descending order of value of Strength."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        instrength = self.det_instrength()
        outstrength = self.det_outstrength()
        a = self.det_strength_1()
        component = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                instrength = self.det_instrength()
                outstrength = self.det_outstrength()
                a = self.det_strength_1()
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Strength')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_Strength_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Strength_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Strength_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Strength")
        worksheet_robustness.write("C1", "Area Under Curve Strength")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Strength":self._number_of_remaining_nodes,"Area Under Curve Strength": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def delete_by_In_Strength_remaining(self):
        """ Delete all the nodes by the descending order of value of Instrength."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = self.det_instrength()
        component = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = self.det_instrength()
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of In_Strength')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Reamining Nodes')
        fig1.savefig('Robustness_In_Strength_Remaining_Nodes.png')
        print("[{}] Created: Robustness_In_Strength_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_In_Strength_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes In Strength")
        worksheet_robustness.write("C1", "Area Under Curve In Strength")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes In Strength":self._number_of_remaining_nodes,"Area Under Curve In Strength": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def delete_by_Out_Strength_remaining(self):
        """ Delete all the nodes by the descending order of value of OutStrength."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = self.det_outstrength()
        print(a)
        component = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            print(name)
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            removed_node = self.find_removed_nodes(original_matrix, self._adjacency_matrix)
            removed_nodes.append(str(removed_node))
            original_matrix = copy.deepcopy(self._adjacency_matrix)
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            print(len(self._digraph_normal))
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = self.det_outstrength()
            else:
                break
            
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Out_Strength')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_Out_Strength_Remaining_Nodes.png')
        print("[{}] Created: Robustness_Out_Strength_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Out_Strength_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Out Strength")
        worksheet_robustness.write("C1", "Area Under Curve Out Strength")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        for k in removed_nodes:
            worksheet_robustness.write(row,3, str(k))
            row+=1
        workbook.close()
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(self._number_of_remaining_nodes)):
            self._number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Out Strength":self._number_of_remaining_nodes,"Area Under Curve Out Strength": arealist}
        df = pd.DataFrame(data=d)
        self._df = pd.concat([self._df, df], axis=1)
        
    def delete_by_relative_likelihood_remaining(self):
        """ Delete all the nodes by the descending order of value of relative_likelihood."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = self.det_relative_likelihood()
        component = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = self.det_relative_likelihood()
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of relative_likelihood')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_relative_likelihood_Remaining_Nodes.png')
        print("[{}] Created: Robustness_relative_likelihood_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_relative_likelihood_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Relative Likelihood")
        worksheet_robustness.write("C1", "Area Under Curve Relative Likelihood")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
             
    def delete_by_causal_contribution_remaining(self):
        """ Delete all the nodes by the descending order of value of causal_contribution."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = self.det_causal_contribution()
        component = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = self.det_causal_contribution()
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._number_of_remaining_nodes.append(0)
        sub1.plot(a, self._number_of_remaining_nodes)
        y = np.array(self._number_of_remaining_nodes)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of causal_contribution')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        fig1.savefig('Robustness_causal_contribution_Remaining_Nodes.png')
        print("[{}] Created: Robustness_causal_contribution_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_causal_contribution_Remaining_Nodes.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Causal Contribution")
        worksheet_robustness.write("C1", "Area Under Curve Causal Contribution")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._number_of_remaining_nodes:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
     
### Robustness of network focusing on largest connected component
    def delete_by_degree_connected(self):
        """
        Delete all the nodes by the descending order of value of degree.
        """
        count = -1
        name = ''
        a = self._digraph_normal.degree
        component = []
        while len(a) != 0:
            for i in a:
                if i[1] > count:
                    count = i[1]
                    name = i[0]
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = self._digraph_normal.degree
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of degree')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_Degree.png')
        print("[{}] Created: Robustness_Degree.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        workbook = xlsxwriter.Workbook('Robustness_Degree_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Degree")
        worksheet_robustness.write("C1", "Area Under Curve Degree")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
                    
    def delete_by_In_degree_connected(self):
        """ Delete all the nodes by the descending order of value of In Degree."""
        count = -1
        name = ''
        a = self._digraph_normal.in_degree
        component = []
        while len(a) != 0:
            for i in a:
                if i[1] > count:
                    count = i[1]
                    name = i[0]
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = self._digraph_normal.in_degree
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of In_Degree')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_In_Degree.png')
        print("[{}] Created: Robustness_In_Degree.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))

        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_In_Degree_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component In Degree")
        worksheet_robustness.write("C1", "Area Under Curve In Degree")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()

    def delete_by_Out_degree_connected(self):
        """ Delete all the nodes by the descending order of value of Out Degree."""
        count = 0
        name = ''
        a = self._digraph_normal.out_degree
        component = []
        while len(a) != 0:
            for i in a:
                if i[1] > count:
                    count = i[1]
                    name = i[0]
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = 0
            name = ''
            a = self._digraph_normal.out_degree
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Out_Degree')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_Out_Degree.png')
        print("[{}] Created: Robustness_Out_Degree.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Out_Degree_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Out Degree")
        worksheet_robustness.write("C1", "Area Under Curve Out Degree")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()

    def delete_by_Closeness_connected(self):
        """ Delete all the nodes by the descending order of value of In_Closeness."""
        count = -1
        name = ''
        cc = 0
        aa = []
        a = nx.closeness_centrality(self._digraph_normal, distance="weight")
        component = []
        while len(a) != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            for i in component:
                if len(i) > cc:
                    cc = len(i)
                    aa.append(i)
                    if len(aa) != 1:
                        aa.pop(0)
            cc = 0
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = nx.closeness_centrality(self._digraph_normal, distance="weight")
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of In_Closeness')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_In_Closeness.png')
        print("[{}] Created: Robustness_In_Closeness.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_In_Closeness_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component In Closeness")
        worksheet_robustness.write("C1", "Area Under Curve In Closeness")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
        
    def delete_by_Out_Closeness_connected(self):
        """ Delete all the nodes by the descending order of value of Closeness."""
        count = -1
        name = ''
        cc = 0
        aa = []
        a = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight")
        component = []
        while len(a) != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            for i in component:
                if len(i) > cc:
                    cc = len(i)
                    aa.append(i)
                    if len(aa) != 1:
                        aa.pop(0)
            cc = 0
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight")
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Out_Closeness')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_Out_Closeness.png')
        print("[{}] Created: Robustness_Out_Closeness.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Out_Closeness_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Out Closeness")
        worksheet_robustness.write("C1", "Area Under Curve Out Closeness")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()

    def delete_by_Eigenvector_connected(self):
        """ Delete all the nodes by the descending order of value of Eigenvector."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = nx.eigenvector_centrality(self._digraph_normal, tol=1e-03)
        component = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = nx.eigenvector_centrality(self._digraph_normal, tol=1e-03)
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Eigenvector')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_Eigenvector.png')
        print("[{}] Created: Robustness_Eigenvector.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Eigenvector_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Eigenvector")
        worksheet_robustness.write("C1", "Area Under Curve Eigenvevctor")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
        
    def delete_by_Strength_connected(self):
        """ Delete all the nodes by the descending order of value of Strength."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        instrength = self.det_instrength()
        outstrength = self.det_outstrength()
        a = self.det_strength(instrength, outstrength)
        component = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                instrength = self.det_instrength()
                outstrength = self.det_outstrength()
                a = self.det_strength(instrength, outstrength)
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Strength')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_Strength.png')
        print("[{}] Created: Robustness_Strength.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Strength_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Strength")
        worksheet_robustness.write("C1", "Area Under Curve Strength")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
        
    def delete_by_In_Strength_connected(self):
        """ Delete all the nodes by the descending order of value of Instrength."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = self.det_instrength()
        component = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = self.det_instrength()
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of In_Strength')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_In_Strength.png')
        print("[{}] Created: Robustness_In_Strength.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_In_Strength_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component In Strength")
        worksheet_robustness.write("C1", "Area Under Curve In Strength")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
        
    def delete_by_Out_Strength_connected(self):
        """ Delete all the nodes by the descending order of value of OutStrength."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = self.det_outstrength()
        component = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = self.det_outstrength()
            else:
                break
            print(b)
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Out_Strength')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_Out_Strength.png')
        print("[{}] Created: Robustness_Out_Strength.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Out_Strength_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Out Strength")
        worksheet_robustness.write("C1", "Area Under Curve Out Strength")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
        
    def delete_by_relative_likelihood_connected(self):
        """ Delete all the nodes by the descending order of value of relative_likelihood."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = self.det_relative_likelihood()
        component = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = self.det_relative_likelihood()
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of relative_likelihood')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_relative_likelihood.png')
        print("[{}] Created: Robustness_relative_likelihood.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_relative_likelihood_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Relative Likelihood")
        worksheet_robustness.write("C1", "Area Under Curve Relative Likelihood")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()
         
    def delete_by_causal_contribution_connected(self):
        """ Delete all the nodes by the descending order of value of causal_contribution."""
        count = -1
        name = ''
        b = len(self._digraph_normal)
        a = self.det_causal_contribution()
        component = []
        while b != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            if len(self._digraph_normal) != 0:
                a = self.det_causal_contribution()
            else:
                break
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of causal_contribution')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_causal_contribution.png')
        print("[{}] Created: Robustness_causal_contribution.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_causal_contribution_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Causal Contribution")
        worksheet_robustness.write("C1", "Area Under Curve Causal Contribution")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()

    def delete_by_Betweenness_connected(self):
        """ Delete all the nodes by the descending order of value of Betweenness."""
        count = -1
        name = ''
        a = nx.betweenness_centrality(self._digraph_normal, normalized=True,weight="weight")
        component = []
        cc = 0
        aa = []
        while len(a) != 0:
            for i in a:
                if a[i] > count:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self.new([], component, 0)
            for i in component:
                if len(i) > cc:
                    cc = len(i)
                    aa.append(i)
                    if len(aa) != 1:
                        aa.pop(0)
            max_length = max([(len(x)) for x in component])
            self._largest_connected_component.append(max_length)
            component = []
            self._matrix.deleteNode(self._delete_node)
            self._delete_node = []
            cc = 0
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._node_neighbor = self.neighbor_of_nodes()
            self._digraph_normal = self.get_Digraph()
            count = -1
            name = ''
            a = nx.betweenness_centrality(self._digraph_normal, normalized=True,weight="weight")
        fig1, sub1 = plt.subplots()
        a = []
        for i in range(len(self._deleted_node)+1):
            a.append(i)
        self._largest_connected_component.append(0)
        sub1.plot(a, self._largest_connected_component)
        y = np.array(self._largest_connected_component)
        area = int(simps(y, x=np.array(a)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Betweenness')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Size of Remaining Largest Component')
        fig1.savefig('Robustness_Betweenness.png')
        print("[{}] Created: Robustness_Betweenness.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook = xlsxwriter.Workbook('Robustness_Betweenness_Connected.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Size of Remaining Largest Component Betweenness")
        worksheet_robustness.write("C1", "Area Under Curve Betweenness")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in self._deleted_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in self._largest_connected_component:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        workbook.close()

    def plot_distribution(self, parameter, figure_number, title):
        """
        Construct distribution plots for each input topology properties on nodes.
        Parameters:
        parameter(List): Showing topology metrics on nodes.
        figure_number(Int): Shows the number of figure.
        title(String): Shows the title of each plots.
        """

        plt.figure(figure_number)
        mean = (np.array(parameter).mean())
        sd = np.array(parameter).std()
        skewness = skew(parameter)

        kurtosis_value = pd.Series(parameter).kurtosis()

        fig, (ax1) = plt.subplots(figsize=(8, 6))
        ax1.hist(parameter, density=False, edgecolor='white')
        plt.axvline(mean, color='k', linestyle='dashed', linewidth=1)
        min_ylim, max_ylim = plt.ylim()
        plt.text(mean * 1.1, max_ylim * 0.9, 'Mean: {:.2f}'.format(mean))
        ax1.set_title(
            f'{title}: $\mu={mean:.2f}$, $\sigma={sd:.2f}$, \nskew={skewness:.2f}, Kurtosis={kurtosis_value:.2f} ')

        for rect in ax1.patches:
            height = rect.get_height()
            ax1.annotate(f'{int(height)}', xy=(rect.get_x() + rect.get_width() / 2, height),
                         xytext=(0, 3), textcoords='offset points', ha='center', va='bottom')

        fig.savefig(title)
        print("[{}] Created: {}".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S"),title))

    def det_indegree(self):
        output = []
        print("[{}] Started Calculating Indegree".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        for i in tqdm(self._digraph_normal.nodes(), position=0, leave=True):
            ind = self._digraph_normal.in_degree(i)
            if type(ind)==int:
                output.append(ind)
            else:
                # ??? Investigate the root cause of this!
                output.append(0)
                print("Warning [{}] setting in degree to zero!".format(i))
            # if i%10==0:
                # print("[{}] Calculating Indegree <{:,d} of {:,d}>".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S"),i,len(self._adjacency_matrix)))
        return output

    def det_outdegree(self):
        print("[{}] Started Calculating Outdegree".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        output = []
        for i in tqdm(self._digraph_normal.nodes(), position=0, leave=True):
            outd= self._digraph_normal.out_degree(i)
            if type(outd)==int:
                output.append(outd)
            else:
               # ??? Investigate the root cause of this!
               output.append(0)
               print("Warning [{}] setting out degree to zero!".format(i))
    
            # if i%10==0:
                # print("[{}] Calculating Outdegree <{:,d} of {:,d}>".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S"),i,len(self._adjacency_matrix)))
        return output

    def det_degree(self, indegree, outdegree):
        sum = [indegree, outdegree]
        output = []
        for x, y in zip(*sum):
            output.append(x + y)
        return output
    
    def det_instrength(self):
        output = {}
        for i in sorted(self._digraph_normal.nodes(), key=lambda x: int(x)):
            total_incoming_weight = 0
            for _, _, edge_data in self._digraph_normal.in_edges(i, data=True):
                weight = edge_data.get('weight', 1)
                total_incoming_weight += round(1 / weight, 2)

            output[i] = total_incoming_weight
            
        return output

    def det_outstrength(self):
        output = {}
        for i in sorted(self._digraph_normal.nodes(), key=lambda x: int(x)):
            total_outgoing_weight = 0
            for _, _, edge_data in self._digraph_normal.out_edges(i, data=True):
                weight = edge_data.get('weight', 1)
                total_outgoing_weight += round(1 / weight, 2)
            output[i] = total_outgoing_weight
        return output

    def det_strength(self, instrength, outstrength):
        output = OrderedDict()
        for i in self._digraph_normal.nodes():
            in_value = instrength.get(i, 0)
            out_value = outstrength.get(i, 0)
            output[i] = round(in_value + out_value, 2)
        return output
    
    def det_strength_1(self):
        output = {}
        instrength = self.det_instrength()
        outstrength = self.det_outstrength()
        for node in sorted(self._digraph_normal.nodes(), key=lambda x: int(x)):
            in_value = instrength.get(node, 0)
            out_value = outstrength.get(node, 0)
            output[node] = round(in_value + out_value, 2)
        return output

    
    def det_relative_likelihood(self):
        output = {}
        for i in range(len(self._adjacency_matrix)):
            total_incoming_weight = 0
            number_of_incoming_edges = 0
            for j in range(len(self._adjacency_matrix)):
                if self._adjacency_matrix[j][i] != 0:
                    total_incoming_weight += round(1/self._adjacency_matrix[j][i], 2)
                    number_of_incoming_edges += 1
            if total_incoming_weight != 0:
                output[str(i)] = total_incoming_weight * total_incoming_weight/number_of_incoming_edges
            elif total_incoming_weight == 0:
                output[str(i)] = 0
        return output

    def det_causal_contribution(self):
        output = {}
        for i in range(len(self._adjacency_matrix)):
            total_outcoming_weight = 0
            number_of_outcoming_edges = 0
            for j in range(len(self._adjacency_matrix)):
                if self._adjacency_matrix[i][j] != 0:
                    total_outcoming_weight += round(1/self._adjacency_matrix[i][j], 2)
                    number_of_outcoming_edges += 1
            if total_outcoming_weight != 0:
                output[str(i)] = total_outcoming_weight * total_outcoming_weight/number_of_outcoming_edges
            elif total_outcoming_weight == 0:
                output[str(i)] = 0
        return output
    
    def excel_Gather(self):

        """(XLSX file): Excel sheet contains node_ID and Info."""

        workbook = xlsxwriter.Workbook('NODEs.xlsx')
        worksheet_nodes = workbook.add_worksheet('nodes_ID')
        worksheet_matrix = workbook.add_worksheet('Adjacency_Matrix')
        worksheet_colormap = workbook.add_worksheet('Colormaps')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_distribution = workbook.add_worksheet('Distribution')
        row = 0
        col = 0
        
        degree_1 = self._digraph_normal.degree
        indegree_1 = self._digraph_normal.in_degree
        outdegree_1 = self._digraph_normal.out_degree
        instrength_1 = self.det_instrength()
        outstrength_1 = self.det_outstrength()
        strength_1 = self.det_strength(instrength_1, outstrength_1)
        Betweenness_1 = nx.betweenness_centrality(self._digraph_normal, normalized = True, weight = "weight")
        Eigenvector_1 = nx.eigenvector_centrality(self._digraph_normal, max_iter=6000)
        Closeness_In = nx.closeness_centrality(self._digraph_normal,distance="weight")
        Closeness_Out = nx.closeness_centrality(self._digraph_normal.reverse(),distance="weight")
        relative_likelihood = self.det_relative_likelihood()
        causal_contribution = self.det_causal_contribution()
        worksheet_nodes.write(row, col + 2, 'Degree')
        worksheet_nodes.write(row, col + 3, 'In Degree')
        worksheet_nodes.write(row, col + 4, 'Out Degree')
        worksheet_nodes.write(row, col + 5, 'Strength')
        worksheet_nodes.write(row, col + 6, 'In Strength')
        worksheet_nodes.write(row, col + 7, 'Out Strength')
        worksheet_nodes.write(row, col + 8, 'Betweenness_normalized')
        worksheet_nodes.write(row, col + 9, 'Eigenvector_normalized')
        worksheet_nodes.write(row, col + 10, 'In_Closeness_normalized')
        worksheet_nodes.write(row, col + 11, 'Out_Closeness_normalized')
        worksheet_nodes.write(row, col + 12, 'Relative Likelihood')
        worksheet_nodes.write(row, col + 13, 'Causal contribution')

        # Node information
        for i in self._node_ID.keys():
            worksheet_nodes.write(row + 1, col, i)
            worksheet_nodes.write(row + 1, col + 1, self._node_ID[i])
            # Degree
            
            worksheet_nodes.write(row + 1, col + 2, degree_1(str(self._node_ID[i])))
            
            # InDegree
            worksheet_nodes.write(row + 1, col + 3, indegree_1(str(self._node_ID[i])))
            
            # OutDegree
            worksheet_nodes.write(row + 1, col + 4, outdegree_1(str(self._node_ID[i])))
            # Strength
            worksheet_nodes.write(row + 1, col + 5, strength_1.get((str(self._node_ID[i]))))
            # In Strength
            worksheet_nodes.write(row + 1, col + 6, instrength_1.get((str(self._node_ID[i]))))
            # Out Strength
            worksheet_nodes.write(row + 1, col + 7, outstrength_1.get((str(self._node_ID[i]))))
            # Betweenness
            worksheet_nodes.write(row + 1, col + 8,
                                  Betweenness_1.get((str(self._node_ID[i]))))
            # Eigenvector
            worksheet_nodes.write(row + 1, col + 9, Eigenvector_1.get((str(self._node_ID[i]))))
            # In_Closeness
            worksheet_nodes.write(row + 1, col + 10,
                                  Closeness_In.get((str(self._node_ID[i]))))
            # Out_Closeness
            worksheet_nodes.write(row + 1, col + 11,
                                  Closeness_Out.get((str(self._node_ID[i]))))
            # Relative Likelihood
            worksheet_nodes.write(row + 1, col + 12,
                                  relative_likelihood.get((str(self._node_ID[i]))))
            # Causal Contribution
            worksheet_nodes.write(row + 1, col + 13,
                                  causal_contribution.get((str(self._node_ID[i]))))
            
            row += 1

        row1 = 0
        col1 = 1

        #Adjacency_Matrix
        for i in range(len(self._adjacency_matrix)):
            worksheet_matrix.write(row1, col1, i)
            col1 += 1
        row1 = 1
        col1 = 0
        for j in range(len(self._adjacency_matrix)):
            worksheet_matrix.write(row1, col1, j)
            for k in range(len(self._adjacency_matrix)):
                worksheet_matrix.write(row1, col1 + 1, self._adjacency_matrix[j][k])
                col1 += 1
            row1 += 1
            col1 = 0

        # Colormap
        # Initial
        worksheet_colormap.write('A1', 'Initial_Digraph:')
        self.plot_Digraph_initial()
        worksheet_colormap.insert_image('D1', 'initial_Digraph.png')

        # Degree
        worksheet_colormap.write('A30', 'Degree_Colormap:')
        self.plot_ColorMap(self.get_dict(degree_1), 'Degree')
        worksheet_colormap.insert_image('D30', 'Degree.png')

        # InDegree
        worksheet_colormap.write('A60', 'In_Degree_Colormap:')
        self.plot_ColorMap(self.get_dict(indegree_1), 'In_Degree')
        worksheet_colormap.insert_image('D60', 'In_Degree.png')

        # OutDegree
        worksheet_colormap.write('M1', 'Out_Degree_Colormap:')
        self.plot_ColorMap(self.get_dict(outdegree_1), 'Out_Degree')
        worksheet_colormap.insert_image('P1', 'Out_Degree.png')

        # Eigenvector
        worksheet_colormap.write('M30', 'Eigenvector_Colormap:')
        self.plot_ColorMap(Eigenvector_1, 'Eigenvector')
        worksheet_colormap.insert_image('P30', 'Eigenvector.png')

        # Betweenness
        worksheet_colormap.write('M60', 'Betweenness_Colormap:')
        self.plot_ColorMap(Betweenness_1, 'Betweenness')
        worksheet_colormap.insert_image('P60', 'Betweenness.png')

        # In_Closeness
        worksheet_colormap.write('Y1', 'In_Closeness_Colormap:')
        self.plot_ColorMap(Closeness_In, 'In_Closeness')
        worksheet_colormap.insert_image('AA1', 'In_Closeness.png')
        
        # Out_Closeness
        worksheet_colormap.write('Y30', 'Out_Closeness_Colormap:')
        self.plot_ColorMap(Closeness_Out, 'Out_Closeness')
        worksheet_colormap.insert_image('AA30', 'Out_Closeness.png')
        
        # Relative Likelihood
        worksheet_colormap.write('Y60', 'Relative Likelihood_Colormap:')
        self.plot_ColorMap(relative_likelihood, 'Relative_Likelihood')
        worksheet_colormap.insert_image('AA60', 'Relative_Likelihood.png')
        
        # Causal Contribution
        worksheet_colormap.write('AJ1', 'Causal Contribution_Colormap:')
        self.plot_ColorMap(causal_contribution, 'Causal_Contribution')
        worksheet_colormap.insert_image('AN1', 'Causal_Contribution.png')
        
        # Strength
        worksheet_colormap.write('AJ30', 'Strength_Colormap:')
        self.plot_ColorMap(strength_1, 'Strength')
        worksheet_colormap.insert_image('AN30', 'Strength.png')
        
        # In_strength
        worksheet_colormap.write('AJ60', 'In_Strength_Colormap:')
        self.plot_ColorMap(instrength_1, 'In_Strength')
        worksheet_colormap.insert_image('AN60', 'In_Strength.png')
        
        # Out_strength
        worksheet_colormap.write('AJ90', 'Out_Strength_Colormap:')
        self.plot_ColorMap(outstrength_1, 'Out_Strength')
        worksheet_colormap.insert_image('AN90', 'Out_Strength.png')

        '''
        # Robustness
        # Degree
        worksheet_robustness.write('A1', 'Degree_Robustness:')
        self.delete_by_degree_connected()
        worksheet_colormap.insert_image('D1', 'Robustness_Degree.png')

        # Indegree
        worksheet_robustness.write('A30', 'In_Degree_Robustness')
        self.delete_by_In_degree_connected()
        worksheet_colormap.insert_image('D30', 'Robustness_In_Degree.png')

        # Outdegree
        worksheet_robustness.write('A60', 'Out_Degree_Robustness')
        self.delete_by_Out_degree_connected()
        worksheet_colormap.insert_image('D60', 'Robustness_Out_Degree.png')

        # Eigenvector
        worksheet_robustness.write('M1', 'Eigenvector_Robustness')
        self.delete_by_Eigenvector_connected()
        worksheet_colormap.insert_image('P1', 'Robustness_Eigenvector.png')

        # Betweenness
        worksheet_robustness.write('M30', 'Betweenness_Robustness')
        self.delete_by_Betweenness_connected()
        worksheet_colormap.insert_image('P30', 'Robustness_Betweenness.png')

        # Closeness
        worksheet_robustness.write('M60', 'Closeness_Robustness')
        self.delete_by_Closeness_connected()
        worksheet_colormap.insert_image('P60', 'Robustness_Closeness.png')
        '''

        Indegree = self.det_indegree()
        Outdegree = self.det_outdegree()
        Degree = self.det_degree(Indegree, Outdegree)
        betweenness_values = []
        In_closeness_centrality_values = []
        Out_closeness_centrality_values = []
        Eigenvector_Centrality_values = []
        strength_list = []
        instrength_1 = self.det_instrength()
        outstrength_1 = self.det_outstrength()
        print("in:" + str(instrength_1))
        instrength_list = []
        outstrength_list = []
        strength_1 = self.det_strength(instrength_1, outstrength_1)
        print(strength_1)
        relative_likelihood_list = []
        relative_likelihood = self.det_relative_likelihood()
        Causal_Contribution_list = []
        Causal_Contribution = self.det_causal_contribution()

        # Distribution
        # Degree
        worksheet_distribution.write('A1', 'Degree_Distribution:')
        self.plot_distribution(Degree, 1, "Degree_Distribution")
        worksheet_distribution.insert_image('D1', 'Degree_Distribution.png')

        # Indegree
        worksheet_distribution.write('A30', 'In_Degree_Distribution')
        self.plot_distribution(Indegree, 2, "In_Degree_Distribution")
        worksheet_distribution.insert_image('D30', 'In_Degree_Distribution.png')

        # Outdegree
        worksheet_distribution.write('A60', 'Out_Degree_Distribution')
        self.plot_distribution(Outdegree, 3, "Out_Degree_Distribution")
        worksheet_distribution.insert_image('D60', 'Out_Degree_Distribution.png')

        # Eigenvector
        worksheet_distribution.write('P1', 'Eigenvector_Distribution')
        self.plot_distribution(self.det_eigenvector_one(Eigenvector_Centrality_values), 4, "Eigenvector_Distribution")
        worksheet_distribution.insert_image('S1', 'Eigenvector_Distribution.png')

        # Betweenness
        worksheet_distribution.write('P30', 'Betweenness_Distribution')
        self.plot_distribution(self.det_betweenness_one(betweenness_values), 5, "Betweenness_Distribution")
        worksheet_distribution.insert_image('S30', 'Betweenness_Distribution.png')

        # In_Closeness
        worksheet_distribution.write('P60', 'In_Closeness_Distribution')
        self.plot_distribution(self.det_in_closeness_one(In_closeness_centrality_values), 6, "In_Closeness_Distribution")
        worksheet_distribution.insert_image('S60', 'In_Closeness_Distribution.png')
        
        # Out_Closeness
        worksheet_distribution.write('P90', 'Out_Closeness_Distribution')
        self.plot_distribution(self.det_out_closeness_one(Out_closeness_centrality_values), 7, "Out_Closeness_Distribution")
        worksheet_distribution.insert_image('S90', 'Out_Closeness_Distribution.png')
        
        # Strength
        worksheet_distribution.write('AE1', 'Strength_Distribution')
        for i in strength_1.values():
            strength_list.append(i)
        self.plot_distribution(strength_list, 8, "Strength_Distribution")
        worksheet_distribution.insert_image('AH1', 'Strength_Distribution.png')
        # In Strength
        worksheet_distribution.write('AE30', 'In_Strength_Distribution')
        for i in instrength_1.values():
            instrength_list.append(i)
        self.plot_distribution(instrength_list, 9, "In_Strength_Distribution")
        worksheet_distribution.insert_image('AH30', 'In_Strength_Distribution.png')
        
        # Out Strength
        worksheet_distribution.write('AE60', 'Out_Strength_Distribution')
        for i in outstrength_1.values():
            outstrength_list.append(i)
        self.plot_distribution(outstrength_list, 10, "Out_Strength_Distribution")
        worksheet_distribution.insert_image('AH60', 'Out_Strength_Distribution.png')
        
        # Relative likelihood
        worksheet_distribution.write('AE90', 'Relative_Likelihood_Distribution')
        for i in range(len(relative_likelihood)):
            relative_likelihood_list.append(relative_likelihood.get(str(i)))
        self.plot_distribution(relative_likelihood_list, 11, 'Relative_Likelihood_Distribution')
        worksheet_distribution.insert_image('AH90', 'Relative_Likelihood_Distribution.png')
        # Causal Contribution
        worksheet_distribution.write('AE120', 'Caucal_Contribution_Distribution')
        for i in range(len(Causal_Contribution)):
            Causal_Contribution_list.append(Causal_Contribution.get(str(i)))
        self.plot_distribution(Causal_Contribution_list, 12, 'Causal_Contribution_Distribution')
        worksheet_distribution.insert_image('AH120', 'Causal_Contribution_Distribution.png')

        workbook.close()
        
    def add_button(self):
        """Add button on canvas and bind the clicks on a button to the left clicks."""

        buttonGatherExcel = tk.Button(self._frame_two, text="Results", width=100, activebackground="#33B5E5")
        buttonGatherExcel.bind("<Button-1>", lambda evt: self.excel_Gather())
        buttonGatherExcel.pack()


        buttonInitial = tk.Button(self._frame_two, text="Initial_Digraph", width=100, activebackground="#33B5E5")
        buttonInitial.bind("<Button-1>", lambda evt: self.plot_Digraph_initial())
        buttonInitial.pack()

    def det_betweenness_one(self, betweenness_values):
        betweenness_centrality = nx.betweenness_centrality(self._digraph_normal_nocolor, normalized=True, weight="weight")
        for value in betweenness_centrality.values():
            betweenness_values.append(value)
        return betweenness_values

    def det_eigenvector_one(self, Eigenvector_Centrality_values):
        eigenvector_centrality = nx.eigenvector_centrality(self._digraph_normal_nocolor, tol=1e-03, max_iter=600)
        for value in eigenvector_centrality.values():
            Eigenvector_Centrality_values.append(value)
        return Eigenvector_Centrality_values

    def det_in_closeness_one(self, in_closeness_centrality_values):
        in_closeness_centrality = nx.closeness_centrality(self._digraph_normal_nocolor)
        for value in in_closeness_centrality.values():
            in_closeness_centrality_values.append(value)
        return in_closeness_centrality_values
    
    def det_out_closeness_one(self, out_closeness_centrality_values):
        out_closeness_centrality = nx.closeness_centrality(self._digraph_normal_nocolor.reverse())
        for value in out_closeness_centrality.values():
            out_closeness_centrality_values.append(value)
        return out_closeness_centrality_values

    def entryValueRemove(self):
        """Get the type-in texts (nodes need to be eliminated) and store in a list."""
        aa = self._entry.get().split(',')
        for i in aa:
            self._delete_node.append(i)
        self._matrix.deleteNode(self._delete_node)
        self._adjacency_matrix = self._matrix.adjacency_matrix()
        self._digraph_normal = self.get_Digraph()
        
    def get_causal_consequence_subgraph(self):
        """Get the type-in texts (nodes need to be eliminated) and store in a list."""
        target_node = str(self._entry_1.get())
        subgraph_nodes = [target_node]
        # Find the nodes having edges pointing to the target node and their causal paths
    
        for node in self._digraph_normal.predecessors(target_node):
            subgraph_nodes.append(node)
            subgraph_nodes.extend(nx.ancestors(self._digraph_normal, node))
        

        # Find the nodes that the target node has edges pointing to and their consequences
        
        for node in self._digraph_normal.successors(target_node):
            subgraph_nodes.append(node)
            subgraph_nodes.extend(nx.descendants(self._digraph_normal, node))

        # Create a subgraph with only the relevant nodes and their connecting edges
        subgraph = self._digraph_normal.subgraph(subgraph_nodes)
        
        new_graph = subgraph.copy()
        
        adjacency_matrix = nx.adjacency_matrix(new_graph, nodelist = self._digraph_normal.nodes, weight='weight')
        adjacency_matrix_array = adjacency_matrix.toarray()
        self._adjacency_matrix = adjacency_matrix_array
        print(adjacency_matrix)
        print(self._adjacency_matrix)
        self._digraph_normal = new_graph
        self._digraph_normal_nocolor = new_graph
        subgraph_node_meanings = {meaning: nodeID for meaning, nodeID in self._node_ID.items() if str(nodeID) in self._digraph_normal.nodes}
        self._node_ID = subgraph_node_meanings
        print(self._node_ID)
        workbook = xlsxwriter.Workbook('AAA.xlsx')
        worksheet_nodes = workbook.add_worksheet('nodes_ID')
        worksheet_matrix = workbook.add_worksheet('Adjacency_Matrix')
        worksheet_colormap = workbook.add_worksheet('Colormaps')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_distribution = workbook.add_worksheet('Distribution')
        row1 = 0
        col1 = 1
        for i in range(len(self._adjacency_matrix)):
            worksheet_matrix.write(row1, col1, i)
            col1 += 1
        row1 = 1
        col1 = 0
        for j in range(len(self._adjacency_matrix)):
            worksheet_matrix.write(row1, col1, j)
            for k in range(len(self._adjacency_matrix)):
                worksheet_matrix.write(row1, col1 + 1, self._adjacency_matrix[j][k])
                col1 += 1
            row1 += 1
            col1 = 0
        workbook.close()

if __name__ == "__main__":
    ##plot initial digraph
    root = tk.Tk()
    root.geometry("1600x1600")
    digraphPlot(root)
    root.update()
    print("[{}] finished root update()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
    root.mainloop()
    print("[{}] finished root mainloop()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
