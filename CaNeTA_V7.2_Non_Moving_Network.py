# -*- coding: utf-8 -*-
"""
Created on Thu Sep 19 17:57:34 2024

@author: uqylin13
"""

# -*- coding: utf-8 -*-
"""
Created on Sun Sep 15 15:28:42 2024

@author: uqylin13
"""

# -*- coding: utf-8 -*-
"""
Created on Mon May 27 22:36:53 2024

@author: uqylin13
"""

from tkinter import *
from tkinter import filedialog
import networkx as nx
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
from PIL import Image
from pyvis.network import Network
import numpy as np
import math
import Granularity
from scipy.stats import wasserstein_distance
from collections import Counter
from node2vec import Node2Vec
from scipy.spatial.distance import jensenshannon
from scipy.cluster.hierarchy import linkage, dendrogram, fcluster
from scipy.spatial.distance import cdist
from astropy.stats import kuiper_two
from sklearn.cluster import SpectralClustering
from sklearn.metrics import pairwise_distances
from sklearn.datasets import make_blobs
from matplotlib.figure import Figure
from sklearn.preprocessing import StandardScaler
from scipy.integrate import simps
from scipy.stats import skew
from scipy.stats import spearmanr
import xlsxwriter
import re
from sklearn.metrics import pairwise_distances
from scipy.spatial.distance import pdist, squareform
import os
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
from scipy.stats import entropy
matplotlib.use('Agg')
from networkx.algorithms.community import girvan_newman
import matplotlib.pyplot as plt
import Granularity
from scipy.cluster.hierarchy import dendrogram
from Grouping_Recorder import GroupingRecorder
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from scipy.stats import ks_2samp
from scipy.stats import cramervonmises_2samp
from scipy.spatial.distance import pdist, squareform
from scipy import stats
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
            
            
        else:
            
            for j in range(len(self._adjacency_matrix)):
                ##The relations showing nodes point to the eliminated node should be removed.
                self._adjacency_matrix[j][int(node_no[0])] = 0
                
                #print(self._adjacency_matrix)
            for mid_lis in self._gather_list:
                mid_list = copy.deepcopy(mid_lis)
                
                if all(isinstance(item, int) for item in mid_list[0]):
                   
                   if int(node_no[0]) in mid_list[0]:
                        
                        nodes_in_and_gate = set(mid_list[0])  # Set of nodes in the AND gate
                        target_node = mid_list[1]  # The target node connected by the AND gate
                        
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
                        else:
                            for item in other_and_gates_pointing:
                                for i in nodes_in_and_gate:
                                     if i != target_node and i not in item[0]:
                                         self._adjacency_matrix[i][target_node] = 0
                            if node_no[0] in other_and_gates_pointing[0][0]:
                                for i in other_and_gates_pointing[0][0]:
                                    self._adjacency_matrix[i][target_node] = 0
                        node_no.append(mid_list[1])
                        gather_list_two.remove(mid_list)

                else:
                    
                    
                    if int(node_no[0]) in mid_list[0]:
                        
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
        self._frame_one = tk.Frame(self._master, bg='grey', width=900, height=1800)
        self._frame_one.pack(side=tk.LEFT, expand=False, anchor=tk.N)  # Pack without expanding
        self._frame_one.pack_propagate(False) 
        #self._frame_one.pack(side=tk.LEFT, expand=1, anchor=tk.W)
        self.plot_Digraph_initial_2()
        self._frame_two = tk.Frame(self._master, bg='grey')
        self._frame_two.pack()
        
        self.options = ["Degree", "In_Degree", "Out_Degree", "Strength", "In_Strength", "Out_Strength", "Eigenvector", 
                                 "In_Closeness", "Out_Closeness", "Betweenness", "Relative_Likelihood", "Causal_Contribution", "Node Weight"]
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
        button_community = Button( self._frame_two , text = "Community", command = self.community, width=100).pack()
        button_granularity = Button( self._frame_two , text = "Granularity", command = self.Granularity, width=100).pack()
        
        #button_random = Button( self._frame_two , text = "Random_Robustness", command = self.start_random_robustness, width=100).pack()
        
        #button_total_robustness_remaining = Button( self._frame_two , text = "Total_Robustness_Remaining", command = self.start_total_robustness_remaining, width=100).pack()
        #button_total_robustness_connected = Button( self._frame_two , text = "Total_Robustness_Connected", command = self.start_total_robustness_connected, width=100).pack()
        self._chosen_metric_for_optimal = ('Degree','In Degree', 'Out Degree', 'In Closeness', 'Out Closeness', 'Betweenness', 'In Strength', 'Out Strength', 'Strength')
        button_robustness_for_all = Button(self._frame_two, text = "Robustness for all metrics: recalculating the metric values", command = self.robustness_remaining_all, width = 100).pack()
        button_robustness_for_all_descending = Button(self._frame_two, text = "Robustness for all metrics: following the initial metric values", command = self.robustness_remaining_all_descending_order_metric, width = 100).pack()
        button_find_optimal = Button( self._frame_two , text = "Start Optimal", command = self.start_optimal, width=100).pack()
        button_toy_network = Button( self._frame_two , text = "Toy network", command = self.toy_network_abstraction, width=100).pack()
        button_interacitve_network = Button( self._frame_two , text = "interactive_network", command = self.interactive_network, width=100).pack()
        button_all_pathway = Button( self._frame_two , text = "all_causal_pathway", command = self.get_causal_consequence_subgraph, width=100).pack()
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
        #self.store_node_weight('Updated_Risk_likelihood_BSOC_Existing_Future_Control.xlsx', 'Node ID', 'Likelihood Exsiting Control Plus Future Control', 'likelihood')
        #self.store_node_weight('Updated_Risk_likelihood_BSOC_Existing_Future_Control.xlsx', 'Node ID', 'Likelihood Exsiting Control Plus Future Control', 'consequence')
        #self.store_node_weight('Updated_Risk_likelihood_BSOC_Existing_Control.xlsx', 'Node ID', 'Likelihood Exsiting Control', 'likelihood')
        #self.subgraph_count()
        #self.subgraph_distribution()
        #self._cycles = list(nx.find_cycle(self._digraph_normal))
        Mygraph = self._digraph_normal.to_undirected()
        self._simple_cycles_2 = list(nx.cycle_basis(Mygraph))
        self._simple_cycles = list(nx.simple_cycles(self._digraph_normal))
        self._recursive_simple_cycles = list(nx.recursive_simple_cycles(self._digraph_normal))
        #print("Cycles in the graph:", self._cycles)
        print("DiCycles in the graph:", self._recursive_simple_cycles)
        print("Simple_cycles in the graph:", self._simple_cycles)
        print("Simple_cycles_2 in the graph:", self._simple_cycles_2)
        
        #self.max_flow_min_cut()
        #self.compare_kl_divergence('histograms_data_BSOC_Existing.xlsx','histograms_data_BSOC_Exsiting.xlsx', 'Node Counts')
        #self.json()
        #data = json_graph.node_link_data(self._digraph_normal)
        #with open('graph.json', 'w') as outfile:
         #   outfile.write(str(data).replace("'", '"'))
        #self.get_results_remove_according_to_weight('consequence')
        #self.get_results_remove_according_to_weight_totol_con('consequence')
        print("\n[{}] finished digraphPlot init()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("running_random........")
        #self.remove_by_risk_level_consequences_likelihood()
        print("finalised")
        #self.euclidean_spectral()
        #self.calculate_degree_distribution(self._digraph_normal)
        #self.calculate_kl_and_compare_raw("Raw.xlsx", "Results19.xlsx")
        #self.Granularity()
        
        #self.Squareform()
        #self.Granularity_based_on_existing_techniques()
        #nx.write_gexf(self._digraph_normal, r"C:\Users\uqylin13\CaNeTA\caneta-master\my_graph.gexf")
        
    def interactive_network(self):
        # Initialize the network
        net = Network(directed=True, height="750px", width="100%")
        net.toggle_physics(True)  # Enable physics initially for automatic layout
    
        # Define node categories and their corresponding colors
        categories = {
            "Technical": list(range(3, 76)),
            "Site": [0, 4, 6, 13, 14, 16, 17, 18, 15, 24, 21, 22, 23, 25, 38, 37, 39, 40, 41, 43, 42],
            "Corporate": [9, 20, 28, 27, 29, 30, 5, 32, 33, 8, 7],
            "Board": [34, 35, 36],
            "Stakeholders": [11, 12, 31, 1, 2],
            "Societal": [10]
        }
        
        color_map = {
            "Technical": "#FF5733",
            "Site": "#33FF57",
            "Corporate": "#5733FF",
            "Board": "#FFC300",
            "Stakeholders": "#C70039",
            "Societal": "#900C3F"
        }
    
        # Assign colors to nodes based on their categories
        for desc, node_id in self._node_ID.items():
            color = "#CCCCCC"  # Default color
            for category, nodes in categories.items():
                if node_id in nodes:
                    color = color_map[category]
                    break
            net.add_node(str(node_id), label=str(node_id), title=desc, size=10, color=color)
    
        # Add edges with labels
        for from_node, to_node in self._digraph_normal.edges():
            edge_weight = self._digraph_normal.edges[from_node, to_node].get('weight', 1)
            edge_label = str(int(edge_weight))
            net.add_edge(str(from_node), str(to_node), title=f"Weight: {edge_weight}", label=edge_label, width=1.5)
    
        # Temporarily show to stabilize the layout, then disable physics
        net.show("temp.html")
        net.toggle_physics(False)  # Disable physics for manual node adjustments
    
        # Save the network to HTML
        net.save_graph("my_network.html")
    
        # Embed custom JavaScript and a legend into the final HTML
        legend_html = """
        <div style="position:absolute; top:20px; left:20px; background-color:white; padding:10px; border:1px solid black; z-index:1000;">
            <strong>Node Legend</strong><br>
            <span style="color:#FF5733;">&#9679;</span> Technical<br>
            <span style="color:#33FF57;">&#9679;</span> Site<br>
            <span style="color:#5733FF;">&#9679;</span> Corporate<br>
            <span style="color:#FFC300;">&#9679;</span> Board<br>
            <span style="color:#C70039;">&#9679;</span> Stakeholders<br>
            <span style="color:#900C3F;">&#9679;</span> Societal<br>
        </div>
        """
    
        # Read the saved HTML and inject custom scripts and legend
        with open("my_network.html", "r") as file:
            content = file.read()
    
        modified_content = f"""
        <!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Causal Network Topology Analysis</title>
            <style>
                body {{ font-family: Arial, sans-serif; margin: 0; padding: 0; background: #f4f4f4; }}
                .header {{ background: #2C3E50; color: #fff; padding: 10px 20px; text-align: center; }}
                #mynetwork {{ height: 750px; width: 100%; border: 1px solid #2C3E50; margin-top: 20px; }}
                @media (max-width: 768px) {{
                    #mynetwork {{ height: 500px; }}  /* Responsive height adjustment */
                }}
            </style>
        </head>
        <body>
            <div class="header">
                <h1>Causal Network Topology Analysis</h1>
            </div>
            {legend_html}
            {content}
            <script>
                function toggleConfigPanel() {{
                    var configPanel = document.getElementById('configNetwork');
                    if (configPanel) {{
                        configPanel.style.display = configPanel.style.display === 'none' ? 'block' : 'none';
                    }}
                }}
            </script>
        </body>
        </html>
        """
        with open("my_network.html", "w") as file:
            file.write(modified_content)
    
        print('Interactive network setup complete and saved to my_network.html')

       
        
    def max_flow_min_cut(self):
        G = nx.DiGraph()

        # Add edges with capacities based on the adjacency matrix
        num_nodes = self._adjacency_matrix.shape[0]
        for i in range(num_nodes):
            for j in range(num_nodes):
                if self._adjacency_matrix[i, j] > 0:  # Ensure there's a positive connection
                    capacity = 1 / self._adjacency_matrix[i, j]
                    G.add_edge(str(i), str(j), capacity=capacity)

        source_nodes = {node for node, in_degree in G.in_degree() if in_degree == 0}
        sink_nodes = {node for node, out_degree in G.out_degree() if out_degree == 0}
        super_source = 'SuperS'
        super_sink = 'SuperT'
        G.add_node(super_source)
        G.add_node(super_sink)
        for src in source_nodes:
            G.add_edge(super_source, str(src), capacity=float('inf'))
        for sink in sink_nodes:
            G.add_edge(str(sink), super_sink, capacity=float('inf')) 
        flow_value, flow_dict = nx.maximum_flow(G, super_source, super_sink)
        print(f"Maximum flow value: {flow_value}")
        cut_value, (set1, set2) = nx.minimum_cut(G, super_source, super_sink)
        print(f"Minimum cut value: {cut_value}")
        print(f"Partition one: {set1}")
        print(f"Partition two: {set2}")
        for u in flow_dict:
            for v, flow in flow_dict[u].items():
                print(f"{u} -> {v}: {flow}")
        
        for u, v, data in G.edges(data=True):
            print(f"Edge from {u} to {v}, capacity: {data.get('capacity')}")

        # After maximum flow calculation
        print("Flow values:")
        for u, flow_edges in flow_dict.items():
            for v, flow_value in flow_edges.items():
                print(f"{u} -> {v}: {flow_value}")
    def Squareform(self):
        # Extract network metrics
        metrics_array = self.compute_network_metrics()
        
        # Initialize list of all node indices
        all_node_indices = list(range(len(metrics_array)))
        
        # Initialize list to store pairs
        pairs = []

        # While there are at least two nodes to pair
        while len(all_node_indices) > 1:
            # Compute distances only for remaining nodes
            distances = squareform(pdist(metrics_array[all_node_indices]))
            np.fill_diagonal(distances, np.inf)  # Avoid pairing a node with itself
            
            # Find the pair with the smallest distance
            i, j = np.unravel_index(np.argmin(distances, axis=None), distances.shape)
            
            # Add the actual node indices to the pairs list
            pairs.append((all_node_indices[i], all_node_indices[j]))
            
            # Remove paired nodes from the list of nodes to consider
            all_node_indices.pop(max(i, j))  # Pop indices in reverse order to maintain correct indexing
            all_node_indices.pop(min(i, j))
        
        # Handle the case of one remaining unpaired node
        if len(all_node_indices) == 1:
            print(f"Single Unpaired Node: {all_node_indices[0]}")

        return pairs
    
    def compute_network_metrics(self):
        # Gather network metrics for each node
        degree = np.array([self._digraph_normal.degree(n) for n in self._digraph_normal.nodes()])
        in_degree = np.array([self._digraph_normal.in_degree(n) for n in self._digraph_normal.nodes()])
        out_degree = np.array([self._digraph_normal.out_degree(n) for n in self._digraph_normal.nodes()])
        betweenness = np.array(list(nx.betweenness_centrality(self._digraph_normal, normalized=True).values()))
        closeness = np.array(list(nx.closeness_centrality(self._digraph_normal, wf_improved=True).values()))
        closeness_out = np.array(list(nx.closeness_centrality(self._digraph_normal.reverse(), wf_improved=True).values()))
        
        return np.vstack((degree, in_degree, out_degree, betweenness, closeness, closeness_out)).T
    
    def euclidean_spectral(self):
        metrics = self.calculate_network_metrics()
        df = pd.DataFrame(metrics)

        # Data validation and preprocessing
        df = df.replace([np.inf, -np.inf], np.nan).dropna()  # Replace inf with NaN and drop
        scaler = StandardScaler()  # Standardize features
        df_scaled = pd.DataFrame(scaler.fit_transform(df), index=df.index, columns=df.columns)

        paired_nodes, unpaired_nodes = self.iterative_pairing(df_scaled)

        if len(unpaired_nodes) == 1:
            print(f"Single Unpaired Node: {unpaired_nodes[0]}")
        else:
            print("All nodes have been successfully paired.")
        return paired_nodes

    def calculate_network_metrics(self):
        metrics = {
            'Degree': [self._digraph_normal.degree(n) for n in self._digraph_normal.nodes],
            'In_Degree': [self._digraph_normal.in_degree(n) for n in self._digraph_normal.nodes],
            'Out_Degree': [self._digraph_normal.out_degree(n) for n in self._digraph_normal.nodes],
            'Betweenness': list(nx.betweenness_centrality(self._digraph_normal, normalized=True).values()),
            'Closeness': list(nx.closeness_centrality(self._digraph_normal).values()),
            'Closeness_Out': list(nx.closeness_centrality(self._digraph_normal.reverse()).values()),
        }
        return metrics

    def iterative_pairing(self, df):
        all_pairs = []
        unpaired_nodes = df.index.tolist()

        while len(unpaired_nodes) > 1:  # Continue until 0 or 1 nodes remain unpaired
            df_sub = df.loc[unpaired_nodes]
            pairwise_dist = pairwise_distances(df_sub.values, metric='euclidean')
            similarity_matrix = np.exp(-pairwise_dist ** 2 / (2. * np.std(pairwise_dist) ** 2))
            np.fill_diagonal(similarity_matrix, 0)

            n_clusters = max(1, len(df_sub) // 2)
            spectral = SpectralClustering(n_clusters=n_clusters, affinity='precomputed', random_state=42)
            labels = spectral.fit_predict(similarity_matrix)

            new_pairs, unpaired_nodes = self.form_pairs(labels, unpaired_nodes)
            all_pairs.extend(new_pairs)

        return all_pairs, unpaired_nodes

    def form_pairs(self, labels, node_indices):
        pairs = []
        node_set = set(node_indices)  # Convert list to set for efficient operations

        for label in range(max(labels) + 1):
            nodes_in_cluster = [node_indices[i] for i, cluster_label in enumerate(labels) if cluster_label == label]

            # Form pairs within this cluster
            for i in range(0, len(nodes_in_cluster) - 1, 2):
                pairs.append((nodes_in_cluster[i], nodes_in_cluster[i + 1]))
                node_set.discard(nodes_in_cluster[i])
                node_set.discard(nodes_in_cluster[i + 1])

        return pairs, list(node_set)
        
          
    
         
        
        
              
        
    def adjust_to_continuous(self, input_dict):
        # Extract unique values from the dictionary and sort them
        unique_values = sorted(set(input_dict.values()))
        
        # Create a mapping from original to new, continuous values
        value_mapping = {}
        for i, value in enumerate(unique_values):
            value_mapping[value] = i
        
        # Adjust the dictionary using the mapping
        adjusted_dict = {k: value_mapping[v] for k, v in input_dict.items()}
        return adjusted_dict
        
    def conversion(self, adj_matrix, grouped_nodes):
        
    
        
        if len(grouped_nodes) == 0:
            print(adj_matrix)
            return(adj_matrix)
        n = len(adj_matrix[0])
        
        
        grouped_node_count = len(grouped_nodes)
        check_grouped = []
        for i in grouped_nodes:
            check_grouped.append(i)
        new_n = n - grouped_node_count  # Decrease size for each grouped pair
        stored_matrix = np.copy(adj_matrix[-1])
        original = np.copy(adj_matrix[0])
        # Create a mapping from old to new node indices                         
        
        ##flattened_grouped_nodes = flatten_grouped_nodes(grouped_nodes)
        new_index = 0
        new_new_index = 0
        already_count = []
        record = 0
        node_mapping_new = {}
        first = 0
        
    
        for grouped_tuple in check_grouped:
            n = len(adj_matrix[-1])
            if first == 0:
                for j in grouped_tuple:
                    node_mapping_new[j] = new_new_index // 2 
                    new_new_index += 1
                    
                    
                    already_count.append(j)
                not_grouped_index = max(node_mapping_new.values())+1
                
            if first != 0:
               
                for j in grouped_tuple:
                    min_value = min(grouped_tuple)
                    new_min= node_mapping_new[min_value]
                    node_mapping_new[j] = new_min
            first += 1
            
            for i in range(n):  
                if i not in grouped_tuple and i not in already_count:
                    if i not in node_mapping_new.keys():
                        
                        node_mapping_new[i] = not_grouped_index
                        not_grouped_index +=1
        
            
            
            node_mapping_new = dict(sorted(node_mapping_new.items(), key=lambda item: item[1]))
                        
            node_mapping_new = self.adjust_to_continuous(node_mapping_new)
                
                        
            print("new_node_map: " + str(node_mapping_new))
            discrete_matrix_len =  n - 1
            
            new_adj_matrix = np.zeros((discrete_matrix_len, discrete_matrix_len))
          
            
            n = len(stored_matrix)
            for i in range(n):
                new_i = node_mapping_new[i]
                
                for j in range(n):
                    new_j = node_mapping_new[j]
                    
                    
                    if stored_matrix[i][j] == 1:
                        if new_i != new_j:
                        
                            new_adj_matrix[new_i][new_j] = stored_matrix[i][j]
                    if stored_matrix[i][j] > 1:
                        if new_i != new_j:
                        
                            new_adj_matrix[new_i][new_j] = max(new_adj_matrix[new_i][new_j], stored_matrix[i][j] - 1)
                        
            
            adj_matrix.append(new_adj_matrix)
                            
            
           
        for new_adj_matrix in adj_matrix[1:]:    
            for i in range(len(new_adj_matrix)):
                for j in range(len(new_adj_matrix)):    
                    if new_adj_matrix[i][j] > 0 and new_adj_matrix[j][i] > 0:
                        if new_adj_matrix[i][j] >= new_adj_matrix[j][i]:
                            new_adj_matrix[j][i] = 0
                        if new_adj_matrix[i][j] < new_adj_matrix[j][i]:
                            new_adj_matrix[i][j] = 0
    
            
        
        
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
        
                 
        return adj_matrix

    def Granularity_based_on_existing_techniques(self):
        stable = 0
        final_data_2 = pd.DataFrame()
        final_data = pd.DataFrame()
        length_check = []
        conversion_time = 0
        method_list = [self.euclidean_spectral]
        for i in method_list:
            
            while True:
                matrix_list = [self._adjacency_matrix]
                converted_node_list = i()
                
                matrix_list = self.conversion(matrix_list, converted_node_list)
                
                for adjacency_matrix in matrix_list:
                    
                    are_matrices_same = np.array_equal(adjacency_matrix, self._adjacency_matrix)
                    if are_matrices_same == False:
                        self._adjacency_matrix = adjacency_matrix
                        print("CHECKKKKKKKKKKKKKK")
                        print(self._adjacency_matrix)
                 
                    # Create and save combined data for this iteration
                        self._digraph_normal = self.get_Digraph_granularity()
                        
                        output = self.calculate_betweenness_into_df(self._digraph_normal,conversion_time,0,stable)
                        
                        final_data = final_data.append(output,ignore_index=False)
                        length_check.append(len(final_data))
                        print("length: " + str(len(matrix_list)))
                        
                        conversion_time+=1
                if len(matrix_list[-1]) <=3:
                    break
                stable += 1
            
            print("Doooooooooooooooooooooone")
        for col in final_data.columns:
            final_data[col] = self.shift_non_nan_values_up(final_data[col])
           
        output_filename = "Results_Other_methods_pairwise.xlsx"
        final_data.to_excel(output_filename, index=False)
        print("start_kl_ks_Cvm")
        KL_differences = self.calculate_kl_KS_CvM_for_dataframe_origin(final_data)
           
        count = 1
        for i in KL_differences:
            result = pd.DataFrame({f'Compare {count}': [i[2],i[3],i[4]]})
               
            count+=1
            final_data_2 = final_data_2.append(result,ignore_index=False)
        for col in final_data_2.columns:
            final_data_2[col] = self.shift_non_nan_values_up(final_data_2[col])
        output_filename2 = "Results_other_methods_pairwise2.xlsx"
        final_data_2.to_excel(output_filename2, index=False)
        print("ssss")

    def find_completely_isolated_nodes(self, adj_matrix):
        completely_isolated_indices = []
        for i in range(len(adj_matrix)):
            # Check if the row and column at index i are all zeros
            if all(value == 0 for value in adj_matrix[i]) and all(adj_matrix[j][i] == 0 for j in range(len(adj_matrix))):
                completely_isolated_indices.append(i)
        return completely_isolated_indices
    
    def Granularity(self):
        cluster_total = []
        cluster_dic_total = []
        times_222 = 0
        largest_cc = max(nx.weakly_connected_components(self._digraph_normal), key=len)
        final_results_grouped_nodes = []
        final_results_dic = []
        subgraph = self._digraph_normal.subgraph(largest_cc)
        sparse_matrix = nx.to_scipy_sparse_matrix(subgraph, weight='weight')
        array_matrix = sparse_matrix.toarray()
        self._adjacency_matrix = array_matrix # remove optional*
        print(array_matrix)
        stored_matrix = self._adjacency_matrix.copy()
        stored_digraph = self._digraph_normal.copy()
        final_order = []
        record_metric = []
        granularity_count = 0
        original_size = len(self._adjacency_matrix.copy())
        for i in range(0,10):
            
            stable = 0
            conversion_time = 0
            final_data = pd.DataFrame()
            length_check = []
            diameter = []
            size = []
            final_data_2 = pd.DataFrame(index=range(10))
            method_list = ['OR','Cause_Con','AND']
            
            largest_cc = max(nx.weakly_connected_components(self._digraph_normal), key=len)
            final_order_grouped = []
            node_mapping_list = []
            node_mapping = []
            metrics_dict = {
                'network size': [],
                'average degree': [],
                'average betweenness': [],
                'average in_closeness': [],
                'average out_closeness': [],
                'average diameter': []
            }
            
    
            #self.plot_Digraph_initial_transparent(granularity_count)
            while True:
                
                
                matrix_list = [self._adjacency_matrix]
                
                adjacency_matrix_list, changes, consistency,final_order_grouped, node_mapping_list = Granularity.running_granularity(method_list, matrix_list,[])
                
                # Check for termination condition: only one node left or no changes
                final_node_dic = [i for i in node_mapping_list]
                node_mapping.append(final_node_dic)
               
                
                final_order.append(final_order_grouped)          
                final_order_grouped = []
                
                for adjacency_matrix in adjacency_matrix_list:
                    granularity_count += 1
                    #if  granularity_count == int(original_size/5) or granularity_count == int(original_size/5) * 2 or granularity_count == int(original_size/5) * 3 or granularity_count == int(original_size/5) * 4 or granularity_count == int(int(original_size/5) * 4.5) or granularity_count == int(int(original_size/5) * 4.75):
                    #self.plot_Digraph_initial_transparent(granularity_count)
                        
                    
                    are_matrices_same = np.array_equal(adjacency_matrix, self._adjacency_matrix)
                    if are_matrices_same == False:
                        self._adjacency_matrix = adjacency_matrix
                        
                        
                        #if granularity_count == 3:
                    # Create and save combined data for this iteration
                         #   self._digraph_normal = self.get_Digraph_granularity()
                          #  self.plot_Digraph_initial_transparent(granularity_count)
                        self._digraph_normal = self.get_Digraph_granularity()
                        
                        
                        largest_diameter = 0
                        sccs = list(nx.strongly_connected_components(self._digraph_normal))
                        wccs = list(nx.weakly_connected_components(self._digraph_normal))
                        
                        
                        size.append(len(self._digraph_normal))
                        
                                
        
                        
                        output = self.calculate_betweenness_into_df(self._digraph_normal,conversion_time,consistency,stable)
                        self.calculate_and_collect_network_metrics(self._digraph_normal, len(self._digraph_normal), metrics_dict)
                        final_data = final_data.append(output,ignore_index=False)
                        length_check.append(len(final_data))
                        record_metric.append(metrics_dict)
                        
                        
                        conversion_time+=1
                
                if len(adjacency_matrix_list[-1]) <=1 or not changes:
                    break
                
                stable += 1
                
                
                    
            
            
            metrics_df = pd.DataFrame(metrics_dict)
            spearman_corr_matrix = metrics_df.corr(method='spearman')
            
            
            
            # Set up the matplotlib figure
            f, ax = plt.subplots(figsize=(13,9))
            
            # Generate a custom diverging colormap
            cmap = sns.diverging_palette(230, 20, as_cmap=True)
            plt.rcParams.update({
                'font.family': 'sans-serif',
                'font.size': 10,
                })
            
            # Generate a mask for the upper triangle
            mask = np.triu(np.ones_like(spearman_corr_matrix, dtype=bool))
            

        
            # Draw the heatmap with the mask and correct aspect ratio
            sns.heatmap(spearman_corr_matrix, mask=mask, cmap=cmap, vmax=1.0, center=0,
                        square=True, linewidths=.5, cbar_kws={"shrink": .5}, annot=True, fmt=".2f")
            plt.xticks(rotation=0, fontsize=8.5)
            plt.yticks(rotation=0, fontsize=8.5)
            plt.tight_layout()

            plt.savefig(f'spearman_corr_{times_222}.png', dpi=300)
            plt.close()
            
             

            print(adjacency_matrix_list[-1])
            print("Doooooooooooooooooooooone")
            
            # After all iterations, create the linkage matrix and plot the dendrogram
            #total_nodes = max(max(pair[:2]) for pair in recorder.grouping_operations) + 1
            #linkage_matrix = self.create_linkage_matrix(recorder.grouping_operations, total_nodes)
            #self.plot_dendrogram(linkage_matrix)
           
            
            for col in final_data.columns:
                final_data[col] = self.shift_non_nan_values_up(final_data[col])
            
            paired_tuples = []
            final_order_tuple = []
            final_tuple = []
            '''
            for final_order_1 in final_order:  
                for k in final_order_1:
                    for i in range(0, len(k) - 1, 2):
                        paired_tuples.append((k[i], k[i + 1]))
                    final_order_tuple.append(paired_tuples)
                    paired_tuples = []
                final_tuple.append(final_order_tuple)
                final_order_tuple = []
                '''
            
            output_filename = f"Results1{times_222}.xlsx"
            final_data.to_excel(output_filename, index=False)
            
            KL_differences = self.calculate_kl_for_betweenness(final_data)
            
            count = 1
            for i in KL_differences:
                # Create 'result' DataFrame with an appropriate index that matches 'final_data_2'
                print(i)
                result = pd.DataFrame({f'Compare {count}': [i[2], i[3], i[4], i[5], i[6], i[7], i[8],i[9], i[10], i[11]]}, index=final_data_2.index[:10])
            
                # Concatenate 'result' with 'final_data_2' horizontally (axis=1) without introducing NaNs due to index misalignment
                final_data_2 = pd.concat([final_data_2, result], axis=1)
                
                count += 1
            print(final_data_2)
            
            final_data_2.fillna(1, inplace=True)
            total_columns = len(final_data_2.columns)
           
            position_based_values = {col: 1 - (i / total_columns) for i, col in enumerate(final_data_2.columns)}

            # Append these values as a new row to the DataFrame
            final_data_2.loc[len(final_data_2)] = position_based_values
            
            for row in final_order_grouped:
                final_data_2.loc[len(final_data_2)] = row
            output_filename2 = f"Results2{times_222}.xlsx"
            final_data_2.to_excel(output_filename2, index=False)
            
            times_222+=1
            self._adjacency_matrix= stored_matrix
            self._digraph_normal= stored_digraph
            final_results_grouped_nodes.append(final_tuple)
            final_results_dic.append(node_mapping)
            
            cluster_total.append(final_order.copy())
            final_order = []
            final_dic_1 = final_results_dic[0] 
            final_results_dic= []
            cluster_dic_total.append(final_dic_1.copy())
        
        timee = 0
        for i, j in zip(cluster_total, cluster_dic_total):
            Granularity.plot_dendrogram(i,j, timee)
            timee+=1
       
        
        
        
       
    
    def plot_Digraph_initial_3(self,time):
        """Plot the directed graph structure on the canvas"""
        # Create a figure without using plt.figure()
        fig = Figure(figsize=(6, 6), dpi=200)
    
        # Add a subplot without using plt directly
        ax = fig.add_subplot(111)
        ax.axis('off')
        fig.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
        # Use the figure and ax objects directly for plotting
        pos = nx.nx_agraph.graphviz_layout(self._digraph_normal)
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {'font_size': 5, 'font_color': 'white', 'node_color': 'black', 'node_size': 80,
                   'style': 'solid', 'width': 0.3, 'arrows': True, 'arrowsize': 2.5,
                   'ax': ax}  # Pass the ax object to draw_networkx
        nx.draw_networkx(self._digraph_normal, pos, edge_color=colors, **options)
        fig.tight_layout(pad=0)
        # Save the figure
        figurename = f"initial_Digraph_{time}.png"
        fig.savefig(figurename, dpi=500, pad_inches=0, bbox_inches='tight')
        
    
        
        
    def calculate_kl_divergence(self, distribution1, distribution2):
       
        
        if len(distribution1) > len(distribution2):
            distribution2 = np.pad(distribution2, (0, len(distribution1) - len(distribution2)), 'constant')
        elif len(distribution2) > len(distribution1):
            distribution1 = np.pad(distribution1, (0, len(distribution2) - len(distribution1)), 'constant')
        
        distribution1 = np.array(distribution1, dtype=float)
        distribution2 = np.array(distribution2, dtype=float)
    
        # Apply Laplace smoothing
        smoothed_distribution1 = distribution1 + 1
        smoothed_distribution2 = distribution2 + 1
        

        # Normalize the distributions to sum to 1 to get probability distributions
        smoothed_distribution1 /= smoothed_distribution1.sum()
        smoothed_distribution2 /= smoothed_distribution2.sum()
    
        '''
        # Normalize the counts to probabilities if they are not already
        distribution1 = np.array(distribution1) / sum(distribution1) if sum(distribution1) != 1 else np.array(distribution1)
        distribution2 = np.array(distribution2) / sum(distribution2) if sum(distribution2) != 1 else np.array(distribution2)
        
        # Ensure distributions are the same length
        min_length = min(len(distribution1), len(distribution2))
        distribution1 = distribution1[:min_length]
        distribution2 = distribution2[:min_length]
        
        
        # Avoid division by zero and only consider positive elements of distribution1
        distribution2 = np.where(distribution2 == 0, 1e-10, distribution2)
        '''
        
        
    
        # Calculate the KL divergence
        kl_div = np.sum(smoothed_distribution1 * np.log(smoothed_distribution1 / smoothed_distribution2))
        
        return kl_div
    
    def calculate_kl_divergence_betweenness(self, distribution1, distribution2):
    
        # Ensure both distributions are the same length by padding with zeros if necessary
        if len(distribution1) > len(distribution2):
            distribution2 = np.pad(distribution2, (0, len(distribution1) - len(distribution2)), 'constant')
        elif len(distribution2) > len(distribution1):
            distribution1 = np.pad(distribution1, (0, len(distribution2) - len(distribution1)), 'constant')
        
        # Convert to float arrays
        distribution1 = np.array(distribution1, dtype=float)
        distribution2 = np.array(distribution2, dtype=float)
        
        # Replace zero probabilities with a small value (e.g., 1e-10) to avoid division by zero or log(0)
        distribution1 = np.where(distribution1 == 0, 1e-10, distribution1)
        distribution2 = np.where(distribution2 == 0, 1e-10, distribution2)
    
        # Calculate the KL divergence (element-wise), ensuring no division by zero or log of zero
        kl_div = np.sum(distribution1 * np.log(distribution1 / distribution2))
        
        return kl_div
    
    # Function to apply KL divergence calculation to DataFrame
    
    
    def calculate_kl_KS_CvM_for_dataframe(self, df):
       
        relevant_cols = [col for col in df.columns if col.startswith("Number of Nodes_consistency:")]
        relevant_cols2 = [col for col in df.columns if col.startswith("P(Degree >= X) stable:")]
        relevant_cols3 = [col for col in df.columns if col.startswith('Edge_number:')]
        
        sorted_cols = sorted(relevant_cols, key=lambda x: int(x.split(': ')[-1].split('_')[0]))
        sorted_cols2 = sorted(relevant_cols2, key=lambda x: int(x.split(': ')[-1].split('_')[0]))
        sorted_cols_edge = sorted(relevant_cols3, key=lambda x: int(x.split(': ')[-1].split('_')[0]))
        Final = []
        
        
        for i in range(len(sorted_cols) - 1):
            
            distribution1 = df[sorted_cols[i]].dropna().tolist()
            distribution11 = distribution1.copy()
            distribution2 = df[sorted_cols[i+1]].dropna().tolist()
            distribution22 = distribution2.copy()
            max_length_1 = max(len(distribution11), len(distribution22))
            
          
            
                
           
            distribution3 = df[sorted_cols2[i]].dropna().tolist()
            distribution4 = df[sorted_cols2[i+1]].dropna().tolist()
            
            
            WSRT_p_value = 0
            WSRT_stat = 1
            emd = 0
            p_value_spearman = 0
            corr_spearman = 0
            js_divergence = 1
            total_nodes_3 = sum(distribution1)
            total_nodes_4 = sum(distribution2)
            probability_degree_distribution_3 = [count / total_nodes_3 for count in distribution1]
            probability_degree_distribution_4 = [count / total_nodes_4 for count in distribution2]
            distribution33 = distribution3.copy()
            distribution44 = distribution4.copy()
            
            max_length = max(len(distribution33), len(distribution44))
            max_length_2 = max(len(probability_degree_distribution_3), len(probability_degree_distribution_4))

            # Pad the shorter distribution with zeros until both have the same length
            
                
            distribution_edge_1 = df[sorted_cols_edge[i]].dropna().tolist()
            distribution_edge_2 = df[sorted_cols_edge[i+1]].dropna().tolist()
            
            distribution3 += [0] * (max_length - len(distribution3))
            distribution4 += [0] * (max_length - len(distribution4))
            distribution33 = distribution3.copy()
            distribution44 = distribution4.copy()
            distribution33 = np.array(distribution33)
            distribution44 = np.array(distribution44)

            kl_div = self.calculate_kl_divergence(distribution1, distribution2)
            
                
            if len(distribution3) != 0 and len(distribution4) != 0:
            
                ks_stat, ks_pvalue = ks_2samp(distribution3, distribution4)
                emd = wasserstein_distance(distribution3, distribution4)
                V_Kuiper, p_value_Kuiper = kuiper_two(distribution33, distribution44)
                WSRT_stat, WSRT_p_value = stats.wilcoxon(distribution3, distribution4)
            
            
            probability_degree_distribution_3 += [0] * (max_length_2 - len(probability_degree_distribution_3))
            probability_degree_distribution_4 += [0] * (max_length_2 - len(probability_degree_distribution_4))
            distribution11 += [0] * (max_length_1 - len(distribution11))
            distribution22 += [0] * (max_length_1 - len(distribution22))
            
            if len(probability_degree_distribution_4) > 0:
                js_divergence = jensenshannon(probability_degree_distribution_3, probability_degree_distribution_4, base=2)
                js_divergence = math.sqrt(js_divergence)
                print("dsdsdsdsddsdssdsdsdsdsds")
                print(js_divergence)
                print('sdasddddddddddddddddddddddddddddddddddddddddddddddddddddd')
                
                print(WSRT_stat)
            
            
                
            if len(distribution_edge_2) > 0:
                edge_difference = distribution_edge_1[0] - distribution_edge_2[0]
            
            
            
           
            #cvm_stat = cramervonmises_2samp(distribution3, distribution4)
            #cvm_stat = cvm_stat.statistic
            Final.append((sorted_cols[i], sorted_cols[i+1], kl_div,ks_stat, ks_pvalue, edge_difference,js_divergence,WSRT_stat, WSRT_p_value, emd, V_Kuiper, p_value_Kuiper))
        
        return Final
    
    def calculate_kl_for_betweenness(self, df):
       
        relevant_cols = [col for col in df.columns if col.startswith("Number of Nodes_consistency:")]
        
        
        sorted_cols = sorted(relevant_cols, key=lambda x: int(x.split(': ')[-1].split('_')[0]))
       
        Final = []
        
        
        for i in range(len(sorted_cols) - 1):
            
            distribution1 = df[sorted_cols[i]].dropna().tolist()
            distribution11 = distribution1.copy()
            distribution2 = df[sorted_cols[i+1]].dropna().tolist()
            distribution22 = distribution2.copy()
            max_length_1 = max(len(distribution11), len(distribution22))
            
          
            
                
           
           

            kl_div = self.calculate_kl_divergence_betweenness(distribution1, distribution2)
            
                
            
            
            
            
                
            
            
           
            #cvm_stat = cramervonmises_2samp(distribution3, distribution4)
            #cvm_stat = cvm_stat.statistic
            Final.append((sorted_cols[i], sorted_cols[i+1], kl_div,sorted_cols[i+1], sorted_cols[i+1], sorted_cols[i+1],sorted_cols[i+1],sorted_cols[i+1], sorted_cols[i+1], sorted_cols[i+1], sorted_cols[i+1], sorted_cols[i+1]))
        
        return Final
    
    def calculate_kl_KS_CvM_for_dataframe_origin(self, df):
       
       
        
        relevant_cols = [col for col in df.columns if col.startswith("Number of Nodes_consistency:")]
        relevant_cols2 = [col for col in df.columns if col.startswith("P(Degree >= X) stable:")]
        relevant_cols3 = [col for col in df.columns if col.startswith('Edge_number:')]
        
        sorted_cols = sorted(relevant_cols, key=lambda x: int(x.split(': ')[-1].split('_')[0]))
        sorted_cols2 = sorted(relevant_cols2, key=lambda x: int(x.split(': ')[-1].split('_')[0]))
        sorted_cols_edge = sorted(relevant_cols3, key=lambda x: int(x.split(': ')[-1].split('_')[0]))
        Final = []
        distribution0 = df[sorted_cols[0]].dropna().tolist()
        total_0 = sum(distribution0)
        probability_degree_distribution_0 = [count / total_0 for count in distribution0]
        cumulative_0 = df[sorted_cols2[0]].dropna().tolist()
        distribution_edge_0 = df[sorted_cols_edge[0]].dropna().tolist()
        max_length_2 = max(len(probability_degree_distribution_3), len(probability_degree_distribution_0))
        for i in range(len(sorted_cols) - 1):
            
            distribution1 = df[sorted_cols[i]].dropna().tolist()
            distribution11 = distribution1.copy()
            
            max_length_1 = max(len(distribution11), len(distribution0))
               
           
            distribution3 = df[sorted_cols2[i]].dropna().tolist()
            
            
            
            WSRT_p_value = 0
            WSRT_stat = 1
            js_divergence = 1
            total_nodes_3 = sum(distribution1)
           
            probability_degree_distribution_3 = [count / total_nodes_3 for count in distribution1]
            
            distribution33 = distribution3.copy()
            
            
            max_length = max(len(distribution33), len(distribution0))
            max_length_2 = max(len(probability_degree_distribution_3), len(probability_degree_distribution_0))

            # Pad the shorter distribution with zeros until both have the same length
            
                
            distribution_edge_1 = df[sorted_cols_edge[i]].dropna().tolist()
            
            
            
            kl_distribution_0 = distribution0.copy()
            kl_div = self.calculate_kl_divergence(kl_distribution_0, distribution1)
            
            ks_distribution_0 = distribution0.copy()
            if len(distribution3) != 0:
            
                ks_stat, ks_pvalue = ks_2samp(ks_distribution_0, distribution3)
                
            
            
            probability_degree_distribution_3 += [0] * (max_length_2 - len(probability_degree_distribution_3))
            probability_degree_distribution_0 += [0] * (max_length_2 - len(probability_degree_distribution_0))
            
            
            if len(probability_degree_distribution_3) > 0:
                js_divergence = jensenshannon(probability_degree_distribution_0, probability_degree_distribution_3, base=2)
                js_divergence = math.sqrt(js_divergence)
                print("dsdsdsdsddsdssdsdsdsdsds")
                print(js_divergence)
                print('sdasddddddddddddddddddddddddddddddddddddddddddddddddddddd')
                WSRT_stat, WSRT_p_value = stats.wilcoxon(probability_degree_distribution_0, probability_degree_distribution_3,zero_method='zsplit')
                print(WSRT_stat)
            
            
                
            if len(distribution_edge_1) > 0:
                edge_difference = distribution_edge_0[0] - distribution_edge_1[0]
            
            
            
           
            #cvm_stat = cramervonmises_2samp(distribution3, distribution4)
            #cvm_stat = cvm_stat.statistic
            Final.append((sorted_cols[i], sorted_cols[i+1], kl_div,ks_stat, ks_pvalue, edge_difference,js_divergence,WSRT_stat, WSRT_p_value))
        
        return Final
    
    def get_Digraph_granularity(self):
        """ Return the directed graph structure from the adjacency matrix"""
        G = nx.DiGraph(directed=True)
        
        for i in range(len(self._adjacency_matrix)):
            for j in range(len(self._adjacency_matrix)):
                weight=int(self._adjacency_matrix[i,j])
                if weight>0:
                    color = self.get_color(weight-1)
                    G.add_edge(str(i), str(j), color=color,weight=weight)
        
        
        return G      
        
    def get_Digraph_granularity_new(self):
        """ Return the directed graph structure from the adjacency matrix"""
        G = nx.DiGraph(directed=True)
        
        for i in range(len(self._adjacency_matrix)):
            for j in range(len(self._adjacency_matrix)):
                weight=int(self._adjacency_matrix[i,j])
                if weight>0:
                    color = self.get_color_new(weight-1)
                    G.add_edge(str(i), str(j), color=color,weight=weight)
        
        
        return G
    
    def shift_non_nan_values_up(self, column):
    
        non_nan_values = column.dropna().reset_index(drop=True)
    
        nan_values = [np.nan] * (len(column) - len(non_nan_values))
   
        return pd.Series(non_nan_values.tolist() + nan_values, index=column.index)
    
    def calculate_and_collect_network_metrics(self, G, network_sizes, metrics_dict):
        
        # Example metrics to calculate (you can expand this with your actual metrics)
        average_degree = sum(dict(G.degree()).values()) / G.number_of_nodes() if G.number_of_nodes() else 0
        betweenness = nx.betweenness_centrality(G)
        average_betweenness = sum(betweenness.values()) / len(betweenness) if len(betweenness) else 0
        in_closeness = nx.closeness_centrality(G)
        average_in_closeness = sum(in_closeness.values()) / len(in_closeness) if len(in_closeness) else 0
        out_closeness = nx.closeness_centrality(G.reverse())
        average_out_closeness = sum(out_closeness.values()) / len(out_closeness) if len(out_closeness) else 0
        AA = G.copy()
        largest_cc_subgraph_undirected = AA.to_undirected()
        diameter = nx.diameter(largest_cc_subgraph_undirected) if len(AA) else 0
        # Store calculated metrics
        metrics_dict['network size'].append(G.number_of_nodes())
        metrics_dict['average degree'].append(average_degree)
        metrics_dict['average betweenness'].append(average_betweenness)
        metrics_dict['average in_closeness'].append(average_in_closeness)
        metrics_dict['average out_closeness'].append(average_out_closeness)
        metrics_dict['average diameter'].append(diameter)

    
        return metrics_dict 
    
    def calculate_degree_into_df(self, G,times,consistency,stable):
        
        degrees = [G.in_degree(n) + G.out_degree(n) for n in G.nodes()]
       
        max_degree = max(degrees) if degrees else 0
        degree_series = pd.Series(np.zeros(max_degree), index=np.arange(1, max_degree + 1))
        degree_counts = pd.Series(degrees).value_counts().sort_index()
        degree_series.update(degree_counts)
        cumulative_counts = degree_series.iloc[::-1].cumsum().iloc[::-1]
        probability_dist = cumulative_counts / len(G.nodes())
        edge_number = G.number_of_edges()
        
        
        degree_data = pd.DataFrame({
            f'Degree times: {times}': degree_series.index,
            f'Number of Nodes_consistency: {times}_{consistency}': degree_series.values,
            'Cumulative Nodes >= Degree': cumulative_counts.values,
            f'P(Degree >= X) stable: {times}_{stable}': probability_dist.values,
            f'Edge_number: {times}': edge_number
        })
        
        selected_columns = degree_data[[f'Degree times: {times}',f'Number of Nodes_consistency: {times}_{consistency}',
                                        f'P(Degree >= X) stable: {times}_{stable}',f'Edge_number: {times}']]
        
       

        return selected_columns
    
    def calculate_betweenness_into_df(self, G, times, consistency, stable):
        # Calculate betweenness centrality for each node
        betweenness = nx.betweenness_centrality(G, normalized=True)
        
        # Extract betweenness values into a list
        betweenness_values = list(betweenness.values())
        
        # Optional: Round betweenness values to avoid floating-point precision issues (rounded to 5 decimal places)
        betweenness_values_rounded = [round(b, 5) for b in betweenness_values]
        
        # Get the maximum betweenness value (no scaling)
        max_betweenness = max(betweenness_values_rounded) if betweenness_values_rounded else 0
        
        # Create a series with zero initialization for the range of betweenness values
        betweenness_series = pd.Series(np.zeros(len(np.unique(betweenness_values_rounded))), 
                                       index=np.unique(betweenness_values_rounded))
        
        # Count the number of occurrences of each betweenness value (rounded)
        betweenness_counts = pd.Series(betweenness_values_rounded).value_counts().sort_index()
        
        # Update the series with actual betweenness counts
        betweenness_series.update(betweenness_counts)
        
        # Calculate the probability distribution (P(Betweenness = X))
        probability_dist = betweenness_series / len(G.nodes())
        
        # Get the number of edges in the graph
        edge_number = G.number_of_edges()
        
        # Create a DataFrame with betweenness centrality and probability distribution
        betweenness_data = pd.DataFrame({
            f'Betweenness times: {times}': betweenness_series.index,
            f'Number of Nodes_consistency: {times}_{consistency}': betweenness_series.values,  # Store the probability distribution here
            f'P(Betweenness = X) stable: {times}_{stable}': probability_dist.values,
            f'Edge_number: {times}': edge_number
        })
        
        # Select the columns to return
        selected_columns = betweenness_data[[f'Betweenness times: {times}', 
                                             f'Number of Nodes_consistency: {times}_{consistency}',
                                             f'P(Betweenness = X) stable: {times}_{stable}', 
                                             f'Edge_number: {times}']]
        
        return selected_columns
   
    def calculate_degree_distribution(self,G):
        degrees = [G.in_degree(n) + G.out_degree(n) for n in G.nodes()]
        max_degree = max(degrees) if degrees else 0
        degree_series = pd.Series(np.zeros(max_degree), index=np.arange(1, max_degree + 1))
        degree_counts = pd.Series(degrees).value_counts().sort_index()
        degree_series.update(degree_counts)
        cumulative_counts = degree_series.iloc[::-1].cumsum().iloc[::-1]
        probability_dist = cumulative_counts / len(G.nodes())
        degree_data = pd.DataFrame({
           
            'Number of Nodes_consistency:': degree_series.values,
            
        })
        output_filename = "Raw.xlsx"
        degree_data.to_excel(output_filename, index=False)
    
    def calculate_kl_and_compare_raw(self, file1, file2):
        df = pd.read_excel(file2)
        df2 = pd.read_excel(file1)
       
        relevant_cols = [col for col in df.columns if col.startswith("Number of Nodes_consistency:")]
        relevant_cols2 = [col for col in df2.columns if col.startswith("Number of Nodes_consistency:")]
        
        
        sorted_cols = sorted(relevant_cols, key=lambda x: int(x.split(': ')[-1].split('_')[0]))
        print(sorted_cols)
        
        Final = []
        
        distribution2 = df2[relevant_cols2[0]].dropna().tolist()
        for i in range(len(sorted_cols) - 1):
            
            distribution1 = df[sorted_cols[i]].dropna().tolist()
            
            kl_div = self.calculate_kl_divergence(distribution1, distribution2)
            
            Final.append(kl_div)
        print(Final)
        print(Final.index(min(Final)))
    
    
    def compare_distributions(self, file1, file2):
        df1 = pd.read_excel(file1)
        df2 = pd.read_excel(file2)
    
        # Get the distribution column from the first file
        distribution1 = df1["P(Degree >= X) stable: 0_0"].dropna().values
        
        calculator = KL_DivergenceCalculator()
        
        # Iterate over columns in the second file and calculate KL divergence
        kl_results = {}
        for col in df2.columns:
            if col.startswith("P(Degree >= X)"):
                distribution2 = df2[col].dropna().values
                kl_div = calculator.calculate_kl_divergence(distribution1, distribution2)
                kl_results[col] = kl_div
    
        return kl_results

        
    
    def create_linkage_matrix(self, grouping_operations, total_initial_nodes):
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
    
    
    def plot_dendrogram(self, linkage_matrix):
        # Ensure linkage_matrix is a NumPy array of type float for dendrogram function
        linkage_matrix = np.array(linkage_matrix, dtype=float)
        # Plot the dendrogram
        print(linkage_matrix)
        dendrogram(linkage_matrix)
        plt.title('Grouping Dendrogram')
        plt.xlabel('Index of Node/Group')
        plt.ylabel('Merge Order')
        plt.show()

    
    def community(self):
        self.start_girvan_newman(self._digraph_normal, [10])
        
    def start_girvan_newman(self, graph, depth):
        
        
        if isinstance(graph, nx.DiGraph):
            graph = graph.to_undirected()
        
        # Apply Girvan-Newman algorithm
        communities_generator = girvan_newman(graph)
        community_df = pd.DataFrame(columns=['Iteration', 'Community Number', 'Nodes'])
        
        for i in depth:
            communities = None
            for j in range(i):
                
                communities = next(communities_generator, None)
                if communities:
                    num_communities = len(communities)
                    colors = plt.cm.tab20(np.linspace(0, 1, num_communities))
                    colors = np.array([color for color in colors if not np.allclose(color, [0, 0, 0, 1], atol=0.3)])
                
                    community_colors = {node: colors[a % len(colors)] for a, community in enumerate(communities) for node in community}
                    for k, community in enumerate(communities, start=1):
                        sorted_community = sorted(community)
                        
                        mapped_community = []
                        for node in sorted_community:
                            for description, nodes in self._node_ID.items():
                                if node == str(nodes):
                                    mapped_community.append(f"{node}:{description}")
                        
                        community_df = community_df.append({
                            'Iteration': j+1,
                            'Community Number': k,
                            'Nodes': ', '.join(mapped_community)
                            }, ignore_index=True)
                    
                    # Assign colors to nodes based on their last known community
                    
    
                    # Draw the graph
                    pos = nx.nx_agraph.graphviz_layout(graph)
                    nx.draw(graph, pos, with_labels=True, node_color=[community_colors[node] for node in graph.nodes()], arrows=False, font_size = 3, node_size = 50)
                    plt.savefig(f"Iteration {j+1}"+ ".png", dpi=300, pad_inches=0)
                    
                    plt.close()
                else:
                    break  # Exit loop if no further division is possible
        print(self._node_ID)
        # Save the community information to an Excel file using xlsxwriter
        with pd.ExcelWriter('girvan_newman_10_iterations.xlsx', engine='xlsxwriter') as writer:
            community_df.to_excel(writer, index=False, sheet_name='Communities')
        print('finished')
            
    def kl_divergence(self, p, q):
        return entropy(p, q)
    
    def safe_float(self, val):
        try:
            return int(val)
        except ValueError:
            return 0
    def subgraph_distribution(self):
        G= self._digraph_normal
        # Generate histograms for number of nodes per subgraph
        node_counts = [len(sg) for sg in nx.weakly_connected_components(self._digraph_normal)]
        hist_nodes, bins_nodes = np.histogram(node_counts, bins=range(1, max(node_counts)+2),density=False)

        # Generate histograms for total consequence per subgraph
        total_consequences = [sum(self.safe_float(G.nodes[n]['consequence']) for n in sg if 'consequence' in G.nodes[n]) for sg in nx.weakly_connected_components(G)]
        hist_consequences, bins_consequences = np.histogram(total_consequences, bins=range(1, max(total_consequences)+2),density=False)
        
        plt.hist(node_counts, bins=range(1, max(node_counts)+2), edgecolor='black', align='left')
        plt.xlabel('Number of Nodes per Subgraph')
        plt.ylabel('Number of Subgraphs')
        plt.show()
        
        plt.hist(total_consequences, bins=range(1, max(node_counts)+2), edgecolor='black', align='left')
        plt.xlabel('Total Consequences per Subgraph')
        plt.ylabel('Number of Subgraphs')
        plt.show()
        df_nodes = pd.DataFrame({'Bins': bins_nodes[:-1], 'Values': hist_nodes})
        df_consequences = pd.DataFrame({'Bins': bins_consequences[:-1], 'Values': hist_consequences})
        with pd.ExcelWriter('histograms_data_BSOC_No.xlsx') as writer:
            df_nodes.to_excel(writer, sheet_name='Node Counts', index=False)
            df_consequences.to_excel(writer, sheet_name='Total Consequences', index=False)
    
    def merge_histograms(self,hist1, bins1, hist2, bins2):
        # Create a common set of bins by taking the union
        common_bins = np.union1d(bins1, bins2)
    
        # Create new histograms using the common bins
        hist1_new, _ = np.histogram(hist1, bins=common_bins, density=True)
        hist2_new, _ = np.histogram(hist2, bins=common_bins,density=True)
    
        return hist1_new, hist2_new

    def compare_kl_divergence(self, file1, file2, sheet_name):
        """ Compare the KL-divergence between histograms in two Excel files. """

        # Read the Excel files into pandas DataFrames
        df1 = pd.read_excel(file1, sheet_name=sheet_name)
        df2 = pd.read_excel(file2, sheet_name=sheet_name)

        # Retrieve the histogram data
        hist1 = df1['Bins'].values
        bins1 = df1['Values'].values
    
        hist2 = df2['Bins'].values
        bins2 = df2['Values'].values

        # Merge histograms to common bins
        hist1_new, hist2_new = self.merge_histograms(hist1, bins1, hist2, bins2)

        # Calculate KL-divergence
        kl_div = self.kl_divergence(hist1_new, hist2_new)
        print("11111111111" + str(kl_div))
        return kl_div
    
    def get_results_remove_according_to_weight_totol_con(self, nodeweight):
        removed_node, consequence_remaining = self.remove_according_to_weight_total_con(nodeweight)
        a = []
        for j in range(len(removed_node)+2):
            a.append(j)
        consequence_remaining.append(0)
        y = np.array(consequence_remaining)
        area = int(simps(y, x=np.array(a)))
        
        
        workbook = xlsxwriter.Workbook('Robustness_' + nodeweight+ '.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Remaining consequence")
        worksheet_robustness.write("C1", "Area Under Curve consequence")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in removed_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in consequence_remaining:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        workbook.close()
    
    def remove_according_to_weight_total_con(self, nodeweight):
        node_id_removed = []
        consequence_remaining = []
        nodes_with_consequence = []
        nodes_with_likelihood = []
        for node_id, data in self._digraph_normal.nodes(data=True):
            if 'likelihood' in data and not isinstance(data['likelihood'], str):
                nodes_with_likelihood.append((node_id, data['likelihood']))
        for node_id, data in self._digraph_normal.nodes(data=True):
            if 'consequence' in data and not isinstance(data['consequence'], str):
                nodes_with_consequence.append((node_id, data['consequence']))
        consequence_remaining.append(sum([t[1] for t in nodes_with_consequence]))
        while len(nodes_with_consequence) != 0:
            
            
            
            # Sort nodes by consequence score in descending order
            
            sorted_nodes = sorted(nodes_with_likelihood, key=lambda x: x[1], reverse=True)

            # Extract only the node IDs
            sorted_node_ids = [node[0] for node in sorted_nodes]
                
            node_left = self.active_nodes(self._adjacency_matrix)
            chosen_node = sorted_node_ids[0]
            
            self._matrix.deleteNode([chosen_node])
            node_id_removed.append(chosen_node)
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._digraph_normal = self.get_Digraph()
            nodes_with_consequence_new = [t for t in nodes_with_consequence if t[0] in self._digraph_normal.nodes()]
            nodes_with_consequence = nodes_with_consequence_new
            consequence_remaining.append(sum([t[1] for t in nodes_with_consequence]))
            nodes_with_likelihood_new = [y for y in nodes_with_likelihood if y[0] in self._digraph_normal.nodes()]
            nodes_with_likelihood = nodes_with_likelihood_new
            
        return node_id_removed, consequence_remaining
        
                
            
        
    def get_results_remove_according_to_weight(self, nodeweight):
        removed_node, remaining_node = self.remove_according_to_weight(nodeweight)
        a = []
        for j in range(len(removed_node)+2):
            a.append(j)
        remaining_node.append(0)
        y = np.array(remaining_node)
        area = int(simps(y, x=np.array(a)))
        
        
        workbook = xlsxwriter.Workbook('Robustness_' + nodeweight+ '.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes consequence")
        worksheet_robustness.write("C1", "Area Under Curve consequence")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(area))
        for i in removed_node:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in remaining_node:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        workbook.close()
    
    def remove_according_to_weight(self, nodeweight):
        node_id_removed = []
        nodes_with_consequence = []
        number_of_nodes_remaining = [len(self._digraph_normal)]
        for node_id, data in self._digraph_normal.nodes(data=True):
            if 'consequence' in data and not isinstance(data['consequence'], str):
                nodes_with_consequence.append((node_id, data['consequence']))
        while len(nodes_with_consequence) != 0:
            sorted_nodes = sorted(nodes_with_consequence, key=lambda x: x[1], reverse=True)
    
            # Extract only the node IDs
            sorted_node_ids = [node[0] for node in sorted_nodes]
                
            node_left = self.active_nodes(self._adjacency_matrix)
            chosen_node = sorted_node_ids[0]
              
            self._matrix.deleteNode([chosen_node])
            node_id_removed.append(chosen_node)
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._digraph_normal = self.get_Digraph()
        
            nodes_with_consequence_new = [t for t in nodes_with_consequence if t[0] in self._digraph_normal.nodes()]
            nodes_with_consequence = nodes_with_consequence_new
            number_of_nodes_remaining.append(len(self._digraph_normal))
        
        print(node_id_removed)
        if len(self._digraph_normal) == 0:
            return node_id_removed, number_of_nodes_remaining
        if len(self._digraph_normal) != 0:
            while len(self._digraph_normal) != 0:
                node_left = self.active_nodes(self._adjacency_matrix)
                if len(node_left) == 0:
                    break
                else:
                    nodeID = int(np.random.choice(node_left, size=1))
                    self._matrix.deleteNode([nodeID])
                    
                    node_id_removed.append(nodeID)
                    self._adjacency_matrix = self._matrix.adjacency_matrix()
                    self._digraph_normal = self.get_Digraph()
                    number_of_nodes_remaining.append(len(self._digraph_normal))
        return node_id_removed, number_of_nodes_remaining
        
                
            
        


    
    def subgraph_count(self):
        
        subgraphs = list(nx.weakly_connected_components(self._digraph_normal))
        num_weakly_connected = len(subgraphs)
        print(f"Number of weakly connected subgraphs: {num_weakly_connected}")
        small_subgraphs = [sg for sg in subgraphs if len(sg) <= 3]
        # Output the total number of such subgraphs
        print(f"Total number of weakly connected subgraphs with 3 or fewer nodes: {len(small_subgraphs)}")

        
    def remove_by_risk_level_consequences_likelihood(self):
        data = pd.read_excel("Compare risk level and metric.xlsx")
        
        
        
        risk_level_area = 100000000
        risk_level_area_high = 0
        risk_level_removed_nodes = []
        risk_level_node_remaining = []
        risk_level_removed_nodes_high = []
        risk_level_node_remaining_high = []
        consequence_area = 100000000
        consequence_area_high = 0
        consequence_removed_nodes = []
        consequence_node_remaining = []
        consequence_removed_nodes_high = []
        consequence_node_remaining_high = []
        likelihood_area = 10000000
        likelihood_area_high = 0
        likelihood_removed_nodes = []
        likelihood_node_remaining = []
        likelihood_removed_nodes_high = []
        likelihood_node_remaining_high = []
         
    
        
        
        ### iterate risk level
        for p in range(0,501):
            risk_level = {"High":[],"Medium":[],"Low":[]}
            for i, j in zip(data['Node ID'], data['Risk']):
                if j == "High":
                    risk_level["High"].append(i) 
                elif j == "Medium":
                    risk_level["Medium"].append(i) 
                elif j == "Low":
                    risk_level["Low"].append(i)
            removed_node, remaining_node = self.random_remove_from_risk_data(risk_level)
            a = []
            for j in range(len(removed_node)+2):
                a.append(j)
            remaining_node.append(0)
            y = np.array(remaining_node)
            area = int(simps(y, x=np.array(a)))
            if area < risk_level_area:
                risk_level_area = area
                risk_level_removed_nodes = removed_node
                risk_level_node_remaining = remaining_node
            if area > risk_level_area_high:
                risk_level_area_high = area
                risk_level_removed_nodes_high = removed_node
                risk_level_node_remaining_high = remaining_node
            self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._digraph_normal = self.get_Digraph()
            print("current: Risk Level Round " + str(p))
        workbook = xlsxwriter.Workbook('Robustness_Risk_Level.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Risk Level")
        worksheet_robustness.write("C1", "Area Under Curve Risk Level")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(risk_level_area))
        for i in risk_level_removed_nodes:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in risk_level_node_remaining:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        workbook.close()
        
        workbook = xlsxwriter.Workbook('Robustness_Risk_Level_High.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes Risk Level")
        worksheet_robustness.write("C1", "Area Under Curve Risk Level")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(risk_level_area_high))
        for i in risk_level_removed_nodes_high:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in risk_level_node_remaining_high:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        workbook.close()
        
        ### iterate consequence ###################################################################
        for p in range(0,501):
            consequence = {5:[],4:[],3:[],2:[],1:[]}
            for k, l in zip(data['Node ID Con'], data['Consequences']):
                if l == 5:
                    consequence[5].append(k) 
                elif l == 4:
                    consequence[4].append(k) 
                elif l == 3:
                    consequence[3].append(k) 
                elif l == 2:
                    consequence[2].append(k) 
                elif l == 1:
                    consequence[1].append(k) 
            removed_node, remaining_node = self.random_remove_from_risk_data(consequence)
            a = []
            for j in range(len(removed_node)+2):
                a.append(j)
            remaining_node.append(0)
            y = np.array(remaining_node)
            area = int(simps(y, x=np.array(a)))
            if area < consequence_area:
                consequence_area = area
                consequence_removed_nodes = removed_node
                consequence_node_remaining = remaining_node
            if area > consequence_area_high:
                consequence_area_high = area
                consequence_removed_nodes_high = removed_node
                consequence_node_remaining_high = remaining_node
            self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._digraph_normal = self.get_Digraph()
            print("current: Consequence Round " + str(p))
        workbook = xlsxwriter.Workbook('Robustness_consequence.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes consequence")
        worksheet_robustness.write("C1", "Area Under Curve consequence")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(consequence_area))
        for i in consequence_removed_nodes:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in consequence_node_remaining:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        workbook.close()
        
        workbook = xlsxwriter.Workbook('Robustness_consequence_high.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes consequence")
        worksheet_robustness.write("C1", "Area Under Curve consequence")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(consequence_area_high))
        for i in consequence_removed_nodes_high:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in consequence_node_remaining_high:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        workbook.close()
        
        
        
        ### iterate likelihood ###############################################################
        for p in range(0,501):
            likelihood = {5:[],4:[],3:[],2:[],1:[]}
            for m, n in zip(data['Node ID Likeli'], data['Likelihood']):
                if n == 5:
                    likelihood[5].append(m) 
                elif n == 4:
                    likelihood[4].append(m) 
                elif n == 3:
                    likelihood[3].append(m) 
                elif n == 2:
                    likelihood[2].append(m) 
                elif n == 1:
                    likelihood[1].append(m)
            removed_node, remaining_node = self.random_remove_from_risk_data(likelihood)
            a = []
            for j in range(len(removed_node)+2):
                a.append(j)
            remaining_node.append(0)
            y = np.array(remaining_node)
            area = int(simps(y, x=np.array(a)))
            if area < likelihood_area:
                likelihood_area = area
                likelihood_removed_nodes = removed_node
                likelihood_node_remaining = remaining_node
            if area > likelihood_area_high:
                likelihood_area_high = area
                likelihood_removed_nodes_high = removed_node
                likelihood_node_remaining_high = remaining_node
            self._matrix = Matrix(self._excel_name, self._node_ID, self._node_weight)
            self._adjacency_matrix = self._matrix.adjacency_matrix()
            self._digraph_normal = self.get_Digraph()
            print("current: Likelihood Round " + str(p))
        workbook = xlsxwriter.Workbook('Robustness_likelihood.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes likelihood")
        worksheet_robustness.write("C1", "Area Under Curve likelihood")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(likelihood_area))
        for i in likelihood_removed_nodes:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in likelihood_node_remaining:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        workbook.close()
        
        workbook = xlsxwriter.Workbook('Robustness_likelihood_high.xlsx')
        worksheet_robustness = workbook.add_worksheet('Robustness')
        worksheet_robustness.write("A1", "No. of Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes likelihood")
        worksheet_robustness.write("C1", "Area Under Curve likelihood")
        row,row2=2,1
        worksheet_robustness.write(1,2, str(likelihood_area_high))
        for i in likelihood_removed_nodes_high:
            worksheet_robustness.write(row,0, str(i))
            row+=1
        for j in likelihood_node_remaining_high:
            worksheet_robustness.write(row2,1, str(j))
            row2+=1
        row = 2
        workbook.close()
        
            
    
    def active_nodes(self,adjacency_matrix):
        n = len(adjacency_matrix)
        active_nodes = []

        for node in range(n):
            has_incoming = any(adjacency_matrix[i][node] for i in range(n))
            has_outgoing = any(adjacency_matrix[node][i] for i in range(n))

            if has_incoming or has_outgoing:
                active_nodes.append(node)

        return active_nodes

    def random_remove_from_risk_data(self, data):
        node_id_removed = []
        number_of_nodes_remaining = [len(self._digraph_normal)]
        for i in data.values():
            ### random pick one node
            while len(i) != 0:
                node_left = self.active_nodes(self._adjacency_matrix)
                chosen_node = random.choice(i)
                if chosen_node not in node_left:
                    i.remove(chosen_node)
                    continue
                if chosen_node in node_left:
                    self._matrix.deleteNode([chosen_node])
                    node_id_removed.append(chosen_node)
                    self._adjacency_matrix = self._matrix.adjacency_matrix()
                    self._digraph_normal = self.get_Digraph()
                    number_of_nodes_remaining.append(len(self._digraph_normal))
                    i.remove(chosen_node)
        if len(self._digraph_normal) == 0:
            return node_id_removed, number_of_nodes_remaining
        if len(self._digraph_normal) != 0:
            while len(self._digraph_normal) != 0:
                node_left = self.active_nodes(self._adjacency_matrix)
                if len(node_left) == 0:
                    break
                else:
                    nodeID = int(np.random.choice(node_left, size=1))
                    self._matrix.deleteNode([nodeID])
                    number_of_nodes_remaining.append(len(self._digraph_normal))
                    node_id_removed.append(nodeID)
                    self._adjacency_matrix = self._matrix.adjacency_matrix()
                    self._digraph_normal = self.get_Digraph()
            return node_id_removed, number_of_nodes_remaining
        
        
    
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
    
    def get_color_new(self,k):
		# Yifei's original colour list
        color_list = ['black','black','black','black','black','black','black','black','black','black','black','black','black']
		
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
        nodes_cannot_be_removed = ['15','6','30','28','23','25','24','31','0','2','3','5','21']
        print(1111111111111111111111111111111111111111111111111)
        metric_remove_method_dic = {"Betweenness": lambda:self.delete_by_Betweenness_remaining(nodes_cannot_be_removed),
                                    "Degree": lambda: self.delete_by_degree_remaining(nodes_cannot_be_removed),
                                    "In Degree": lambda: self.delete_by_In_degree_remaining(nodes_cannot_be_removed),
                                    "Out Degree": lambda: self.delete_by_Out_degree_remaining(nodes_cannot_be_removed),
                                    "Strength": lambda: self.delete_by_Strength_remaining(nodes_cannot_be_removed),
                                    "In Strength": lambda: self.delete_by_In_Strength_remaining(nodes_cannot_be_removed),
                                    "Out Strength": lambda: self.delete_by_Out_Strength_remaining(nodes_cannot_be_removed),
                                    "In Closeness": lambda: self.delete_by_Closeness_remaining(nodes_cannot_be_removed),
                                    "Out Closeness": lambda: self.delete_by_Out_Closeness_remaining(nodes_cannot_be_removed),
                                    "Betweenness Degree":self.delete_by_Betweenness_Degree_remaining,
                                    "Total Combined": lambda: self.start_optimal(nodes_cannot_be_removed)}
        options = ["Degree", "In Degree", "Out Degree", "Strength", "In Strength", "Out Strength", 
                    "In Closeness", "Out Closeness", "Betweenness", "Total Combined"]
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
        fig, axes= plt.subplots(figsize=(15,7))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Betweenness'], color='g',marker="X", markersize=4, markerfacecolor="red", markeredgecolor="black", linewidth=1.5, label='Betweenness: ' + str(int(excel_data['Area Under Curve Betweenness'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Degree'], color='k',linewidth=1.5,  marker="o", markersize=4, markerfacecolor="None", label='Degree: '+ str(int(excel_data['Area Under Curve Degree'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Strength'], color='m',  linewidth=1.5,  marker="D", markersize=4, markerfacecolor="None",label='Strength: '+ str(int(excel_data['Area Under Curve Strength'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Degree'], color='y', linewidth=1.5, marker="s", markersize=4, markerfacecolor="blue", markeredgecolor="yellow", label='In Degree: '+ str(int(excel_data['Area Under Curve In Degree'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Strength'], color='b',linewidth=1.5,  marker="P", markersize=4, markerfacecolor="None", label='In Strength: '+ str(int(excel_data['Area Under Curve In Strength'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes In Closeness'], color='tab:pink',linewidth=1.5,  marker="1", markersize=4, markerfacecolor="None",label='In Closeness: '+ str(int(excel_data['Area Under Curve In Closeness'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Degree'], color='tab:purple', linewidth=1.5, marker=(5,2), markersize=4, markerfacecolor="None",label='Out Degree: '+ str(int(excel_data['Area Under Curve Out Degree'][0])))
        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Strength'], color='c', linewidth=1.5,marker="2", markersize=4, markerfacecolor="None", label='Out Strength: '+ str(int(excel_data['Area Under Curve Out Strength'][0])))

        #plt.plot(excel_data['Number of Removed Nodes'], excel_data['Number of Remaining Nodes Out Closeness'], color='tab:olive',linewidth=1.5,  marker="v", markersize=4, markerfacecolor="None",label='Out Closeness: '+ str(int(excel_data['Area Under Curve Out Closeness'][0])))
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
        plt.xlabel("Number of Removed Nodes",fontsize=12)
        plt.xticks(fontsize = 18)
        plt.yticks(fontsize = 18)
        plt.ylabel("Number of Remaining Nodes",fontsize=12)
        plt.legend(fontsize="small", title = "Metric: Area Under Curve", title_fontsize = 'medium')
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, "Robustness_Total.png")
        plt.savefig(figure_path,dpi=500,bbox_inches='tight')
        print('Finished robustness for all metrics')
        
        
                
        
        
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
        
    
    
    def store_node_weight(self, excel_name, node_id_col, node_weight_col, node_weight_name):
        df = pd.read_excel(excel_name)

        # Check if the specified columns exist in the DataFrame
        if node_id_col not in df.columns or node_weight_col not in df.columns:
            raise ValueError("Specified columns do not exist in the Excel file")

        # Iterate over the rows in the DataFrame
        for index, row in df.iterrows():
            node_id = str(row[node_id_col])
            node_weight = row[node_weight_col]

            # If the node already exists in the graph, update its weight
            # If the node does not exist, add it to the graph with the specified weight
            
            for i in self._digraph_normal:
                print(f"Node ID: {i}, Type: {type(i)}")

            if self._digraph_normal.has_node(node_id):
                print("Startttt")
                self._digraph_normal.nodes[node_id][node_weight_name] =  node_weight
                
                self._digraph_normal_nocolor.nodes[node_id][node_weight_name] = node_weight
            if 'weight' in self._digraph_normal.nodes[node_id]:
                print(f"Node {node_id} has a weight of {self._digraph_normal.nodes[node_id]['weight']}.")
            else:
                print(f"Node {node_id} does not have a weight attribute.")
        
    
    def det_node_weight(self, node_weight_name):
        # Retrieve node weights in a dictionary, skip nodes that do not have a 'weight' attribute or have a weight of 'None'
        node_weights = {node: data[node_weight_name] for node, data in self._digraph_normal.nodes(data=True) if node_weight_name in data and data[node_weight_name] != 'None'}
        print(node_weights)
        return node_weights
    
    def start_optimal_node_weight(self):
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


        
    def start_optimal(self, node_cannot_be_removed):
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
                        if j[1] > count and j[0] not in node_cannot_be_removed:
                            count = j[1]
                            name = j[0]
                elif c >=4:
                    for k in a:
                        if a[k] > count and k not in node_cannot_be_removed:
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
        fig1, sub1 = plt.subplots()
        y=  df['second_column']
        x1 = df['first_column']
        y_1 = df1['second_column']
        x1_1 = df1['first_column']
        sub1.plot(x1, self._number_of_remaining_nodes)
        
        area = int(simps(y, x=np.array(x1)))
        sub1.text(20, 150, 'The area under curve is ' + str(area))
        sub1.set_title('Nodes elimination follows order of Total_Combined')
        sub1.set_xlabel('Number of Removed Nodes')
        sub1.set_ylabel('Number of Remaining Nodes')
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_Total_Combined_Metrics_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        workbook_path = os.path.join(folder_path, 'Robustness_Total_Combined_Metrics_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
        worksheet_robustness = workbook.add_worksheet('Robustness')
       
        
        worksheet_robustness.write("A1", "No. of Removed Nodes")
        worksheet_robustness.write("B1", "Number of Remaining Nodes")
        worksheet_robustness.write("C1", "Area Under Curve")
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
        
        arealist = [area]
        for i in range(len(self._total_node)-1):
            arealist.append(None)
        for j in range(len(self._total_node) - len(number_of_remaining_nodes)):
            number_of_remaining_nodes.append(None)
        d = {"Number of Remaining Nodes Total Combined":number_of_remaining_nodes,"Area Under Curve Total Combined": arealist}
        print(len(number_of_remaining_nodes))
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
            self.plot_ColorMap(nx.closeness_centrality(self._digraph_normal.reverse(), distance = 'weight',wf_improved=False ), 'Out_Closeness')
        elif self.clicked.get() == "Betweenness":
            self.plot_ColorMap(nx.betweenness_centrality(self._digraph_normal),'Betweenness')
        elif self.clicked.get() == "Relative_Likelihood":
            self.plot_ColorMap(self.det_relative_likelihood(), 'Relative_Likelihood')
        elif self.clicked.get() == "Causal_Contribution":
            self.plot_ColorMap(self.det_causal_contribution(), 'Causal_Contribution')
        elif self.clicked.get() == "Node Weight":
            self.plot_ColorMap_2(self.det_node_weight("consequence"), self.det_node_weight("likelihood"), 'Consequence', 'Likelihood')
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
        print(len(G))
        return G
    
    def get_Digraph_Nocolor(self):
        """ Return the directed graph structure from the adjacency matrix"""
        G = nx.DiGraph(directed=True)
        
        #print("[{}] started get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        self._adjacency_matrix = self._matrix.adjacency_matrix()
        for i in range(len(self._adjacency_matrix)):
            for j in range(len(self._adjacency_matrix)):
                weight=int(self._adjacency_matrix[i][j])
                if weight>0:
                    
                    G.add_edge(str(i), str(j),weight=weight)
        
        #print("[{}] finished get_Digraph()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        return G

    def plot_Digraph_initial(self):
        """ Plot the directed graph structure on the canvas"""
        fig = plt.figure(figsize=(6, 6), dpi=200)

        plt.axis('off')
        plt.subplots_adjust(top=1, bottom=0, right=1, left=0,
                            hspace=0, wspace=0)
        pos = nx.nx_agraph.graphviz_layout(self._digraph_normal)
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {'font_size': 5, 'font_color': 'white', 'node_color': 'black', 'node_size': 80,
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
        
    def plot_Digraph_initial_transparent(self,file_name):
        """ Plot the directed graph structure on the canvas"""
        fig = plt.figure(figsize=(6, 6), dpi=300, facecolor='none', edgecolor='none')
    
        plt.axis('off')
        plt.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
        pos = nx.circular_layout(self._digraph_normal)
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {
            'font_size': 3,
            'font_color': 'white',
            'node_color': 'black',
            'node_size': 55,
            'style': 'solid',
            'width': 0.05
        }
        nx.draw_networkx(self._digraph_normal, pos, edge_color=colors, arrows=True, arrowsize=2.5, **options)
        plt.margins(0, 0)
        plt.savefig(f"initial_Digraph {file_name}.png", dpi=300, pad_inches=0, transparent=True)
        print("[{}] Created: initial_Digraph.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        
    def plot_Digraph_initial_transparent(self,file_name):
        """ Plot the directed graph structure on the canvas"""
        fig = plt.figure(figsize=(6, 6), dpi=300, facecolor='none', edgecolor='none')
    
        plt.axis('off')
        plt.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
        pos = nx.circular_layout(self._digraph_normal)
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {
            'font_size': 3,
            'font_color': 'white',
            'node_color': 'black',
            'node_size': 65,
            'style': 'solid',
            'width': 0.15
        }
        nx.draw_networkx(self._digraph_normal, pos, edge_color=colors, arrows=True, arrowsize=2.5, **options)
        plt.margins(0, 0)
        plt.savefig(f"initial_Digraph {file_name}.png", dpi=300, pad_inches=0, transparent=True)
        print("[{}] Created: initial_Digraph.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))

        
    def plot_Digraph_initial_2(self):
        """Plot the directed graph structure on the canvas"""
        # Create a figure without using plt.figure()
        fig = Figure(figsize=(6, 6), dpi=200)
    
        # Add a subplot without using plt directly
        ax = fig.add_subplot(111)
        ax.axis('off')
        fig.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
        # Use the figure and ax objects directly for plotting
        pos = nx.nx_agraph.graphviz_layout(self._digraph_normal)
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {'font_size': 5, 'font_color': 'white', 'node_color': 'black', 'node_size': 80,
                   'style': 'solid', 'width': 0.3, 'arrows': True, 'arrowsize': 2.5,
                   'ax': ax}  # Pass the ax object to draw_networkx
        nx.draw_networkx(self._digraph_normal, pos, edge_color=colors, **options)
        fig.tight_layout(pad=0)
        # Save the figure
        fig.savefig("initial_Digraph.png", dpi=500, pad_inches=0, bbox_inches='tight')
        print("[{}] Created: initial_Digraph.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
    
        # Clear the frame before adding the new canvas
        for widget in self._frame_one.winfo_children():
            widget.destroy()
    
        # Embed the figure into the Tkinter canvas
        canvas = FigureCanvasTkAgg(fig, master=self._frame_one)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.LEFT, fill=tk.BOTH, expand=tk.YES)

    def plot_ColorMap(self, measures, measure_name):
        """ Plot the colormap structure (Degree, In-degree, Out-degree, Betweenness, Closeness) on the canvas"""
        folder_path = 'colormap'
        os.makedirs(folder_path, exist_ok=True)
        
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
        save_path = os.path.join(folder_path, f"{measure_name}.png")
        fig.savefig(save_path,dpi = 500)
        print("[{}] Created: {}".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S"), save_path))
        
        print("[{}] Created: {}".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S"),measure_name + ".png"))
        for widget in self._frame_one.winfo_children():
            widget.destroy()
        canvas = FigureCanvasTkAgg(fig, master=self._frame_one)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.LEFT, fill=None, expand=tk.YES)
        
    def plot_ColorMap_2(self, measures1, measures2, measure_name1, measure_name2):
        # Remove nodes with measure value 0
        measures1 = {node: value for node, value in measures1.items() if value != 0}
        measures2 = {node: value for node, value in measures2.items() if value != 0}

        if not measures1 and not measures2:
            print(f"No measures to plot for {measure_name1} and {measure_name2}.")
            return

        # Setup plot
        fig, ax = plt.subplots(figsize=(6, 6), dpi=200)
        plt.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
        plt.axis('off')
        plt.margins(0, 0)

        # Draw the network with edge colors
        # Assuming self._pos is defined and contains the positions of the nodes
        colors = nx.get_edge_attributes(self._digraph_normal, 'color').values()
        options = {'font_size': 3, 'font_color': 'black', 'node_color': 'gray', 'node_size': 50, 'style': 'solid', 'width': 0.3}
        nx.draw_networkx(self._digraph_normal, self._pos, edge_color=colors, arrows=True, arrowsize=2, **options)

        # Setup colormaps
        cmap1 = plt.get_cmap('coolwarm', 9)
        cmap1.set_under('gray')
        cmap2 = plt.get_cmap('YlGn', 9) # Changed from 'viridis' to 'plasma'
        cmap2.set_under('gray')

        # Get the measure values and define the colormap range for both measures
        raw1 = list(measures1.values())
        vmin1 = min(raw1)
        vmax1 = max(raw1)

        raw2 = list(measures2.values())
        vmin2 = min(raw2)
        vmax2 = max(raw2)

        # Draw the nodes with colormaps
        nodes1 = nx.draw_networkx_nodes(self._digraph_normal, self._pos, node_size=50, cmap=cmap1, node_color=raw1, nodelist=measures1.keys())
        nodes1.set_norm(mcolors.SymLogNorm(linthresh=1, linscale=0.05, vmin=vmin1, vmax=vmax1))

        nodes2 = nx.draw_networkx_nodes(self._digraph_normal, self._pos, node_size=50, cmap=cmap2, node_color=raw2, nodelist=measures2.keys())
        nodes2.set_norm(mcolors.SymLogNorm(linthresh=1, linscale=0.05, vmin=vmin2, vmax=vmax2))

        # Add colorbars, labels, and titles
        cbar1 = plt.colorbar(nodes1, shrink=0.2)
        cbar1.ax.tick_params(labelsize=3)
        cbar1.set_label(measure_name1, size=5)  # Set label for colorbar1

        # Calculate the positions of the ticks for each color in the colormap and set them as integer values
        num_colors = 9
        tick_positions1 = [int(vmin1 + (vmax1 - vmin1) * (i + 0.5) / num_colors) for i in range(num_colors)]
        cbar1.set_ticks(tick_positions1)
        cbar1.set_ticklabels([str(tick) for tick in tick_positions1])

        cbar2 = plt.colorbar(nodes2, shrink=0.2)
        cbar2.ax.tick_params(labelsize=3)
        cbar2.set_label(measure_name2, size=5)  # Set label for colorbar2

        # Calculate the positions of the ticks for each color in the colormap and set them as integer values
        tick_positions2 = [int(vmin2 + (vmax2 - vmin2) * (i + 0.5) / num_colors) for i in range(num_colors)]
        cbar2.set_ticks(tick_positions2)
        cbar2.set_ticklabels([str(tick) for tick in tick_positions2])


        plt.title('Colormap of Two Measures')

        # Save the figure
        plt.savefig(measure_name1 + "_" + measure_name2 + ".png", dpi=1000, bbox_inches='tight')
        print("[{}] Created: {}".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S"), measure_name1 + "_" + measure_name2 + ".png"))

        # Update canvas
        # Assuming self._frame_one is defined and is a tkinter frame
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
    def delete_by_degree_remaining(self, node_cannot_be_removed):
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
                if i[1] > count and i[0] not in node_cannot_be_removed:
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
            print('this node being selected: ' + str(self._deleted_node))
            if len(removed_node) == 0:
                break
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_Degree_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        workbook_path = os.path.join(folder_path, 'Robustness_Degree_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_Degree_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        workbook_path = os.path.join(folder_path, 'Robustness_Degree_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        
    def delete_by_Out_degree_remaining(self, node_cannot_be_removed):
        """ Delete all the nodes by the descending order of value of Out Degree."""
        count = 0
        name = ''
        a = self._digraph_normal.out_degree
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        component = []
        print(a)
        while len(a) != 0:
            print('start')
            print(a)
            for i in a:
                if i[1] > count and i[0] not in node_cannot_be_removed:
                    count = i[1]
                    name = i[0]
            print(name)
            print('?' + str(self._digraph_normal))
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
            print('deleted_node: '+str(self._deleted_node))
            
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_Out_Degree_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_Out_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook_path = os.path.join(folder_path, 'Robustness_Out_Degree_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        
    def delete_by_In_degree_remaining(self, node_cannot_be_removed):
        """ Delete all the nodes by the descending order of value of In Degree."""
        count = 0
        name = ''
        a = self._digraph_normal.in_degree
        component = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        while len(a) != 0:
            for i in a:
                if i[1] > count and i[0] not in node_cannot_be_removed:
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_In_Degree_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_In_Degree_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook_path = os.path.join(folder_path, 'Robustness_In_Degree_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        
        
    def delete_by_Closeness_remaining(self, node_cannot_be_removed):
        """ Delete all the nodes by the descending order of value of In_Closeness."""
        count = -1
        name = ''
        cc = 0
        aa = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        a = nx.closeness_centrality(self._digraph_normal, distance="weight", wf_improved = True)
        component = []
        while len(a) != 0:
            for i in a:
                if a[i] > count and i not in node_cannot_be_removed:
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
            a = nx.closeness_centrality(self._digraph_normal, distance="weight",wf_improved = True)
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_In_Closeness_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_In_Closeness_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook_path = os.path.join(folder_path, 'Robustness_In_Closeness_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        
    def delete_by_Out_Closeness_remaining(self, node_cannot_be_removed):
        """ Delete all the nodes by the descending order of value of Closeness."""
        count = -1
        name = ''
        cc = 0
        aa = []
        original_matrix = copy.deepcopy(self._adjacency_matrix)
        removed_nodes = []
        a = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight", wf_improved = True)
        component = []
        while len(a) != 0:
            for i in a:
                if a[i] > count and i not in node_cannot_be_removed:
                    count = a[i]
                    name = i
            self._deleted_node.append(name)
            self._delete_node.append(int(name))
            self._number_of_remaining_nodes.append(self._digraph_normal.number_of_nodes())
            component = []
            print(self._delete_node)
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
            a = nx.closeness_centrality(self._digraph_normal.reverse(), distance="weight", wf_improved = True)
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_Out_Closeness_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_Out_Closeness_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook_path = os.path.join(folder_path, 'Robustness_Out_Closeness_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        
    def delete_by_Betweenness_remaining(self, node_cannot_be_removed):
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
                if a[i] > count and i not in node_cannot_be_removed:
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_Betweenness_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_Betweenness_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook_path = os.path.join(folder_path, 'Robustness_Betweenness_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        
    def delete_by_Strength_remaining(self, node_cannot_be_removed):
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
                if a[i] > count and i not in node_cannot_be_removed:
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_Strength_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_Strength_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook_path = os.path.join(folder_path, 'Robustness_Strength_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        
    def delete_by_In_Strength_remaining(self, node_cannot_be_removed):
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
                if a[i] > count and i not in node_cannot_be_removed:
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_In_Strength_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_In_Strength_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook_path = os.path.join(folder_path, 'Robustness_In_Strength_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        
    def delete_by_Out_Strength_remaining(self, node_cannot_be_removed):
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
                if a[i] > count and i not in node_cannot_be_removed:
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
        folder_path = 'robustness'
        os.makedirs(folder_path, exist_ok=True)
        figure_path = os.path.join(folder_path, 'Robustness_Out_Strength_Remaining_Nodes.png')
        fig1.savefig(figure_path)
        print("[{}] Created: Robustness_Out_Strength_Remaining_Nodes.png".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
        print("area =", area)
        workbook_path = os.path.join(folder_path, 'Robustness_Out_Strength_Remaining_Nodes.xlsx')
        workbook = xlsxwriter.Workbook(workbook_path)
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
        folder_path = 'distribution'
        os.makedirs(folder_path, exist_ok=True) 
        
        plt.figure(figure_number)
        plt.close()
        
        mean = (np.array(parameter).mean())
        sd = np.array(parameter).std()
        skewness = skew(parameter)

        kurtosis_value = pd.Series(parameter).kurtosis()

        fig, ax1 = plt.subplots(figsize=(8, 6))
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
        save_path = os.path.join(folder_path, f"{title}.png")
        fig.savefig(save_path)
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

        workbook = xlsxwriter.Workbook('Total_results.xlsx')
        worksheet_nodes = workbook.add_worksheet('nodes_ID')
        worksheet_matrix = workbook.add_worksheet('Adjacency_Matrix')
        worksheet_colormap = workbook.add_worksheet('Colormaps')
        
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
        Closeness_In = nx.closeness_centrality(self._digraph_normal,distance="weight", wf_improved = True)
        Closeness_Out = nx.closeness_centrality(self._digraph_normal.reverse(),distance="weight", wf_improved = True)
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
        print(self._node_ID)
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
        worksheet_colormap.insert_image('D30', 'colormap/Degree.png')

        # InDegree
        worksheet_colormap.write('A60', 'In_Degree_Colormap:')
        self.plot_ColorMap(self.get_dict(indegree_1), 'In_Degree')
        worksheet_colormap.insert_image('D60', 'colormap/In_Degree.png')

        # OutDegree
        worksheet_colormap.write('M1', 'Out_Degree_Colormap:')
        self.plot_ColorMap(self.get_dict(outdegree_1), 'Out_Degree')
        worksheet_colormap.insert_image('P1', 'colormap/Out_Degree.png')

        # Eigenvector
        worksheet_colormap.write('M30', 'Eigenvector_Colormap:')
        self.plot_ColorMap(Eigenvector_1, 'Eigenvector')
        worksheet_colormap.insert_image('P30', 'colormap/Eigenvector.png')

        # Betweenness
        worksheet_colormap.write('M60', 'Betweenness_Colormap:')
        self.plot_ColorMap(Betweenness_1, 'Betweenness')
        worksheet_colormap.insert_image('P60', 'colormap/Betweenness.png')

        # In_Closeness
        worksheet_colormap.write('Y1', 'In_Closeness_Colormap:')
        self.plot_ColorMap(Closeness_In, 'In_Closeness')
        worksheet_colormap.insert_image('AA1', 'colormap/In_Closeness.png')
        
        # Out_Closeness
        worksheet_colormap.write('Y30', 'Out_Closeness_Colormap:')
        self.plot_ColorMap(Closeness_Out, 'Out_Closeness')
        worksheet_colormap.insert_image('AA30', 'colormap/Out_Closeness.png')
        
        # Relative Likelihood
        worksheet_colormap.write('Y60', 'Relative Likelihood_Colormap:')
        self.plot_ColorMap(relative_likelihood, 'Relative_Likelihood')
        worksheet_colormap.insert_image('AA60', 'colormap/Relative_Likelihood.png')
        
        # Causal Contribution
        worksheet_colormap.write('AJ1', 'Causal Contribution_Colormap:')
        self.plot_ColorMap(causal_contribution, 'Causal_Contribution')
        worksheet_colormap.insert_image('AN1', 'colormap/Causal_Contribution.png')
        
        # Strength
        worksheet_colormap.write('AJ30', 'Strength_Colormap:')
        self.plot_ColorMap(strength_1, 'Strength')
        worksheet_colormap.insert_image('AN30', 'colormap/Strength.png')
        
        # In_strength
        worksheet_colormap.write('AJ60', 'In_Strength_Colormap:')
        self.plot_ColorMap(instrength_1, 'In_Strength')
        worksheet_colormap.insert_image('AN60', 'colormap/In_Strength.png')
        
        # Out_strength
        worksheet_colormap.write('AJ90', 'Out_Strength_Colormap:')
        self.plot_ColorMap(outstrength_1, 'Out_Strength')
        worksheet_colormap.insert_image('AN90', 'colormap/Out_Strength.png')

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
        worksheet_distribution.insert_image('D1', 'distribution/Degree_Distribution.png')

        # Indegree
        worksheet_distribution.write('A30', 'In_Degree_Distribution')
        self.plot_distribution(Indegree, 2, "In_Degree_Distribution")
        worksheet_distribution.insert_image('D30', 'distribution/In_Degree_Distribution.png')

        # Outdegree
        worksheet_distribution.write('A60', 'Out_Degree_Distribution')
        self.plot_distribution(Outdegree, 3, "Out_Degree_Distribution")
        worksheet_distribution.insert_image('D60', 'distribution/Out_Degree_Distribution.png')

        # Eigenvector
        worksheet_distribution.write('P1', 'Eigenvector_Distribution')
        self.plot_distribution(self.det_eigenvector_one(Eigenvector_Centrality_values), 4, "Eigenvector_Distribution")
        worksheet_distribution.insert_image('S1', 'distribution/Eigenvector_Distribution.png')

        # Betweenness
        worksheet_distribution.write('P30', 'Betweenness_Distribution')
        self.plot_distribution(self.det_betweenness_one(betweenness_values), 5, "Betweenness_Distribution")
        worksheet_distribution.insert_image('S30', 'distribution/Betweenness_Distribution.png')

        # In_Closeness
        worksheet_distribution.write('P60', 'In_Closeness_Distribution')
        self.plot_distribution(self.det_in_closeness_one(In_closeness_centrality_values), 6, "In_Closeness_Distribution")
        worksheet_distribution.insert_image('S60', 'distribution/In_Closeness_Distribution.png')
        
        # Out_Closeness
        worksheet_distribution.write('P90', 'Out_Closeness_Distribution')
        self.plot_distribution(self.det_out_closeness_one(Out_closeness_centrality_values), 7, "Out_Closeness_Distribution")
        worksheet_distribution.insert_image('S90', 'distribution/Out_Closeness_Distribution.png')
        
        # Strength
        worksheet_distribution.write('AE1', 'Strength_Distribution')
        for i in strength_1.values():
            strength_list.append(i)
        self.plot_distribution(strength_list, 8, "Strength_Distribution")
        worksheet_distribution.insert_image('AH1', 'distribution/Strength_Distribution.png')
        # In Strength
        worksheet_distribution.write('AE30', 'In_Strength_Distribution')
        for i in instrength_1.values():
            instrength_list.append(i)
        self.plot_distribution(instrength_list, 9, "In_Strength_Distribution")
        worksheet_distribution.insert_image('AH30', 'distribution/In_Strength_Distribution.png')
        
        # Out Strength
        worksheet_distribution.write('AE60', 'Out_Strength_Distribution')
        for i in outstrength_1.values():
            outstrength_list.append(i)
        self.plot_distribution(outstrength_list, 10, "Out_Strength_Distribution")
        worksheet_distribution.insert_image('AH60', 'distribution/Out_Strength_Distribution.png')
        
        # Relative likelihood
        worksheet_distribution.write('AE90', 'Relative_Likelihood_Distribution')
        for i in range(len(relative_likelihood)):
            relative_likelihood_list.append(relative_likelihood.get(str(i)))
        self.plot_distribution(relative_likelihood_list, 11, 'Relative_Likelihood_Distribution')
        worksheet_distribution.insert_image('AH90', 'distribution/Relative_Likelihood_Distribution.png')
        # Causal Contribution
        worksheet_distribution.write('AE120', 'Caucal_Contribution_Distribution')
        for i in range(len(Causal_Contribution)):
            Causal_Contribution_list.append(Causal_Contribution.get(str(i)))
        self.plot_distribution(Causal_Contribution_list, 12, 'Causal_Contribution_Distribution')
        worksheet_distribution.insert_image('AH120', 'distribution/Causal_Contribution_Distribution.png')

        workbook.close()
        print('Finished_getting_all_results')
        
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
        print(self._digraph_normal.out_degree)
        
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
      
        
        self._digraph_normal = new_graph
        self._digraph_normal_nocolor = new_graph
        subgraph_node_meanings = {meaning: nodeID for meaning, nodeID in self._node_ID.items() if str(nodeID) in self._digraph_normal.nodes}
        self._node_ID = subgraph_node_meanings
        
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
        
        

    def get_causal_consequence_subgraph(self):
        """Extract all the pathways (directed) from all zero in-degree nodes to all zero out-degree nodes."""
        
        # Identifying source nodes (zero in-degree)
        source_nodes = [node for node in self._digraph_normal.nodes() if self._digraph_normal.in_degree(node) == 0]
    
        # Identifying sink nodes (zero out-degree)
        sink_nodes = [node for node in self._digraph_normal.nodes() if self._digraph_normal.out_degree(node) == 0]
    
        # Find all paths from source nodes to sink nodes
        all_paths = []
        paths_info = []  # To store tuple of (source, sink, path)
        for source in source_nodes:
            for sink in sink_nodes:
                paths = list(nx.all_simple_paths(self._digraph_normal, source=source, target=sink))
                for path in paths:
                    all_paths.append(path)
                    path_str = ' -> '.join(map(str, path))  # Convert path list to a string for easy reading
                    paths_info.append((source, sink, path_str))
    
        # Open a workbook and add a worksheet
        workbook = xlsxwriter.Workbook('all_causal_pathway.xlsx')
        worksheet = workbook.add_worksheet('Paths Info')
    
        # Add headers
        worksheet.write(0, 0, 'Source')
        worksheet.write(0, 1, 'Sink')
        worksheet.write(0, 2, 'Path')
    
        # Write data to worksheet
        for row_num, (source, sink, path_str) in enumerate(paths_info, start=1):
            worksheet.write(row_num, 0, str(source))
            worksheet.write(row_num, 1, str(sink))
            worksheet.write(row_num, 2, path_str)
    
        workbook.close()
        print('Excel file saved with paths information.')

if __name__ == "__main__":
    ##plot initial digraph
    root = tk.Tk()
    root.geometry("1600x1600")
    digraphPlot(root)
    root.update()
    print("[{}] finished root update()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))
    root.mainloop()
    print("[{}] finished root mainloop()".format(datetime.now().strftime("%d-%m-%Y %H:%M:%S")))