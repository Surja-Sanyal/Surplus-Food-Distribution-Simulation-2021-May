#Program:   Surplus Food Redistribution Simulations
#Inputs:    TBD
#Outputs:   TBD
#Author:    Surja Sanyal
#Date:      29 DEC 2020
#Comments:  None




##   Start of Code   ##


#   Imports    #

import os
import re
import sys
import math
import copy
import time
import psutil
import shutil
import random
import resource
import datetime
import traceback
import itertools
import numpy as np
import multiprocessing
from textwrap import wrap
from functools import partial
import matplotlib.pyplot as plt
from scipy.stats import truncnorm




##  Global environment   ##

#   Customize here  #
AGENTS					= 5000					#Number								Default number of agent requests
PAYLOAD_MAX				= 100					#Number								Volunteer payload limit in kilograms
COORDINATE_MAX       	= 50					#Number								City start (at 0) to end limit in kilometers
DAY_MAX			      	= 18					#Number								Day start (at 0) to end limit in hours
SAVE					= "OFF"					#ON/OFF								Save data
SORTING					= "END"					#START/END							Receiver sorting
PREFERENCE				= "ELIGIBLE"			#ORIGINAL/ELIGIBLE/UPDATED			Usage of preference lists
VOLUNTEERS				= "1X"					#1X/2X/4X/8X/16X/32X				Volunteer availability (1/2/4/8/16/32) times donors
MANIPULATION			= "ON"					#ON/OFF								Manipulation of preferences

#	Thresholds	#
To		= 0.25									#Overlap time (hours)
Tl		= 5										#Off-routing (percentage)
Tm		= 1										#Meal size  (kilograms)
Ta		= 20									#Extra payload (percentage)
Tpm		= 5000									#Default perishable food travel distance (kilometers)
Tpnm	= 1000									#Default perishable food travel distance (kilometers)
Tnp		= 10000									#Default non-perishable food travel distance (kilometers)
Td		= 2										#Process advance start threshold for donors (hours)
Tr		= 3										#Process advance start threshold for receivers (hours)
Tw		= 10									#Match acceptance window (minutes)

#   Do not change   #
LOCK                = multiprocessing.Lock()								#Multiprocessing lock
CPU_COUNT           = multiprocessing.cpu_count()							#Logical CPUs
MEMORY              = math.ceil(psutil.virtual_memory().total/(1024.**3))	#RAM capacity
DATA_LOAD_LOCATION	= os.path.dirname(sys.argv[0]) + "/Statistics/"			#Data load location
DATA_STORE_LOCATION	= os.path.dirname(sys.argv[0]) + "/Graphs/"				#Data store location




##  Function definitions    ##


#   Print with lock    #
def print_locked(*content, sep=" ", end="\n"):

    store = DATA_LOAD_LOCATION
    
    with open(store + "_Log_File.txt", "a") as log_file:
    
        try:
        
            with lock:
            
                print (*content, sep = sep, end = end)
                print (*content, sep = sep, end = end, file=log_file)

        except Exception:
        
            with LOCK:
            
                print (*content, sep = sep, end = end)
                print (*content, sep = sep, end = end, file=log_file)


#   Convert string to int or float    #
def convert(some_value):

    try:
        return int(some_value)
        
    except ValueError:
    
        try:
        
            return float(some_value)
        
        except ValueError:
        
            print_locked(traceback.format_exc())


#   Display execution data in a graph   #
def display_bar_graph(file_name, fig_name, purpose):

	load, store = DATA_LOAD_LOCATION, DATA_STORE_LOCATION
	volunteer, data, y_axis = [], [], []
    
    #   Read data   #
	with open(load + file_name + ".txt", "r") as fp:
        
		for line in fp:
        
			pieces = [convert(stat) for stat in line.strip().split()]
			data.append(pieces)
	
	for each_entry in data:
    
		volunteer.append(each_entry[0])
		
		y_axis.append(each_entry[1:])
    
	y_axis = list(zip(*y_axis))
	
    #   Create the figure   #
	comparision = plt.figure(fig_name)
	
	if purpose == 'SORTING':
    
		labels = ['START', 'END']
		ax = plt.subplot(111, ylim=(0, 100))
    
	elif purpose == 'PREFERENCES':
    
		labels = ['ORIGINAL', 'ELIGIBLE']
		ax = plt.subplot(111, ylim=(0, 100))
    
	elif purpose == 'MANIPULATION':
    
		labels = ['GAIN', 'LOSS', 'SAME', 'NONE']
		ax = plt.subplot(111, ylim=(0, 120))
	
	width = 40
	bars = []
	colors = ['b', 'g', 'r', 'y']
	
	for row in range(len(y_axis)):
	
		bars.append(ax.bar([200 * math.log2(each) - int(len(y_axis)/2) * width + row * width for each in volunteer], y_axis[row], width=width, color=colors[row], align='center'))
	
	ax.set_xticks([200 * math.log2(each) - width/2 for each in volunteer])
	ax.set_xticklabels([tick for tick in volunteer])
	ax.set_yticks([0, 20, 40, 60, 80, 100])
	ax.set_yticklabels(['0', '20', '40', '60', '80', '100'])
	
	if purpose == 'SORTING':
    
		ax.legend(bars, labels, loc='upper left', title='Agent Chronological Sort')
    
	elif purpose == 'PREFERENCES':
    
		ax.legend(bars, labels, loc='upper left', title='Preference Selection')
    
	elif purpose == 'MANIPULATION':
    
		ax.legend(bars, labels, loc='upper center', title='Preference Manipulation')
    
	#   Customize plot   #
	[autolabel(bars[row], ax) for row in range(len(bars))]
	
	plt.ylabel('Allocated Agents ( % ) -->\n')
	plt.xlabel('\nVolunteer Availability ( × Donors ) -->')
	plt.tight_layout(pad=1.0, w_pad=1.0, h_pad=1.0)
    
	comparision.savefig(store + fig_name + ".pdf", bbox_inches='tight')
	comparision.savefig(store + fig_name + ".jpg", bbox_inches='tight')


#	Heights of bars	#
def autolabel(rects, ax):

	for rect in rects:
    
		h = rect.get_height()
		ax.text(rect.get_x()+rect.get_width()/2., 1.05*h, '%.2f'%float(h) + " %", ha='center', va='bottom', rotation='vertical')


#   Display execution data in a graph   #
def display_line_graph(file_name, fig_name):

	load, store = DATA_LOAD_LOCATION, DATA_STORE_LOCATION
	volunteer, data, y_axis = [], [], []
    
    #   Read data   #
	with open(load + file_name + ".txt", "r") as fp:
        
		for line in fp:
        
			pieces = [convert(stat) for stat in line.strip().split()]
			data.append(pieces)
	
	for each_entry in data:
    
		volunteer.append(each_entry[0])
		
		y_axis.append(each_entry[1:])
    
	#   Create the figure   #
	comparision = plt.figure(fig_name)
	ax = plt.subplot(111, xlim=(0, 40), ylim=(0, 85))
	label = 'ALLOCATION ( % )'
	
	plot = ax.plot(volunteer, y_axis, label=label, color='g', marker='o')
    
	#   Customize plot   #
	ax.set_xticks(volunteer)
	ax.set_xticklabels([tick for tick in volunteer])
	ax.set_yticks([0, 20, 40, 60, 80])
	ax.set_yticklabels(['0', '20', '40', '60', '80'])
	
	plt.ylabel('Allocated Agents ( % ) -->\n')
	plt.xlabel('\nVolunteer Availability ( × Donors ) -->')
	
	ax.legend(loc='lower right', title='Agent Allocation vs Volunteer Availability')
	
	y_axis = [element[0] for element in y_axis]
	
	for x, y in zip(volunteer, y_axis):
	
		plt.text(x + 1, y - 3, str(y) + " %")

    
	comparision.savefig(store + fig_name + ".pdf", bbox_inches='tight')
	comparision.savefig(store + fig_name + ".jpg", bbox_inches='tight')



##  The main function   ##

#   Main    #
def main():

	data_sources = [['StartVSEnd', 'Start vs End Sorting for Receivers', 'SORTING'], ['OriginalVSEligible', 'Original vs Eligible Preferences for Agents', 'PREFERENCES'], ['Manipulation', 'Manipulation of Preferences by Agents', 'MANIPULATION'], ['ExecutionCurve', 'Allocation vs Volunteer Availability']]
	
	[display_bar_graph(stat[0], stat[1], stat[2]) for stat in data_sources[:-1]]
	
	display_line_graph(data_sources[-1][0], data_sources[-1][1])



##  Call the main function  ##

#   Initiation  #
if __name__=="__main__":

    try:
    
        #   Start logging to file     #        
        print_locked('\n\n\n\n{:.{align}{width}}'.format("Execution Start at: " 
            + str(datetime.datetime.now()), align='<', width=70), end="\n\n")
        
        print_locked("\n\nProgram Name:\n\n" + str(sys.argv[0].split("/")[-1]))
        
        print_locked("\n\nProgram Path:\n\n" + os.path.dirname(sys.argv[0]))
        
        print_locked("\n\nProgram Name With Path:\n\n" + str(sys.argv[0]), end="\n\n\n")
        
        #   Clear the terminal  #
        os.system("clear")
        
        #   Initiate lock object    #
        lock = multiprocessing.Lock()

        #   Initiate pool objects   #
        pool = multiprocessing.Pool(multiprocessing.cpu_count())
        
        #   Call the main program   #
        start = datetime.datetime.now()
        main()
        print_locked("\nProgram execution time:\t\t", datetime.datetime.now() - start, "hours\n")
        
        #   Close Pool object    #
        pool.close()

    except Exception:
    
        print_locked(traceback.format_exc())


##   End of Code   ##

