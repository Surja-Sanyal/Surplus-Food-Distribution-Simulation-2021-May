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
VOLUNTEERS				= "32X"					#1X/2X/4X/8X/16X/32X				Volunteer availability (1/2/4/8/16/32) times donors
MANIPULATION			= "ON"					#ON/OFF								Manipulation of preferences

#	Thresholds	#
To		= 0.25									#Overlap time (hours)
Tl		= 5										#Off-routing (percentage)
Tm		= 1										#Meal size  (kilograms)
Ta		= 20									#Extra payload (percentage)
Tpm		= 20									#Default perishable food travel distance (kilometers)
Tpnm	= 5										#Default perishable food travel distance (kilometers)
Tnp		= 100									#Default non-perishable food travel distance (kilometers)
Td		= 2										#Process advance start threshold for donors (hours)
Tr		= 3										#Process advance start threshold for receivers (hours)
Tw		= 10									#Match acceptance window (minutes)

#   Do not change   #
LOCK                = multiprocessing.Lock()								#Multiprocessing lock
CPU_COUNT           = multiprocessing.cpu_count()							#Logical CPUs
MEMORY              = math.ceil(psutil.virtual_memory().total/(1024.**3))	#RAM capacity
DATA_LOAD_LOCATION	= os.path.dirname(sys.argv[0]) + "/"					#Data load location
DATA_STORE_LOCATION	= os.path.dirname(sys.argv[0]) + "/"					#Data store location




##  Function definitions    ##


#   Print with lock    #
def print_locked(*content, sep=" ", end="\n"):

    store = DATA_STORE_LOCATION
    
    with open(store + "_Log_File.txt", "a") as log_file:
    
        try:
        
            with lock:
            
                print (*content, sep = sep, end = end)
                print (*content, sep = sep, end = end, file=log_file)

        except Exception:
        
            with LOCK:
            
                print (*content, sep = sep, end = end)
                print (*content, sep = sep, end = end, file=log_file)


#   Load data option    #
def get_agent_generation_options():

    print_locked("\nDo you want to generate fresh agent data (y/n)?: ", end="")
    agent_auto_generate = input()
    
    if agent_auto_generate.upper() != 'Y':
    
    	print_locked("\nPrevious data will be used.")
    
    else:
    
    	agent_auto_generate = 'Y'
    	print_locked("\nPrevious data will not be used. Fresh data will be generated.")
    
    return agent_auto_generate


#   Get number of agent requests    #
def get_num_requests():

    print_locked("\nHow many agent requests do you want to create?: ", end="")
    num_requests = input()

    try:
        num_requests = int(num_requests)
        print_locked("\nAgent request generation number:", num_requests)
    
    except Exception:
    
        num_requests = AGENTS
        print_locked("\nAgent request generation number defaulted to:", num_requests)

    return num_requests


#	Define agent class	#
class Agent:

	def __init__(self, agentid, agenttype, ftype, amount, startx, starty, startt, endt, 
						pref, endx = -1, endy = -1, transtype = '', transac = ''):
		self.agentid	= agentid		#Agent identifier
		self.agenttype	= agenttype		#Agent type
		self.ftype		= ftype			#Food type
		self.amount		= amount		#Amount/Payload
		self.transtype	= transtype		#Transportation type
		self.transac	= transac		#Transportation AC status
		self.startx		= startx		#Location start x-coordinate
		self.starty		= starty		#Location start y-coordinate
		self.endx		= endx			#Location end x-coordinate
		self.endy		= endy			#Location end y-coordinate
		self.startt		= startt		#Availability start time
		self.endt		= endt			#Availability end time
		self.pref		= pref			#Preference list
		self.m_pref		= pref			#Updated preference list
		self.vicinity	= -1			#Neighbourhood radius

	def get_details(self):
	
		return [self.agentid, self.agenttype, self.ftype, self.amount, self.startx, self.starty, \
				self.startt, self.endt, self.pref, self.endx, self.endy, self.transtype, \
				self.transac]


#	Save agent requests	#
def save_agent_requests(C):

	store = DATA_STORE_LOCATION

    #   Write data  #
	with open(store + "_agent_requests.txt", "w") as fp:
        
		[fp.write(str(agent.get_details()) + "\n") for agent in C]


#	Save matches	#
def save_matches(matches):

	store = DATA_STORE_LOCATION

    #   Write data  #
	with open(store + "_matched_requests.txt", "w") as fp:
        
		[fp.write(str(the_tuple) + "\n") for the_tuple in matches]


#	Generate agent requests	#
def generate_and_classify_agents(num_requests):

	C, PFD, PFR, NPFD, NPFR, V = [], [], [], [], [], []
	city_limits, working_hour_limits, max_payload = COORDINATE_MAX, DAY_MAX, PAYLOAD_MAX
	
	for i in range(num_requests):
	
		#	Generate agent attributes	#
		agentid			= i
		agenttype		= random.choices(('D', 'R', 'V'), weights = (2, 2, get_v_settings('32X')))[0]
		startx			= random.choice(range(city_limits + 1))
		starty			= random.choice(range(city_limits + 1))
		startt			= random.choice(range(working_hour_limits))
		endt			= random.choice(range(startt, working_hour_limits + 1))
		
		if agenttype == "V":

			endx		= random.choice(range(city_limits + 1))
			endy		= random.choice(range(city_limits + 1))
			transac		= random.choice(('AC', ''))
			transtype	= random.choice(('MOTORED', ''))
			amount		= random.choice(range(1, max_payload + 1))
			ftype		= ''
			pref		= random.sample(range(num_requests), random.choices(range(0, num_requests), weights = [i + 1 for i in range(num_requests)])[0])
		
		elif agenttype == "R":
		
			endx		= -1
			endy		= -1
			transac		= ''
			transtype	= ''
			ftype		= random.choice(('P', 'NP'))
			amount		= Tm
			pref		= random.sample(range(num_requests), random.choices(range(0, num_requests), weights = [0.9999 ** (i + 1) for i in range(num_requests)])[0])
		
		else:
		
			endx		= -1
			endy		= -1
			transac		= ''
			transtype	= ''
			ftype		= random.choice(('P', 'NP'))
			amount		= Tm
			pref			= random.sample(range(num_requests), random.choices(range(0, num_requests), weights = [0.9 ** (i + 1) for i in range(num_requests)])[0])
		
		
		#	Create agent request	#
		C.append(Agent(agentid, agenttype, ftype, amount, startx, starty, startt, endt, pref, endx, endy, transtype, transac))
		
		#	Add to list	#
		if agenttype == 'V':
		
			V.append(agentid)
		
		elif agenttype == 'D':
		
			if ftype == 'P':
		
				PFD.append(agentid)
			
			else:
			
				NPFD.append(agentid)
		
		else:
		
			if ftype == 'P':
		
				PFR.append(agentid)
			
			else:
			
				NPFR.append(agentid)
	
	#	Save agent requests	#
	if SAVE == 'ON':
	
		multiprocessing.Process(target=save_agent_requests, args=(C, )).start()
	
	#	Return agent requests	#
	return C, PFD, PFR, NPFD, NPFR, V


#	Read matches	#
def get_matches():

	matches = []
	load = DATA_LOAD_LOCATION
	
	#   Read agent matches    #
	with open(load + "_matched_requests.txt", "r") as fp:
    
		for line in fp:
		
			line = line[1:-2]
			parts = [convert(piece) for piece in re.split(", ", line)]
			
			if len(parts) > 2:
			
				matches.append((parts[0], parts[1], parts[2]))
			
			else:
			
				matches.append((parts[0], parts[1]))
	
	return matches


#	Read requests and classify into lists	#
def read_and_classify_agents():

	C, PFD, PFR, NPFD, NPFR, V = [], [], [], [], [], []
	load = DATA_LOAD_LOCATION
	
	#   Read agent requests    #
	with open(load + "_agent_requests.txt", "r") as fp:
    
		for line in fp:
		
			line = line[1:-2]
			parts = [piece for piece in re.split("\]|\[", line)]
			
			part_1 = [convert(piece) for piece in re.split(", ", parts[0])]
			part_2 = [convert(piece) for piece in re.split(", ", parts[-1])]
			
			part_1 = [piece for piece in part_1 if piece is not None]
			part_2 = [piece for piece in part_2 if piece is not None]
			
			if len(parts) == 2:
			
				pref   = []
			
			else:
			
				pref   = convert(parts[1])
				
				if type(pref) is not list:
				
					pref = [pref]
			
			C.append(Agent(part_1[0], part_1[1], part_1[2], part_1[3], part_1[4], part_1[5], part_1[6], part_1[7], 
							pref, 
							part_2[1], part_2[2], part_2[3]))
			
			if part_1[1] == 'V':
			
				V.append(part_1[0])
			
			elif part_1[1] == 'D':
			
				if part_1[2] == 'P':
			
					PFD.append(part_1[0])
				
				else:
				
					NPFD.append(part_1[0])
			
			else:
			
				if part_1[2] == 'P':
			
					PFR.append(part_1[0])
				
				else:
				
					NPFR.append(part_1[0])
	
	return C, PFD, PFR, NPFD, NPFR, V


#   Convert read values to int, str or list    #
def convert(some_value):

	try:
    
		return int(some_value)
        
	except ValueError:
	
		if ',' not in some_value:
    	
			return some_value[1:-1]
		
		else:
    	
			return [int(element) for element in re.split("\[|, |\]", some_value)]


#	Get volunteer availability settings	#
def get_v_settings(setting):

	if setting == '1X':
	
		return 2
	
	elif setting == '2X':
	
		return 4
	
	elif setting == '4X':
	
		return 8
	
	elif setting == '8X':
	
		return 16
	
	elif setting == '16X':
	
		return 32
	
	elif setting == '32X':
	
		return 64


#	Get agent with matching agentid	#
def get_agent(C, request_id):

	corresponding_agent = [agent for agent in C if agent.agentid == request_id]
	
	return corresponding_agent[0]


#	Assign volunteer, update preference and match requests	#
def match_requests(C, D, R, V, Food):

	M = []
	
	#	Match volunteers	#
	for donor in D:
	
		donor_agent = get_agent(C, donor)
		v_prime = []
		
		for volunteer in V:
		
			volunteer_agent = get_agent(C, volunteer)
			
			if ((volunteer_agent.amount >= (1 + Ta/100) * donor_agent.amount)
				and (math.sqrt((donor_agent.startx - volunteer_agent.startx) ** 2 + (donor_agent.starty - volunteer_agent.starty) ** 2) <= (Tl/100) * math.sqrt((volunteer_agent.startx - volunteer_agent.endx) ** 2 + (volunteer_agent.starty - volunteer_agent.endy) ** 2))
				and (donor_agent.startt < volunteer_agent.endt and volunteer_agent.startt < donor_agent.endt and (volunteer_agent.endt - donor_agent.startt >= To or donor_agent.endt - volunteer_agent.startt >= To))
				and (donor_agent.agentid in volunteer_agent.m_pref or len(volunteer_agent.m_pref) == 0)):
			
				v_prime.append(volunteer)
		
		if len(v_prime) == 0:
		
			if Food == 'P':
			
				vicinity = Tpnm
			
			else:
			
				vicinity = Tnp
		
		else:
		
			for volunteer in v_prime:
			
				volunteer_agent = get_agent(C, volunteer)
				
				if Food != 'P':
				
					vicinity = int(math.sqrt((volunteer_agent.startx - volunteer_agent.endx) ** 2 
											+ (volunteer_agent.starty - volunteer_agent.endy) ** 2))
				
				else:
				
					if volunteer_agent.transac == 'AC':
					
						vicinity = int(math.sqrt((volunteer_agent.startx - volunteer_agent.endx) ** 2 
											+ (volunteer_agent.starty - volunteer_agent.endy) ** 2))
					
					else:
					
						if volunteer_agent.transtype == 'MOTORED':
						
							vicinity = Tpm
						
						else:
						
							vicinity = Tpnm
				
				if vicinity > donor_agent.vicinity:
				
					donor_agent.vicinity = vicinity
					match_index = [i for i, match in enumerate(M) if match[0] == donor_agent.agentid]
					
					if len(match_index) > 0:
					
						M[match_index[0]] = (donor_agent.agentid, volunteer_agent.agentid)
					
					else:
					
						M.append((donor_agent.agentid, volunteer_agent.agentid))
	
		try:
		
			match_index = [i for i, match in enumerate(M) if match[0] == donor_agent.agentid]
			matched_volunteer_agent = get_agent(C, M[match_index[0]][1])
			
			if matched_volunteer_agent.amount < 2 * Tm:
			
				V.remove(M[match_index[0]][1])
			
			else:
			
				matched_volunteer_agent.amount = matched_volunteer_agent.amount - Tm
		
		except Exception:
		
			pass
	
	
	#	Match receivers	#
	#	Update receiver preferences#
	preference_settings = PREFERENCE
	receiver_sort_settings = SORTING
	
	for receiver in R:
	
		receiver_agent = get_agent(C, receiver)		
		original_pref = receiver_agent.m_pref
		eligibility = []
		
		for donor in D:
		
			donor_agent = get_agent(C, donor)
			d_to_r_distance = math.sqrt((donor_agent.startx - receiver_agent.startx) ** 2 + (donor_agent.starty - receiver_agent.starty) ** 2)
			
			if d_to_r_distance <= donor_agent.vicinity:
			
				if ((receiver_sort_settings == 'START' and donor_agent.endt < receiver_agent.startt)
					or (receiver_sort_settings == 'END' and donor_agent.endt < receiver_agent.endt)):
			
					eligibility.append(donor_agent.agentid)
		
		eligible_not_preferred = [agent for agent in eligibility if agent not in original_pref]
		eligible_not_preferred.sort(key=lambda x: (get_agent(C, x).startt, x))
		
		if preference_settings == 'ORIGINAL':
		
			receiver_agent.m_pref = [agent for agent in original_pref if agent in eligibility]
		
		elif preference_settings in ['ELIGIBLE', 'UPDATED']:
		
			receiver_agent.m_pref = [agent for agent in original_pref if agent in eligibility] + eligible_not_preferred
		
	#	Update donor preferences#
	for donor in D:
	
		donor_agent = get_agent(C, donor)
		original_pref = donor_agent.m_pref
		volunteer = [the_tuple[1] for the_tuple in M if (the_tuple[0] == donor)]
		
		if len(volunteer) != 0:
		
			volunteer_agent = get_agent(C, volunteer[0])
			v_s_to_e_distance = math.sqrt((volunteer_agent.startx - volunteer_agent.endx) ** 2 + (volunteer_agent.starty - volunteer_agent.endy) ** 2)
		
		else:
		
			v_s_to_e_distance = 0
		
		neighbourhood = []
		
		for receiver in R:
		
			receiver_agent = get_agent(C, receiver)
			d_to_r_distance = math.sqrt((donor_agent.startx - receiver_agent.startx) ** 2 + (donor_agent.starty - receiver_agent.starty) ** 2)
			
			if len(volunteer) != 0:
			
				twice_triangle_area = abs((volunteer_agent.startx - volunteer_agent.endx) * (volunteer_agent.endy - receiver_agent.endy) - (volunteer_agent.starty - volunteer_agent.endy) * (volunteer_agent.endx - receiver_agent.endx))
				off_routing_distance = twice_triangle_area/v_s_to_e_distance
			
			else:
			
				off_routing_distance = -1
			
			if (d_to_r_distance <= donor_agent.vicinity and (off_routing_distance <= (Tl/100) * v_s_to_e_distance)):
				
				if ((receiver_sort_settings == 'START' and donor_agent.endt < receiver_agent.startt)
					or (receiver_sort_settings == 'END' and donor_agent.endt < receiver_agent.endt)):
				
					neighbourhood.append(receiver_agent.agentid)
		
		neighbour_not_preferred = [agent for agent in neighbourhood if agent not in original_pref]
		
		if receiver_sort_settings == 'START':
		
			neighbour_not_preferred.sort(key=lambda x: (get_agent(C, x).startt, x))
		
		else:
		
			neighbour_not_preferred.sort(key=lambda x: (get_agent(C, x).endt, x))
		
		if preference_settings == 'ORIGINAL':
		
			receiver_agent.m_pref = [agent for agent in original_pref if agent in neighbourhood]
		
		elif preference_settings in ['ELIGIBLE', 'UPDATED']:
		
			receiver_agent.m_pref = [agent for agent in original_pref if agent in neighbourhood] + neighbour_not_preferred
	
	
	#	Receiver sorting #
	if receiver_sort_settings == 'START':
	
		R.sort(key=lambda x: (get_agent(C, x).startt, x))
	
	else:
	
		R.sort(key=lambda x: (get_agent(C, x).endt, x))
	
	#	Match donor and receivers	#
	for receiver in R:
	
		receiver_agent = get_agent(C, receiver)
		receiver_pref = [agent for agent in receiver_agent.m_pref if agent in D]
		match_donor_position = -1
		best_preference = -1
		
		for i, donor in enumerate(receiver_pref):
		
			donor_agent = get_agent(C, donor)
			
			try:
			
				current_position = donor_agent.m_pref.index(receiver)
				
				if (current_position < best_preference or match_donor_position < 0):
				
					match_donor_position = i
					best_preference = current_position
			
			except Exception:
			
				pass
		
		try:
		
			match_index = [i for i, match in enumerate(M) if match[0] == receiver_pref[match_donor_position]]
			match_tuples = [match for i, match in enumerate(M) if match[0] == receiver_pref[match_donor_position]]
			M[match_index[0]] = (receiver_pref[match_donor_position], M[match_index[0]][1], receiver_agent.agentid)
			D.remove(M[match_index[0]][0])
		
		except Exception:
		
			try:
			
				M.append((receiver_pref[match_donor_position], receiver_agent.agentid))
				D.remove(M[match_index[0]][0])
			
			except Exception:
			
				pass

	
	#	Return matching and remaining agents	#
	return M, D, R, V



##  The main function   ##

#   Main    #
def main():

	#	Get volunteer settings	#
	save_setting, v_setting, pref_setting, sort_setting, manip_setting = SAVE, VOLUNTEERS, PREFERENCE, SORTING, MANIPULATION

    #   Auto-generate agent requests   #
	agent_auto_generate = get_agent_generation_options()
	
	#	Display settings	#
	print_locked("\n\n\nSETTINGS APPLIED:")
	print_locked("Agent request saving:\t\t", save_setting)
	print_locked("Volunteer availability:\t\t", v_setting)
	print_locked("Agent preference used:\t\t", pref_setting)
	print_locked("Receiver sort timing:\t\t", sort_setting)
	print_locked("Preference manipulation:\t", manip_setting)
    
	if agent_auto_generate.upper() != 'Y':
    
		C, PFD, PFR, NPFD, NPFR, V = read_and_classify_agents()
    	
	else:
    
		num_requests = get_num_requests()
		C, PFD, PFR, NPFD, NPFR, V = generate_and_classify_agents(num_requests)
    
	#	Update with volunteer settings	#
	V = random.sample(V, int(len(V) * round(get_v_settings(v_setting)/get_v_settings('32X'), 5)))
	
	#	Manipulation	#
	if manip_setting == 'ON' and agent_auto_generate.upper() != 'Y':
	
		working_agents = PFD + PFR + NPFD + NPFR
		previous_matches = get_matches()
		common_agents = [agent for agent in working_agents if agent in [y for x in previous_matches for y in x]]
		manipulated_ids = random.sample(common_agents, random.choice(range(1, len(common_agents))))
		previous_matches = list(set([the_tuple for the_tuple in previous_matches if (the_tuple[0] in manipulated_ids or the_tuple[1] in manipulated_ids or the_tuple[-1] in manipulated_ids)]))
		
		for agent in C:
		
			if agent.agentid in manipulated_ids:
			
				agent.m_pref = agent.pref[::-1]
	
	#	Keep counts	#
	c_PFD, c_PFR, c_NPFD, c_NPFR, c_V = len(PFD), len(PFR), len(NPFD), len(NPFR), len(V)
	
	#	Display counts	#
	print_locked("\nAGENT COUNTS:\t\t\t", c_PFD + c_NPFD + c_PFR + c_NPFR + c_V)
	print_locked("Perishable donors:\t\t", c_PFD)
	print_locked("Non-perishable donors:\t\t", c_NPFD)
	print_locked("Perishable receivers:\t\t", c_PFR)
	print_locked("Non-perishable receivers:\t", c_NPFR)
	print_locked("Volunteers:\t\t\t", c_V, "(", round(get_v_settings(v_setting)/2), "X donors )")
    
    #	Assign volunteer, update preference and match requests	#
    #	Perishable	#
	Mp, PFD, PFR, V = match_requests(C, PFD, PFR, V, Food = 'P')
	Mp = [the_tuple for the_tuple in Mp if (the_tuple[-1] in PFR)]
	
    #	Non-perishable	#
	Mnp, NPFD, NPFR, V = match_requests(C, NPFD, NPFR, V, Food = '')
	Mnp = [the_tuple for the_tuple in Mnp if (the_tuple[-1] in NPFR)]
	
	#	Save matches	#
	
	multiprocessing.Process(target=save_matches, args=(Mp + Mnp, )).start()
	
	#	Display matches	#
	print_locked("\nAGENTS MATCHED:\t\t\t", len(Mp) + len(Mnp), "/", c_PFD + c_NPFD, "(", round(100 * (len(Mp) + len(Mnp))/(c_PFD + c_NPFD), 2), "% )")
	print_locked("Perishable:\t\t\t", len(Mp), "/", c_PFD, "(", round(100 * (len(Mp))/(c_PFD), 2), "% )")
	print_locked("Non-perishable:\t\t\t", len(Mnp), "/", c_NPFD, "(", round(100 * (len(Mnp))/(c_NPFD), 2), "% )")
	
	#	Manipulation	#
	if manip_setting == 'ON' and agent_auto_generate.upper() != 'Y':
	
		#	Current matches	#
		current_matches = list(set([the_tuple for the_tuple in Mp + Mnp if (the_tuple[0] in manipulated_ids or the_tuple[1] in manipulated_ids or the_tuple[-1] in manipulated_ids)]))
		
		#	Manipulation stats	#
		better, same, worse, uncomparable = 0, 0, 0, 0
		
		
		for agent in manipulated_ids:
		
			assignments = []
			
			for match in previous_matches:
			
				if agent == match[0]:
				
					previous = match[-1]
					assignments.append(match[-1])
					break
				
				elif agent == match[-1]:
				
					previous = match[0]
					assignments.append(match[0])
					break
			
			for match in current_matches:
			
				if agent == match[0]:
				
					current = match[-1]
					assignments.append(match[-1])
					break
				
				elif agent == match[-1]:
				
					current = match[0]
					assignments.append(match[0])
					break
				
				else:
				
					current = None
			
			orig_preference = get_agent(C, agent).pref
			relative_pref = [preference for preference in orig_preference if preference in assignments]
			
			'''
			try:
			
				print_locked(agent, previous, current, relative_pref)
			
			except Exception:
			
				print_locked(agent, [match for match in previous_matches if agent == match[0] or agent == match[1]], [match for match in current_matches if agent == match[0] or agent == match[1]], relative_pref)
			'''
			
			if previous == current:
			
				same = same + 1
			
			elif previous > -1 and current is None:
			
				worse = worse + 1
			
			elif len(relative_pref) == 2:
			
				if relative_pref[0] == previous:
				
					worse = worse + 1
				
				elif relative_pref[1] == previous:
				
					better = better + 1
			
			else:
			
				uncomparable = uncomparable + 1

		#	Display manipulation results	#
		print_locked("\nMANIPULATION RESULTS:\t\t", len(manipulated_ids))
		print_locked("Gained:\t\t\t\t", better, "(", round(100 * (better)/(len(manipulated_ids)), 2), "% )")
		print_locked("Lost:\t\t\t\t", worse, "(", round(100 * (worse)/(len(manipulated_ids)), 2), "% )")
		print_locked("Same:\t\t\t\t", same, "(", round(100 * (same)/(len(manipulated_ids)), 2), "% )")
		print_locked("Uncomparable:\t\t\t", uncomparable, "(", round(100 * (uncomparable)/(len(manipulated_ids)), 2), "% )")




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

