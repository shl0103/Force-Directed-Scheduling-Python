#!/usr/bin/env python


import sys
import os
import llvm 
# top-level, for common stuff
from llvm.core import *
global Latency
import copy
global Reg_Limit
import time
#===----------------------------------------------------------------------===
# Get the name of an LLVM value
def get_name(val) :
    if (not isinstance(val, Value)):
        return ''
    if isinstance(val, Argument):
        #return val.name + " [in]" 
        return val.name
    if isinstance(val, GlobalVariable):
        #return val.name + " [out]" 
        return val.name 
    if isinstance(val, Instruction):
        if val.opcode_name == 'store':
           return "[store]" 
    if isinstance(val, ConstantInt):
        return str(val.z_ext_value)
    return val.name
# /*to calculate depth of each instruction 'key', Dict is dictionary of instructions. Depth gives number of stages below instruction in graph8/

def CalcDepth(Dict,key,l):

    key1=key
    Users=Dict[key1]['Users']
    if(Users==""):
        return l
    else:
        if("," not in Users):
            l=l+1
            l=CalcDepth(Dict,Users,l)
        else:
            Users=Users.split(",")
            l=l+1
            list_val=[]
            for item in Users:
                list_val.append(CalcDepth(Dict,item,l))
            l=max(list_val)
        return l


# To  find subtree in graph(key is instruction in subtree, DictMain is dictionary of instructions, Listkey is list of instructions in subtree)
def FindTrees(DictMain,key,Listkey):
    Users=DictMain[key]['Users']
    if(Users==""):
        pass
    elif("," not in Users):
        Listkey.append(Users)
        Listkey.append(key)
        Listkey=FindTrees(DictMain,Users,Listkey)
    else:
        Users=Users.split(",")
        for item in Users:
            Listkey.append(key)
            Listkey.append(item)
            Listkey=FindTrees(DictMain,item,Listkey)
    return Listkey 

    # To calculate distribution graph of all Dictionary
def CalculateDGNew(Dict):
    #fds_dump.write("\n\n ENTERED DG NEW CALC")
    global Latency
    DG_vector=[]
    for i in range(0,Latency):
        DG_vector.append(0.0)
    for key in Dict.iterkeys():
        if(Dict[key]['Type']=='STORE'):
            continue
        if(Dict[key]['Users']==""):
            continue
            NumberOfCycles=Dict[key]['Timeframe'][1]-Dict[key]['Timeframe'][0]            
        else:
            if("," not in Dict[key]['Users']):
                Succ=Dict[key]['Users']
                ASAP_Lifetime=Dict[Succ]['Timeframe'][0]-Dict[key]['Timeframe'][0]
                ALAP_Lifetime=Dict[Succ]['Timeframe'][1]-Dict[key]['Timeframe'][1]
                Max_Lifetime=Dict[Succ]['Timeframe'][1]-Dict[key]['Timeframe'][0]
                Avg_Life=float(ASAP_Lifetime+ALAP_Lifetime+Max_Lifetime)/3
                overlap=0
                if(Dict[Succ]['Timeframe'][0]>Dict[key]['Timeframe'][1]):
                    overlap=Dict[Succ]['Timeframe'][0]-Dict[key]['Timeframe'][1]-1                
                for i in range(Dict[key]['Timeframe'][0],Dict[Succ]['Timeframe'][0]):
                    if(i in range(Dict[key]['Timeframe'][1]+1,Dict[Succ]['Timeframe'][0])):
                       DG_vector[i]+=1
                    else:
                        DG_contribution=float((Avg_Life-overlap)/(Max_Lifetime-overlap))
                        DG_vector[i]+=DG_contribution
            else:
                       Users=Dict[key]['Users'] 
                       Users=Users.split(",")
                       max_avg_life=0
                       max_user=""
                       for item in Users:     
                            ASAP_Lifetime=Dict[item]['Timeframe'][0]-Dict[key]['Timeframe'][0]
                            ALAP_Lifetime=Dict[item]['Timeframe'][1]-Dict[key]['Timeframe'][1]
                            Max_Lifetime=Dict[item]['Timeframe'][1]-Dict[key]['Timeframe'][0]
                            Avg_Life=float(ASAP_Lifetime+ALAP_Lifetime+Max_Lifetime)/3
                            if(Avg_Life>=max_avg_life):
                               max_avg_life=Avg_Life
                               max_user=item
                       ASAP_Lifetime=Dict[max_user]['Timeframe'][0]-Dict[key]['Timeframe'][0]
                       ALAP_Lifetime=Dict[max_user]['Timeframe'][1]-Dict[key]['Timeframe'][1]
                       Max_Lifetime=Dict[max_user]['Timeframe'][1]-Dict[key]['Timeframe'][0]
                       Avg_Life=float(ASAP_Lifetime+ALAP_Lifetime+Max_Lifetime)/3
                       overlap=0
                       if(Dict[max_user]['Timeframe'][0]>Dict[key]['Timeframe'][1]):
                            overlap=Dict[max_user]['Timeframe'][0]-Dict[key]['Timeframe'][1]-1
                       for i in range(Dict[key]['Timeframe'][0],Dict[max_user]['Timeframe'][0]):

                            if(i in range(Dict[key]['Timeframe'][1]+1,Dict[max_user]['Timeframe'][0]+1)):
                               DG_vector[i]+=1
                            else:
                                DG_contribution=float((Avg_Life-overlap)/(Max_Lifetime-overlap))
                                DG_vector[i]+=DG_contribution
    return DG_vector

    
  # To calculate self force of instruction key in cycle step. Dict is dictionary of all instructions
def CalculateSelfForceNew(Dict,key,step):
    DictCopy=copy.deepcopy(Dict)
    DictCopy[key]['Timeframe'][0]=step
    DictCopy[key]['Timeframe'][1]=step
    DictCopy=AdjustPredTimeframes(DictCopy,key,step,"main")
    DictCopy=AdjustSuccTimeFrames(DictCopy,key,step,"main")
    DG_Mod=CalculateDGNew(DictCopy)
    Pred_Available=0.0
    Preds=Dict[key]['Predecessors']
    if(Preds==""):
        Pred_Available=DictCopy[key]['Timeframe'][0]
    else:
            if("," not in Preds):
                if(DictCopy[Preds]['FDS Scheduled?']=="Yes"):
                    Pred_Available=DictCopy[Preds]['FDS Start Time']+1
                else:
                    Pred_Available=int(round(((DictCopy[Preds]['Timeframe'][0]+DictCopy[Preds]['Timeframe'][1])/2)))
            else:
                Preds=Preds.split(",")
                earliest_start=DictCopy[key]['Timeframe'][0]
                for item in Preds:
                    if(DictCopy[item]['FDS Scheduled?']=="Yes"):
                        if(Dict[item]['FDS Start Time']<earliest_start):
                            earliest_start=DictCopy[item]['FDS Start Time']+1
                    else:
                        time_approx=round(((DictCopy[item]['Timeframe'][0]+DictCopy[item]['Timeframe'][1])/2))
                        if(time_approx<earliest_start):
                            earliest_start=time_approx
                Pred_Available=int(earliest_start)
    Users=DictCopy[key]['Users']
    if(Users==""):
        Last_Needed=DictCopy[key]['Timeframe'][1]
    else:
        if("," not in Users):
            if(DictCopy[Users]['FDS Scheduled?']=="Yes"):
                User_Start_Time=DictCopy[Users]['FDS Start Time']
            else:
                User_Start_Time=round(((DictCopy[Users]['Timeframe'][0]+DictCopy[Users]['Timeframe'][1])/2))
            Last_Needed=int(User_Start_Time)
        else:
            Users=Users.split(",")
            Max_Start=DictCopy[key]['Timeframe'][1]
            for item in Users:
                if(DictCopy[item]['FDS Scheduled?']=="Yes"):
                    if(DictCopy[item]['FDS Start Time']>Max_Start):
                        Max_Start=DictCopy[item]['FDS Start Time']
                else:
                    time_2=round(((DictCopy[item]['Timeframe'][0]+DictCopy[item]['Timeframe'][1])/2))
                    if(time_2>Max_Start):
                        Max_Start=time_2
            Last_Needed=int(Max_Start)
    NumberOfCycles=Last_Needed-Pred_Available
    New_Sum=0.0

    for i in range(Pred_Available,Last_Needed):
        if(i==step):
            New_Sum+=DG_Mod[i]
        else:
            New_Sum+=DG_Mod[i]
    DG_in_step=float(New_Sum)
    DG_ALL=0.0
    
    for i in range(Dict[key]['Timeframe'][0],Dict[key]['Timeframe'][1]+1):
        DictCopy={}
        DictCopy=copy.deepcopy(Dict)
        DictCopy[key]['Timeframe'][0]=i
        DictCopy[key]['Timeframe'][1]=i
        DictCopy=AdjustPredTimeframes(DictCopy,key,i,"main")
        DictCopy=AdjustSuccTimeFrames(DictCopy,key,i,"main")
        DG_Mod=CalculateDGNew(DictCopy)
        New_Sum=0.0
        Pred_Available=0.0
        Preds=Dict[key]['Predecessors']
        if(Preds==""):
            Pred_Available=DictCopy[key]['Timeframe'][0]
        else:
            if("," not in Preds):
                if(DictCopy[Preds]['FDS Scheduled?']=="Yes"):
                    Pred_Available=DictCopy[Preds]['FDS Start Time']+1
                else:
                    Pred_Available=int(round(((DictCopy[Preds]['Timeframe'][0]+DictCopy[Preds]['Timeframe'][1])/2)))
            else:
                Preds=Preds.split(",")
                earliest_start=DictCopy[key]['Timeframe'][0]
                for item in Preds:
                    if(DictCopy[item]['FDS Scheduled?']=="Yes"):
                        if(DictCopy[item]['FDS Start Time']<earliest_start):
                            earliest_start=DictCopy[item]['FDS Start Time']+1
                    else:
                        time_3=round(((DictCopy[item]['Timeframe'][0]+DictCopy[item]['Timeframe'][1])/2))
                        if(time_3<earliest_start):
                            earliest_start=time_3
                Pred_Available=int(earliest_start)     
        Users=DictCopy[key]['Users']
        if(Users==""):
            Last_Needed=DictCopy[key]['Timeframe'][1]
        else:
            if("," not in Users):
                if(DictCopy[Users]['FDS Scheduled?']=="Yes"):
                    User_Start_Time=DictCopy[Users]['FDS Start Time']
                else:
                    User_Start_Time=round(((DictCopy[Users]['Timeframe'][0]+DictCopy[Users]['Timeframe'][1])/2))
                Last_Needed=int(User_Start_Time)
            else:
                Users=Users.split(",")
                Max_Start=DictCopy[key]['Timeframe'][1]
                for item in Users:
                    if(DictCopy[item]['FDS Scheduled?']=="Yes"):
                        if(DictCopy[item]['FDS Start Time']>Max_Start):
                            Max_Start=DictCopy[item]['FDS Start Time']
                    else:
                        time_4=round(((DictCopy[item]['Timeframe'][0]+DictCopy[item]['Timeframe'][1])/2))
                        if(time_4>Max_Start):
                            Max_Start=time_4
                Last_Needed=int(Max_Start)        
        NumberOfCycles=Last_Needed-Pred_Available
        for j in range(Pred_Available,Last_Needed):
            if(j==i):
                New_Sum+=DG_Mod[j]
            else:
                New_Sum+=DG_Mod[j]
        New_Sum=float(New_Sum)
        DG_ALL+=New_Sum
    Number_Of_Cycles=DictCopy[key]['Timeframe'][1]-DictCopy[key]['Timeframe'][0]+1
    Self_Force=0.0
    Self_Force=DG_in_step-float(DG_ALL/Number_Of_Cycles)
    return Self_Force



# To calculate predecessor and successor forces of key in cycle step
def CalcOtherForceNew(Dict,key,step):
    DictCopy=copy.deepcopy(Dict)
    DictCopy[key]['Timeframe'][0]=step
    DictCopy[key]['Timeframe'][1]=step
    DictCopy=AdjustPredTimeframes(DictCopy,key,step,"main")
    DictCopy=AdjustSuccTimeFrames(DictCopy,key,step,"main")
    Users=DictCopy[key]['Users']
    Preds=DictCopy[key]['Predecessors']
    Total_Force=0.0
    Pred_Force=0.0
    Succ_Force=0.0
    if(Users==""):
        Succ_Force=0.0
    else:
         Users=Users.split(",")
         for item in Users:
            SingleUser=item
            NewASAPStartTime=DictCopy[SingleUser]['Timeframe'][0]
            NewALAPStartTime=DictCopy[SingleUser]['Timeframe'][1]
            NewNumberOfCycles=NewALAPStartTime-NewASAPStartTime+1
            NewSum=0.0
            NewForce=0.0
            OldASAPStartTime=Dict[SingleUser]['Timeframe'][0]
            OldALAPStartTime=Dict[SingleUser]['Timeframe'][1]
            for i in range(NewASAPStartTime,NewALAPStartTime+1):
                New_Sum=CalculateSelfForceNew(DictCopy,SingleUser,i)
                NewForce+=New_Sum
            NewForce=float(NewForce/NewNumberOfCycles) 
            OldNumberOfCycles=OldALAPStartTime-OldASAPStartTime+1
            Old_Force=0.0
            DictOldCopy=copy.deepcopy(Dict)
            Old_Sum=0.0
            NumberOfCycles=OldALAPStartTime-OldASAPStartTime+1
            for i in range(OldASAPStartTime,OldALAPStartTime+1):
                Old_Sum=CalculateSelfForceNew(DictOldCopy,SingleUser,i)
                Old_Force+=Old_Sum
            Old_Force=float(Old_Force/NumberOfCycles)
            Force=NewForce-Old_Force
            Succ_Force+=Force
    if(Preds==""):
        Pred_Force=0.0
    else:
         Preds=Preds.split(",")
         for item in Preds:
            SinglePred=item
            NewASAPStartTime=DictCopy[SinglePred]['Timeframe'][0]
            NewALAPStartTime=DictCopy[SinglePred]['Timeframe'][1]
            NewNumberOfCycles=NewALAPStartTime-NewASAPStartTime+1
            NewSum=0.0
            NewForce=0.0
            OldASAPStartTime=Dict[SinglePred]['Timeframe'][0]
            OldALAPStartTime=Dict[SinglePred]['Timeframe'][1]
            for i in range(NewASAPStartTime,NewALAPStartTime+1):
                New_Sum=CalculateSelfForceNew(DictCopy,SinglePred,i)
                NewForce+=New_Sum
            NewForce=float(NewForce/NewNumberOfCycles)            
            OldNumberOfCycles=OldALAPStartTime-OldASAPStartTime+1
            Old_Force=0.0
            DictOldCopy=copy.deepcopy(Dict)
            Old_Sum=0.0
            NumberOfCycles=OldALAPStartTime-OldASAPStartTime+1
            for i in range(OldASAPStartTime,OldALAPStartTime+1):
                Old_Sum=CalculateSelfForceNew(DictOldCopy,SinglePred,i)
                Old_Force+=Old_Sum
            Old_Force=float(Old_Force/NumberOfCycles)
            Force=NewForce-Old_Force
            Pred_Force+=Force
    Total_Force=Pred_Force+Succ_Force
    return Total_Force

# To extend the timeframe of each instruction in dictionary based on New relaxed latency
def RelaxLatency(dict_local,Old,New):
    change=New-Old
    for key1 in dict_local.iterkeys():
        if("Ret" in key1):
                 dict_local[key1]['Timeframe'][1]=0
                 dict_local[key1]['ALAP Start Time']=0
                 continue
        dict_local[key1]['Timeframe'][1]+=change
        dict_local[key1]['ALAP Start Time']+=change
    for key in dict_local.iterkeys():
            if("Ret" in key):
                dict_local[key]['Lifetime']=0
                continue
            User_list=dict_local[key]['Users']
            if(',' not in User_list):
                if(User_list==""):
                    dict_local[key]['Lifetime']=dict_local[key]['Timeframe'][1]+1
                else:                
                    dict_local[key]['Lifetime']=dict_local[User_list]['Timeframe'][1]#(dict_local[User_list]['Timeframe'][1]+dict_local[User_list]['Timeframe'][0])/2
            else:
                NoOfUsers=User_list.count(',')+1
                c=0
                MaxLifeTime=0
                while(c<NoOfUsers):
                    if(',' in User_list ):
                        item=User_list.split(',',1)[0]
                    else:
                        item=User_list
                    if(dict_local[item]['Timeframe'][1]>MaxLifeTime):
                        MaxLifeTime=dict_local[item]['Timeframe'][1]
                    if(',' in User_list ):
                        User_list=User_list.split(',',1)[1]
                    c=c+1
                dict_local[key]['Lifetime']=MaxLifeTime
    return dict_local


def AdjustPredTimeframes(DictLocal,key_val,c_step,mod_dict):
    global count
    global DG_Modified
    mod=mod_dict
    ListOfPredsAdjust=DictLocal[key_val]['Predecessors'][:]
    if(ListOfPredsAdjust!=""):
                    if(',' not in ListOfPredsAdjust):  
                        SinglePredAdjust=ListOfPredsAdjust
                        Pred_TimeFrame_Adjust=DictLocal[SinglePredAdjust]['Timeframe'][:]
                        if(DictLocal[SinglePredAdjust]['FDS Scheduled?']=="No"):       
                            if(Pred_TimeFrame_Adjust[1]>=DictLocal[key_val]['Timeframe'][1]):
                                DictLocal[SinglePredAdjust]['Timeframe'][1]=DictLocal[key_val]['Timeframe'][1]-1
                                if(mod=='temp'):    
                                    if(DictLocal[SinglePredAdjust]['Timeframe'][1]==DictLocal[SinglePredAdjust]['Timeframe'][0]):
                                        DictLocal[SinglePredAdjust]['FDS Scheduled?']="Yes"
                                        count+=1
                                        DictLocal[SinglePredAdjust]['FDS Start Time']=DictLocal[SinglePredAdjust]['Timeframe'][0]           
                                DictLocal=(AdjustPredTimeframes(DictLocal,SinglePredAdjust,DictLocal[SinglePredAdjust]['Timeframe'][0],mod))
                        return DictLocal
                    else:
                        NoOfPredsAdjust=ListOfPredsAdjust.count(',')+1
                        cnt_pred_adjust=0
                        while(cnt_pred_adjust<NoOfPredsAdjust):
                            if(',' in ListOfPredsAdjust):
                                CurrPredAdjust=ListOfPredsAdjust.split(',',1)[0]
                            else:
                                CurrPredAdjust=ListOfPredsAdjust
                            if(DictLocal[CurrPredAdjust]['FDS Scheduled?']=="No"):
                                Pred_TimeFrame_Adjust=DictLocal[CurrPredAdjust]['Timeframe'][:]
                                if(Pred_TimeFrame_Adjust[1]>=DictLocal[key_val]['Timeframe'][1]):
                                    DictLocal[CurrPredAdjust]['Timeframe'][1]=DictLocal[key_val]['Timeframe'][1]-1
                                    if(mod=='temp'):
                                        if(DictLocal[CurrPredAdjust]['Timeframe'][1]==DictLocal[CurrPredAdjust]['Timeframe'][0]):
                                            DictLocal[CurrPredAdjust]['FDS Scheduled?']="Yes"
                                            count+=1
                                            DictLocal[CurrPredAdjust]['FDS Start Time']=DictLocal[CurrPredAdjust]['Timeframe'][0]     
                                    DictLocal=(AdjustPredTimeframes(DictLocal,CurrPredAdjust,DictLocal[CurrPredAdjust]['Timeframe'][0],mod))
                            if(',' in ListOfPredsAdjust):
                                ListOfPredsAdjust=ListOfPredsAdjust.split(',',1)[1]
                            cnt_pred_adjust+=1
                        return DictLocal
    else:
        return DictLocal


# To adjust predecessors lifetimes of instruction key_val once it has been scheduled
def AdjustPredLifetime(DictLocal,key_val):
    ListOfPredsAdjustLifetime=DictLocal[key_val]['Predecessors'][:]
    if(ListOfPredsAdjustLifetime!=""):
                    if(',' not in ListOfPredsAdjustLifetime):
                            SinglePredAdjust=ListOfPredsAdjustLifetime                 
                            UsersOfPred=DictLocal[SinglePredAdjust]['Users']
                            if(',' not in UsersOfPred):
                                DictLocal[SinglePredAdjust]['Lifetime']=DictLocal[key_val]['Timeframe'][1]
                            else:
                                MaxStartTime=0
                                SuccsOfPred=UsersOfPred
                                NumberOfUsers=SuccsOfPred.count(',')+1
                                cnt=0
                                while(cnt<NumberOfUsers):
                                    if("," in SuccsOfPred):
                                        FirstUser=SuccsOfPred.split(",",1)[0]
                                    else:
                                        FirstUser=SuccsOfPred
                                    if(FirstUser!=key_val):                                        
                                        StartTime=0
                                        if(DictLocal[FirstUser]['FDS Scheduled?']=="Yes"):
                                            StartTime=DictLocal[FirstUser]['FDS Start Time']
                                        else:
                                            StartTime=DictLocal[FirstUser]['Timeframe'][1]
                                        if(StartTime>MaxStartTime):
                                            MaxStartTime=StartTime                                    
                                    cnt+=1
                                    if("," in SuccsOfPred):
                                        SuccsOfPred=SuccsOfPred.split(",",1)[1]
                                if(DictLocal[key_val]['FDS Start Time']>MaxStartTime):
                                     DictLocal[SinglePredAdjust]['Lifetime']=DictLocal[key_val]['Timeframe'][1]                                  
                            return DictLocal
                    else:
                        
                        NoOfPredsAdjustLifetime=ListOfPredsAdjustLifetime.count(',')+1
                        cnt_pred_adjust=0
                        while(cnt_pred_adjust<NoOfPredsAdjustLifetime):
                                if(',' in ListOfPredsAdjustLifetime):
                                    CurrPredAdjustLifetime=ListOfPredsAdjustLifetime.split(',',1)[0]                                    
                                else:
                                    CurrPredAdjustLifetime=ListOfPredsAdjustLifetime
                                UsersOfPred=DictLocal[CurrPredAdjustLifetime]['Users']
                                if(',' not in UsersOfPred):
                                    DictLocal[CurrPredAdjustLifetime]['Lifetime']=DictLocal[key_val]['Timeframe'][1]
                                else:
                                    MaxStartTime=0
                                    SuccsOfPred=UsersOfPred
                                    NumberOfUsers=SuccsOfPred.count(',')+1
                                    cnt=0                                    
                                    StartTime=0
                                    while(cnt<NumberOfUsers):
                                        if("," in SuccsOfPred):
                                            FirstUser=SuccsOfPred.split(",",1)[0]
                                        else:
                                            FirstUser=SuccsOfPred
                                        if(FirstUser!=key_val):                                            
                                            if(DictLocal[FirstUser]['FDS Scheduled?']=="Yes"):
                                                StartTime=DictLocal[FirstUser]['FDS Start Time']
                                            else:
                                                StartTime=DictLocal[FirstUser]['Timeframe'][1]
                                            if(StartTime>MaxStartTime):
                                                MaxStartTime=StartTime                                            
                                        cnt+=1
                                        if("," in SuccsOfPred):
                                            SuccsOfPred=SuccsOfPred.split(",",1)[1]
                                    if(DictLocal[key_val]['FDS Start Time']>=MaxStartTime):
                                        DictLocal[CurrPredAdjustLifetime]['Lifetime']=DictLocal[key_val]['Timeframe'][1]                                        
                                if(',' in ListOfPredsAdjustLifetime):
                                    ListOfPredsAdjustLifetime=ListOfPredsAdjustLifetime.split(',',1)[1]
                                cnt_pred_adjust+=1
                    return DictLocal
    else:
        return DictLocal


# adjust timeframe of successors of key_val once it has been scheduled
def AdjustSuccTimeFrames(DictLocal,key_val,c_step,mod_dict):
    mod=mod_dict
    global count
    ListOfSuccsAdjust=DictLocal[key_val]['Users'][:]
    if(ListOfSuccsAdjust!=""):
                    if(',' not in ListOfSuccsAdjust):
                        SingleSuccAdjust=ListOfSuccsAdjust            
                        Succ_TimeFrame_Adjust=DictLocal[SingleSuccAdjust]['Timeframe'][:]
                        if(DictLocal[SingleSuccAdjust]['FDS Scheduled?']=="No"):
                            if(Succ_TimeFrame_Adjust[0]<=DictLocal[key_val]['Timeframe'][0]):
                                DictLocal[SingleSuccAdjust]['Timeframe'][0]=DictLocal[key_val]['Timeframe'][0]+1
                                if(mod=='temp'):
                                    if(DictLocal[SingleSuccAdjust]['Timeframe'][0]==DictLocal[SingleSuccAdjust]['Timeframe'][1]):
                                        DictLocal[SingleSuccAdjust]['FDS Scheduled?']="Yes"
                                        count+=1
                                        DictLocal[SingleSuccAdjust]['FDS Start Time']=DictLocal[SingleSuccAdjust]['Timeframe'][0]                               
                                DictLocal=(AdjustSuccTimeFrames(DictLocal,SingleSuccAdjust,DictLocal[SingleSuccAdjust]['Timeframe'][0],mod))
                        return DictLocal
                    else:
                        NoOfSuccsAdjust=ListOfSuccsAdjust.count(',')+1
                        cnt_succ_adjust=0
                        while(cnt_succ_adjust<NoOfSuccsAdjust):
                            if(',' in ListOfSuccsAdjust):
                                CurrSuccAdjust=ListOfSuccsAdjust.split(',',1)[0]
                            else:
                                CurrSuccAdjust=ListOfSuccsAdjust                  
                            if(DictLocal[CurrSuccAdjust]['FDS Scheduled?']=="No"):
                                Succ_TimeFrame_Adjust=DictLocal[CurrSuccAdjust]['Timeframe'][:]
                                if(Succ_TimeFrame_Adjust[0]<=DictLocal[key_val]['Timeframe'][0]):                                        
                                    DictLocal[CurrSuccAdjust]['Timeframe'][0]=DictLocal[key_val]['Timeframe'][0]+1
                                    if(mod=='temp'):                                        
                                        if(DictLocal[CurrSuccAdjust]['Timeframe'][0]==DictLocal[CurrSuccAdjust]['Timeframe'][1]):
                                            DictLocal[CurrSuccAdjust]['FDS Scheduled?']="Yes"
                                            count+=1    
                                            DictLocal[CurrSuccAdjust]['FDS Start Time']=DictLocal[CurrSuccAdjust]['Timeframe'][0]                                       
                                    DictLocal=(AdjustSuccTimeFrames(DictLocal,CurrSuccAdjust,DictLocal[CurrSuccAdjust]['Timeframe'][0],mod))
                            if(',' in ListOfSuccsAdjust):
                                ListOfSuccsAdjust=ListOfSuccsAdjust.split(',',1)[1]
                            cnt_succ_adjust+=1 
                        return DictLocal
    else:
        return DictLocal




    # Is the value a store?
def is_store(val) :
    if not isinstance(val, Instruction):
        return 0
    return val.opcode_name == 'store'

# Is the value a return?
def is_return(val) :
    if not isinstance(val, Instruction):
        return 0 
    return val.opcode_name == 'ret'

# Is the value a multiplication?
def is_mul(val) :
    if not isinstance(val, Instruction):
        return 0
    if not val.is_binary_op:
        return 0
    return val.opcode_name == 'mul'

# Is the value an addition or a subtraction?
def is_addsub(val) :
    if not isinstance(val, Instruction):
        return 0
    if not val.is_binary_op:
        return 0
    opc = val.opcode_name 
    return opc == 'add' or opc == 'sub' 

# Get the pretty string in C-like syntax of an LLVM value
def to_string(val) :
    # Is an Instruction?
    if isinstance(val, Instruction): 
        opc = val.opcode_name
        # Get the first operand if there is any
        if val.operand_count > 0:
            op0 = val.operands[0]
        # Get the second operand if there is any
        if val.operand_count > 1:
            op1 = val.operands[1]
        # Binary operation
        if val.is_binary_op:
            opc_map = {'add':'+', 'sub':'-', 'mul':'*'}
            if (opc in opc_map): opc = opc_map[opc]
            # Generate string in C-like syntax
            return get_name(val) + ' = ' + get_name(op0) + ' ' + opc + ' ' + get_name(op1)
        # Store operation
        elif opc == 'store':
            # Generate string in C-like syntax
            return '*' + get_name(op1) + ' = ' + get_name(op0)
        # Store operation
        elif opc == 'ret':
            # Generate string in C-like syntax
            return 'return'
        else:
            return opc
    # Is a Constant?
    elif isinstance(val, ConstantInt):
        return get_name(val)
    return '' 

# Main function
def run(testcase):
    ASAP_start=time.time()
    f = open(testcase)
    global Latency
    global Availability
    global count
    global Reg_Limit
    global DG_Modified
    global fds_dump
    count=0
    f1=open(r'temp.txt','w')
    m = Module.from_assembly(f)
    dut_name = os.path.splitext(os.path.basename(testcase))[0]
    dut = m.get_function_named(dut_name)

    #===-----------------------------------------------------------===
    # Print instructions in DFG under test 
    for inst in dut.basic_blocks[0].instructions:
        #print the instruction in LLVM form
##        print "\n"
##        print inst
        f1.write("\n")
        f1.write(str(inst))
        #Print the instruction in C form
##        print "  - C syntax: " + to_string(inst)
        f1.write("  - C syntax: " + to_string(inst))
        

        # Print its operation type
        type = "  - Type: " 
        if is_store(inst) :
            type += "STORE"
        elif is_addsub(inst) :
            type += "ADDSUB"
        elif is_mul(inst) :
            type += "MUL"
        elif is_return(inst) :
            type += "RETURN"
        else: 
            type += "UNKNOWN"
##        print type
        f1.write(type)

        # Print its operands in short name 
        operands = "  - Operands: "
        for o in inst.operands:
            operands += get_name(o) + "; "
        # Zero operands?
        if len(inst.operands) <= 0:
            operands += "NONE"
##        print operands
        f1.write(operands)

        # Print its uses in pretty form
        uses = "  - Uses: "
        for u in inst.uses:
            uses += to_string(u) + "; "
        # Zero uses?
        if len(inst.uses) <= 0:
            uses += "NONE"
##        print uses
        f1.write(uses)

    # No work left
    f.close()
    f1.close()
    DictMain={}
    f2=open(r'temp.txt')
    f2.readline()
    NoStores=0

    #*************CREATION OF DICTIONARIES FOR EACH OPERATION**************************************#
    for line in f2:
        
        if("STORE" in line):
            strline=line
            #print strline
            dicttemp={} # Dictionary of Dictionaries- contains all operations
            dicttemp['Scheduled?']='No'
            dicttemp['ALAP Scheduled?']='No'
            dicttemp['Start Time']=0
            dicttemp['Life Time']=0
            dicttemp['End Time']=0
            dicttemp['ALAP Start Time']=0
            dicttemp['ALAP End Time']=0
            dicttemp['Timeframe']=[]
            dicttemp['Self Force']=[]
            dicttemp['Total Force']=[]
            dicttemp['FDS Start Time']=0
            dicttemp['FDS End Time']=0
            dicttemp['FDS Scheduled?']='No'
            dicttemp['Probability']=0
            dicttemp['Change']=0
            dicttemp['DistFromPred']=0
            strline=strline.split("C syntax: ",1)[1]
            Name=strline
            Name=Name.split(' =',1)[0]
            dicttemp['Name']=Name
            #print "Name of Store Dict",Name
            CSyntax=strline.split("  - Type:",1)[0]
            dicttemp['C Syntax']=CSyntax
            strline=strline.split("  - Type: ",1)[1]
            Type=strline.split("  - Operands",1)[0]
            dicttemp['Type']=Type

            strline=strline.split("Uses:",1)[1]
            NoOfUses=strline.count(';')
            Users=""
            i=0
            while(i<NoOfUses):
                if(i!=0):
                    Users+=","
                Pred=strline.split(";",1)[0]
                Pred=Pred.split(" =")[0]
                Pred=Pred.split(" ",1)[1]
                strline=strline.split(";",1)[1]
                Users+=Pred
                i=i+1

            dicttemp['Users']=Users
            dicttemp['Predecessors']=""
            #print dicttemp
            DictMain[Name]=dicttemp
            NoStores=NoStores+1
        elif("ret" in line):
            dicttemp={}
            dicttemp['Scheduled?']='Yes'
            dicttemp['ALAP Scheduled?']='Yes'
            dicttemp['Start Time']=0
            dicttemp['Life Time']=0
            dicttemp['End Time']=0
            dicttemp['ALAP Start Time']=0
            dicttemp['ALAP End Time']=0
            dicttemp['Timeframe']=[]
            dicttemp['Self Force']=[]
            dicttemp['Total Force']=[]
            dicttemp['FDS Start Time']=0
            dicttemp['FDS End Time']=0
            dicttemp['FDS Scheduled?']='No'
            dicttemp['Probability']=0.0
            dicttemp['C Syntax']='ret'
            dicttemp['Type']='ret'
            dicttemp['Users']=""
            dicttemp['Predecessors']=""
            DictMain['Ret']=dicttemp
            dicttemp['Change']=0
            dicttemp['DistFromPred']=0
        else:
            strline=line
            #print strline
            #print "inside sched"
            dicttemp={}
            dicttemp['Scheduled?']='No'
            dicttemp['ALAP Scheduled?']='No'
            dicttemp['Start Time']=0
            dicttemp['Life Time']=0
            dicttemp['End Time']=0
            dicttemp['Timeframe']=[]
            dicttemp['Self Force']=[]
            dicttemp['Total Force']=[]
            dicttemp['FDS Start Time']=0
            dicttemp['FDS End Time']=0
            dicttemp['FDS Scheduled?']='No'
            dicttemp['Probability']=0.0
            dicttemp['ALAP Start Time']=0
            dicttemp['ALAP End Time']=0
            dicttemp['Change']=0
            dicttemp['DistFromPred']=0
            strline=strline.split("%",1)[1]
            OperationName=strline.split(" =",1)[0]
            dicttemp['Name']=OperationName
            strline=strline.split("C syntax: ",1)[1]
            CSyntax=strline.split("  - Type:",1)[0]
            dicttemp['C Syntax']=CSyntax
            strline=strline.split("  - Type: ",1)[1]
            Type=strline.split("  - Operands",1)[0]
            dicttemp['Type']=Type
            strline=strline.split("Uses:",1)[1]
            NoOfUses=strline.count(';')
            Users=""
            i=0
            while(i<NoOfUses):
                if(i!=0):
                    Users+=","
                Pred=strline.split(";",1)[0]
                Pred=Pred.split(" =")[0]
                Pred=Pred.split(" ",1)[1]
                strline=strline.split(";",1)[1]
                Users+=Pred
                i=i+1

            dicttemp['Users']=Users
            dicttemp['Predecessors']=""
            DictMain[OperationName]=dicttemp
  
    f2.close()        

    NoOfOperations=0
    #--------------------------Gets the list of predecessors for each operation-can work if inputs are not topplogically sorted------------------------*
    for key in DictMain.iterkeys():
        if(DictMain[key]['Scheduled?']=='No'):
            NoOfOperations+=1
        for key2 in DictMain.iterkeys():
            User_list=DictMain[key2]['Users']
            if(',' not in User_list):
                if(key==User_list):
                    if(DictMain[key]['Predecessors']==""):
                        DictMain[key]['Predecessors']=key2
                    else:                  
                        DictMain[key]['Predecessors']+=","+key2
            else:
                NoOfUserP=User_list.count(',')+1
                c=0
                while(c<NoOfUserP):
                    if(',' in User_list ):
                        item=User_list.split(',',1)[0]
                    else:
                        item=User_list
                    if(item==key):
                        if(DictMain[key]['Predecessors']==""):
                            DictMain[key]['Predecessors']=key2
                        else:                  
                            DictMain[key]['Predecessors']+=","+key2
                    if(',' in User_list ):
                        User_list=User_list.split(',',1)[1]
                    c=c+1
                        
                            
    NoOfStoresFound=0     
    TotalOperations=NoOfOperations

    

    while(NoOfOperations>0):
        for key in DictMain.iterkeys():
            if(DictMain[key]['Scheduled?']=="No"):
                ListOfPred=DictMain[key]['Predecessors']
                if(ListOfPred==""):
                    DictMain[key]['Start Time']=0
                    DictMain[key]['End Time']=1
                    DictMain[key]['Scheduled?']='Yes'
                    DictMain[key]['Timeframe'].append(DictMain[key]['Start Time'])
                    NoOfOperations=NoOfOperations-1
                else:
                        if(',' not in ListOfPred):
                            Dependency=ListOfPred
                            if(DictMain[Dependency]['Scheduled?']=='Yes'):
                                DictMain[key]['Start Time']=DictMain[Dependency]['End Time']
                                DictMain[key]['End Time']=DictMain[key]['Start Time']+1
                                DictMain[key]['Scheduled?']='Yes'
                                DictMain[key]['Timeframe'].append(DictMain[key]['Start Time'])
                                NoOfOperations=NoOfOperations-1
                        else:
                           NoOfDependencies=ListOfPred.count(',')+1
                           
                           j=0
                           sched=0 
                           MaxEndTime=0
                           while(j<NoOfDependencies):
                                if(',' in ListOfPred):
                                    Dependency=ListOfPred.split(',',1)[0]
                                else:
                                    Dependency=ListOfPred
                                if(DictMain[Dependency]['Scheduled?']=='Yes'):
                                    sched=sched+1
                                    temp=DictMain[Dependency]['End Time']
                                    if(temp>MaxEndTime):
                                        MaxEndTime=temp
                                if(',' in ListOfPred):
                                    ListOfPred=ListOfPred.split(',',1)[1]
                                j=j+1
                           if(sched==NoOfDependencies):
                                DictMain[key]['Start Time']=MaxEndTime
                                DictMain[key]['End Time']=DictMain[key]['Start Time']+1
                                DictMain[key]['Scheduled?']='Yes'
                                DictMain[key]['Timeframe'].append(DictMain[key]['Start Time'])
                                NoOfOperations=NoOfOperations-1

    #calculation of Latency and Lifetime
    Latency=1    
    for key in DictMain.iterkeys():
        if(DictMain[key]['End Time']>Latency):
            Latency=DictMain[key]['End Time']
        User_list=DictMain[key]['Users']
        
        if(',' not in User_list):
            if(User_list==""):
                DictMain[key]['Lifetime']=DictMain[key]['Start Time']+1
            else:                
                DictMain[key]['Lifetime']=DictMain[User_list]['Start Time']
        else:
            NoOfUsers=User_list.count(',')+1
            c=0
            MaxLifeTime=0
            while(c<NoOfUsers):
                if(',' in User_list ):
                    item=User_list.split(',',1)[0]
                else:
                    item=User_list
                if(DictMain[item]['Start Time']>MaxLifeTime):
                    MaxLifeTime=DictMain[item]['Start Time']
                if(',' in User_list ):
                    User_list=User_list.split(',',1)[1]
                c=c+1
            DictMain[key]['Lifetime']=MaxLifeTime
    DictMain['Ret']['Start Time']=Latency-1
    DictMain['Ret']['End Time']=Latency
    DictMain['Ret']['ALAP Start Time']=Latency-1
    DictMain['Ret']['ALAP End Time']=Latency
    DictMain['Ret']['Timeframe'].append(DictMain[key]['Start Time'])
    DictMain['Ret']['Timeframe'].append(DictMain[key]['ALAP Start Time'])
    DictMain['Ret']['Self Force']=[]
    DictMain['Ret']['Total Force']=[]
    DictMain['Ret']['FDS Start Time']=0
    DictMain['Ret']['FDS End Time']=0
    DictMain['Ret']['FDS Scheduled?']='No'
    DictMain['Ret']['Probability']=0.0
    ASAP_end=time.time()
    ASAP_time=ASAP_end-ASAP_start
    #----------printing output onto result file------------------------#
    result_asap=(str(sys.argv[1]).split("/",1)[1]).split(".ll",1)[0]+"__REG.txt"
    f_ASAP=open(result_asap,'w')
    f_ASAP.write("\n          lATENCY IS : "+str(Latency))
    f_ASAP.write("\n****----ASAP Schedule----****")
    f_ASAP.write("\n TIME TAKEN"+str(ASAP_time)+" seconds")
    lineno=0
    MaxNoOfADDSUB=0
    MaxNoOfMULT=0
    MaxNoOfRegisters=0
    while(lineno<Latency):
        AddSub=0
        Mult=0
        Reg=0
        Prev_stage=0
        Store=0
        inst_retained=[]
        f_ASAP.write("\n \n")
        
        str1="CYCLE"+str(lineno+1)+"\n"
        f_ASAP.write(str1)
        for key in DictMain.iterkeys():
                          
            if(DictMain[key]['Start Time']==lineno):
                if(DictMain[key]['Type']=='ret'):
                    continue
                f_ASAP.write("\n"+DictMain[key]['C Syntax'])
                if(DictMain[key]['Type']=="ADDSUB"):
                    AddSub+=1
                if(DictMain[key]['Type']=="MUL"):
                    Mult+=1
                if(DictMain[key]['Type']=="STORE"):
                    Store+=1
                
            if((DictMain[key]['Lifetime']>lineno) and (DictMain[key]['Start Time']<=lineno)):
                Prev_stage=Prev_stage+1
                inst_retained.append(key)
            if(AddSub>MaxNoOfADDSUB):
                MaxNoOfADDSUB=AddSub
            if(Mult>MaxNoOfMULT):
                MaxNoOfMULT=Mult
        Reg=Prev_stage
        if(Reg>MaxNoOfRegisters):
            MaxNoOfRegisters=Reg
        
        f_ASAP.write("\n **** RESOURCE USAGE ***")
        f_ASAP.write("\nNO of ADDSUB required: "+str(AddSub))
        f_ASAP.write("\nNO of MUL required: "+str(Mult))
        f_ASAP.write("\nNO of REG required: "+str(Reg))
        f_ASAP.write("\nInstructions Retained"+str(inst_retained))
        lineno=lineno+1
    f_ASAP.write("\n **** OVERALL RESOURCE USAGE***")
    f_ASAP.write("\n MAX NUMBER OF ADD/SUB : "+str(MaxNoOfADDSUB))
    f_ASAP.write("\n MAX NUMBER OF MULT : "+str(MaxNoOfMULT))
    f_ASAP.write("\n MAX NUMBER OF REG : "+str(MaxNoOfRegisters))
    
        
#-----------ALAP start--------------

   #-------------------------------ALAP--------------------------------------------*
    ALAP_start=time.time()
    NoOfOperations=TotalOperations
    while(NoOfOperations>0):
        for key in DictMain.iterkeys():
            if(DictMain[key]['ALAP Scheduled?']=="No"):
                ListOfSucc=DictMain[key]['Users']
                if(ListOfSucc==""):
                    DictMain[key]['ALAP End Time']=Latency
                    DictMain[key]['ALAP Start Time']=DictMain[key]['ALAP End Time']-1
                    DictMain[key]['ALAP Scheduled?']='Yes'
                    DictMain[key]['Timeframe'].append(DictMain[key]['ALAP Start Time'])
                    NoOfOperations=NoOfOperations-1
                else:
                        if(',' not in ListOfSucc):
                            Dependency=ListOfSucc
                            if(DictMain[Dependency]['ALAP Scheduled?']=='Yes'):
                                DictMain[key]['ALAP End Time']=DictMain[Dependency]['ALAP Start Time']
                                DictMain[key]['ALAP Start Time']=DictMain[key]['ALAP End Time']-1
                                DictMain[key]['Timeframe'].append(DictMain[key]['ALAP Start Time'])
                                DictMain[key]['ALAP Scheduled?']='Yes'
                                NoOfOperations=NoOfOperations-1
                        else:
                           NoOfDependencies=ListOfSucc.count(',')+1
                           
                           j=0
                           sched=0 
                           MinStartTime=Latency
                           while(j<NoOfDependencies):
                                if(',' in ListOfSucc):
                                    Dependency=ListOfSucc.split(',',1)[0]
                                else:
                                    Dependency=ListOfSucc
                                if(DictMain[Dependency]['ALAP Scheduled?']=='Yes'):
                                    sched=sched+1
                                    temp=DictMain[Dependency]['ALAP Start Time']
                                    if(temp<MinStartTime):
                                        MinStartTime=temp
                                if(',' in ListOfSucc):
                                    ListOfSucc=ListOfSucc.split(',',1)[1]
                                j=j+1
                           if(sched==NoOfDependencies):
                                DictMain[key]['ALAP End Time']=MinStartTime
                                DictMain[key]['ALAP Start Time']=DictMain[key]['ALAP End Time']-1
                                DictMain[key]['ALAP Scheduled?']='Yes'
                                DictMain[key]['Timeframe'].append(DictMain[key]['ALAP Start Time'])
                                NoOfOperations=NoOfOperations-1

    for key in DictMain.iterkeys():
        User_list=DictMain[key]['Users']
        
        if(',' not in User_list):
            if(User_list==""):
                DictMain[key]['Lifetime']=DictMain[key]['ALAP Start Time']+1
            else:                
                DictMain[key]['Lifetime']=DictMain[User_list]['ALAP Start Time']
        else:
            NoOfUsers=User_list.count(',')+1
            c=0
            MaxLifeTime=0
            while(c<NoOfUsers):
                if(',' in User_list ):
                    item=User_list.split(',',1)[0]
                else:
                    item=User_list
                if(DictMain[item]['ALAP Start Time']>MaxLifeTime):
                    MaxLifeTime=DictMain[item]['ALAP Start Time']
                if(',' in User_list ):
                    User_list=User_list.split(',',1)[1]
                c=c+1
            DictMain[key]['Lifetime']=MaxLifeTime
    ALAP_end=time.time()
    ALAP_time=ALAP_end-ALAP_start
    #-------------------printing out ALAP SChedule-------------------------
    f_ASAP.write("\n\n\n ****----ALAP Schedule----****")
    f_ASAP.write("\n TIME TAKEN :"+str(ALAP_time)+" seconds")
    lineno=0
    MaxNoOfADDSUB=0
    MaxNoOfMULT=0
    MaxNoOfRegisters=0
    while(lineno<Latency):
        AddSub=0 
        Mult=0
        Reg=0
        Prev_stage=0
        Store=0
        inst_retained=[]
        f_ASAP.write("\n \n")        
        str1="CYCLE"+str(lineno+1)+"\n"
        f_ASAP.write(str1)
        for key in DictMain.iterkeys():                          
            if(DictMain[key]['ALAP Start Time']==lineno):
                if(DictMain[key]['Type']=='ret'):
                    continue
                f_ASAP.write("\n"+DictMain[key]['C Syntax'])
                if(DictMain[key]['Type']=="ADDSUB"):
                    AddSub+=1
                if(DictMain[key]['Type']=="MUL"):
                    Mult+=1
                if(DictMain[key]['Type']=="STORE"):
                    Store+=1                
            if((DictMain[key]['Lifetime']>lineno) and (DictMain[key]['ALAP Start Time']<=lineno)):
                Prev_stage=Prev_stage+1
                inst_retained.append(key)            
            if(AddSub>MaxNoOfADDSUB):
                MaxNoOfADDSUB=AddSub
            if(Mult>MaxNoOfMULT):
                MaxNoOfMULT=Mult
        Reg=Prev_stage
        if(Reg>MaxNoOfRegisters):
            MaxNoOfRegisters=Reg
        f_ASAP.write("\n **** RESOURCE USAGE ***")
        f_ASAP.write("\nNO of ADDSUB required: "+str(AddSub))
        f_ASAP.write("\nNO of MUL required: "+str(Mult))
        f_ASAP.write("\nNO of REG required: "+str(Reg))
        f_ASAP.write("\nInstructions Retained"+str(inst_retained))
        lineno=lineno+1
    f_ASAP.write("\n **** OVERALL RESOURCE USAGE ***")
    f_ASAP.write("\n MAX NUMBER OF ADD/SUB : "+str(MaxNoOfADDSUB))
    f_ASAP.write("\n MAX NUMBER OF MULT : "+str(MaxNoOfMULT))
    f_ASAP.write("\n MAX NUMBER OF REG : "+str(MaxNoOfRegisters))
    main_list=[]
    DictGraphs={}
    for key in DictMain.iterkeys():
        if(DictMain[key]['Start Time']==0):
            vars()[key]=[]
            vars()[key]=FindTrees(DictMain,key,eval(key))
            DictGraphs[key]=eval(key)
    for k in DictGraphs.iterkeys():
        listk=DictGraphs[k]
        remove=[]
        keep=[]
        for o in DictGraphs.iterkeys():
            listo=DictGraphs[o]
            list_common=set(listk).intersection(listo)
            if(len(list_common))==0:
                pass
            else:
                if("NULL" not in DictGraphs[k]):
                    keep.append(k)
                    DictGraphs[k]=DictGraphs[k]+DictGraphs[o]
                    if o not in keep:
                        remove.append(o)
        if(len(remove)!=0):
            for l in remove:
                DictGraphs[l]=["NULL"]
    DictFinal={}
    for k in DictGraphs.iterkeys():
        #print "\n \n \ n   ",k, "  ",DictGraphs[k]
        if(DictGraphs[k]!=["NULL"]):
            DictFinal[k]=DictGraphs[k]


    listkey=[]        
    sizeg=[]
    depthg=[]
    
    for k in DictFinal.iterkeys():
        #print "\n key of DIct final is ",k, "  ",DictFinal[k]
        listofel=DictFinal[k]
        listkey.append(k)
        max_depth=0
        sizeg.append(len(listofel))
        for u in listofel:
            m=CalcDepth(DictMain,u,0)
            if(m>max_depth):
                max_depth=m

        depthg.append(max_depth)

    list_desc_size=[]
    sizez=sizeg[:]
    
    while(len(sizez)>0):
        max_size=max(sizez)
        pos_max=sizeg.index(max_size)
        list_desc_size.append(listkey[pos_max])
        sizez.remove(max_size)
        sizeg.remove(max_size)
        listkey.remove(listkey[pos_max])

    FDS_start=time.time()
    DictMain['Ret']['FDS Scheduled?']="Yes"
    DictMain['Ret']['Timeframe'][0]=0
    DictMain['Ret']['Timeframe'][1]=0
    DictMain['Ret']['FDS Start Time']=0
    DictMain['Ret']['Lifetime']=0
    #################################################################################################################################################################
    NoOfOpFDS=TotalOperations
    DG_Reg_Stat=[]
    DG_Modified=[]
    Availability=[]
    Reg_Limit=500
    #DictMain=RelaxLatency(DictMain,Latency,int(round(Latency+6)))
    global Latency
    Latency=Latency+7
    for i in range(0,Latency):
        Availability.append(Reg_Limit)
    NoOfRegsUsed=[]
    for i in range(0,Latency):
        NoOfRegsUsed.append(0)
    FDS_time=FDS_start

    while(NoOfOpFDS>0):#FDS begins
        P_Store=0.0
        min_force=99999
        modified=0
        schedule_this=[0,0,0]
        Not_Possible=0
        for key in DictMain.iterkeys():
            if(DictMain[key]['FDS Scheduled?']=="No"):
                a=DictMain[key]["Timeframe"][0]
                b=DictMain[key]["Timeframe"][1]
                if(a==b):
                    DictMain[key]['FDS Start Time']=a
                    DictMain[key]['FDS End Time']=a+1
                    DictMain[key]["Timeframe"][0]=a
                    DictMain[key]["Timeframe"][1]=a
                    lifetime_ok=[]
                    if(DictMain[key]['Type']=="STORE"):
                       DictMain[key]["Lifetime"]=a 
                    start=a
                    DictMain[key]['FDS Scheduled?']="Yes"
                    DictMain=(AdjustPredTimeframes((DictMain),key,start,'main'))
                    DictMain=(AdjustSuccTimeFrames((DictMain),key,start,'main'))
                    DictMain=(AdjustPredLifetime((DictMain),key))
                    NoOfOpFDS-=1
                else:
                    Self_Force=0.0
                    Pred_Succ_Forces=0.0
                    Total_Force=0.0
                    attempt=0
                    Not_Possible=0
                    for i in range(a,b+1):
                        Self_Force=CalculateSelfForceNew(DictMain,key,i)
                        Pred_Succ_Forces= CalcOtherForceNew(DictMain,key,i)
                        Total_Force=Self_Force+Pred_Succ_Forces
                        if(Total_Force<min_force):
                            modified=1
                            min_force=Total_Force
                            schedule_this[0]=key
                            schedule_this[1]=i
                            schedule_this[2]=min_force


        if(modified==1):
            Op_To_Schedule=schedule_this[0]
            Cycle_To_Schedule=schedule_this[1]
            lifetime_ok=[]
            for i in range(Cycle_To_Schedule,DictMain[Op_To_Schedule]["Lifetime"]):
                if(Availability[i]==0):
                    lifetime_ok.append(1)
                else:
                    lifetime_ok.append(0)
            DictMain[Op_To_Schedule]['FDS Start Time']=Cycle_To_Schedule
            DictMain[Op_To_Schedule]['FDS End Time']=Cycle_To_Schedule+1
            DictMain[Op_To_Schedule]["Timeframe"][0]=Cycle_To_Schedule
            DictMain[Op_To_Schedule]["Timeframe"][1]=Cycle_To_Schedule
            if(DictMain[Op_To_Schedule]['Type']=="STORE"):
                       DictMain[Op_To_Schedule]["Lifetime"]=Cycle_To_Schedule
            if(DictMain[Op_To_Schedule]['Users']==""):
                DictMain[Op_To_Schedule]["Lifetime"]=Cycle_To_Schedule+1
            if(DictMain[Op_To_Schedule]["Lifetime"]==Cycle_To_Schedule):
                DictMain[Op_To_Schedule]["Lifetime"]+=1
            start=Cycle_To_Schedule
            DictMain[Op_To_Schedule]['FDS Scheduled?']="Yes"   
            DictMain=(AdjustPredTimeframes(DictMain,Op_To_Schedule,start,'main'))
            DictMain=(AdjustSuccTimeFrames(DictMain,Op_To_Schedule,start,'main'))
            DictMain=(AdjustPredLifetime(DictMain,Op_To_Schedule))            
            NoOfOpFDS-=1
            if(Not_Possible==1):
                break
    FDS_end=time.time()
    FDS_time=FDS_end-FDS_start
    f_ASAP.write("\n\n\n ****FDS SCHEDULING***")
    f_ASAP.write("\n TIME TAKEN :"+str(FDS_time)+" seconds")
    for key in DictMain.iterkeys():
        User_list=DictMain[key]['Users']        
        if(',' not in User_list):
            if(User_list==""):
                DictMain[key]['Lifetime']=DictMain[key]['FDS Start Time']+1
            else:                
                DictMain[key]['Lifetime']=DictMain[User_list]['FDS Start Time']
        else:
            NoOfUsers=User_list.count(',')+1
            c=0
            MaxLifeTime=0
            while(c<NoOfUsers):
                if(',' in User_list ):
                    item=User_list.split(',',1)[0]
                else:
                    item=User_list
                if(DictMain[item]['FDS Start Time']>MaxLifeTime):
                    MaxLifeTime=DictMain[item]['FDS Start Time']
                if(',' in User_list ):
                    User_list=User_list.split(',',1)[1]
                c=c+1
            DictMain[key]['Lifetime']=MaxLifeTime
    filename='output_graph'
    def print_dot(DictMain,filename):
         file = open("%s.dot" % filename, "w")
         #print "opened file!"
         file.write("digraph %s {\n" % filename)
         for key in DictMain.iterkeys():
             Users=DictMain[key]['Users']
             if(Users!=""):
                 if("," in Users):
                     Users=Users.split(",")
                 else:
                     Users=[Users]
                 for user in Users:
                         file.write(" %s -> %s\n" % (str(key),str(user)))
         file.write("}\n")
         file.close()
    #print_dot(DictMain,filename)
    lineno=0
    MaxNoOfADDSUB=0
    MaxNoOfMULT=0
    MaxNoOfRegisters=0

    while(lineno<Latency):
        AddSub=0 
        Mult=0
        Reg=0
        Prev_stage=0
        Store=0
        inst_retained=[]
        f_ASAP.write("\n \n")
        
        str1="CYCLE"+str(lineno+1)+"\n"
        f_ASAP.write(str1)
        for key in DictMain.iterkeys():
                          
            if(DictMain[key]['FDS Start Time']==lineno):
                if(DictMain[key]['Type']=='ret'):
                    continue
                f_ASAP.write("\n"+DictMain[key]['C Syntax'])
                if(DictMain[key]['Type']=="ADDSUB"):
                    AddSub+=1
                if(DictMain[key]['Type']=="MUL"):
                    Mult+=1
                if(DictMain[key]['Type']=="STORE"):
                    Store+=1
                
            if((DictMain[key]['Lifetime']>lineno) and (DictMain[key]['FDS Start Time']<=lineno and DictMain[key]['Type']!="STORE")):
                inst_retained.append(key)
                Prev_stage=Prev_stage+1
            if(AddSub>MaxNoOfADDSUB):
                MaxNoOfADDSUB=AddSub
            if(Mult>MaxNoOfMULT):
                MaxNoOfMULT=Mult
        Reg=Prev_stage
        if(Reg>MaxNoOfRegisters):
            MaxNoOfRegisters=Reg
        f_ASAP.write("\n **** FDS RESOURCE USAGE ***")
        f_ASAP.write("\nNO of ADDSUB required: "+str(AddSub))
        f_ASAP.write("\nNO of MUL required: "+str(Mult))
        f_ASAP.write("\nNO of REG required: "+str(Reg))
        f_ASAP.write("\nInstructions Retained"+str(inst_retained))           
        lineno=lineno+1
    f_ASAP.write("\n **** OVERALL RESOURCE USAGE ***")
    f_ASAP.write("\n MAX NUMBER OF ADD/SUB : "+str(MaxNoOfADDSUB))
    f_ASAP.write("\n MAX NUMBER OF MULT : "+str(MaxNoOfMULT))
    f_ASAP.write("\n MAX NUMBER OF REG : "+str(MaxNoOfRegisters))       
    f_ASAP.close()

# Prompt CLI usage
if len(sys.argv) < 2:
    sys.exit('Usage: python %s <test>.ll' % sys.argv[0])
# Test exists?
elif not os.path.exists(sys.argv[1]):
    sys.exit('Cannot locate specified test case %s' % sys.argv[1])

run(sys.argv[1])




