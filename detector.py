#! /usr/bin/python3

##
##  DETECTOR.PY
##
##  Performs pcap file analysis and vector correlation 
##  in order to detect data exfiltration over DoH
##
##  written by Tony Imbierski Jan-Feb 2021
##  as part of RHUL Information Security MSc
##
##     usage: detector.py <pcapfile> [-verbose] [-brief] [-sizes] [-times] [-vectors] [-learn] [-detect]
##  
##
import sys
import os
import pcapy
import time
import statistics 
import json
import math
import scipy
import numpy

global pcapFile
global baseTime
global verbose
global summary
global printSizes
global printTimes
global csv
global terse
global learn
global detect
global learnData
global learnDataUpdated
global pReader
global detectThreshhold

LEARNDATAFILE='learndatafile'
detectThreshhold=0.99

OFF_MAC_DST = 0
LEN_MAC_DST = 6
OFF_MAC_SRC = 6
LEN_MAC_SRC = 6
OFF_ETHERTYPE = 12
LEN_ETHERTYPE = 2
OFF_IP_PROTO = 23
LEN_IP_PROTO = 1
OFF_IP_DST = 30
LEN_IP_DST = 4
OFF_IP_SRC = 26
LEN_IP_SRC = 4
OFF_TCP_SRC = 34
LEN_TCP_SRC = 2
OFF_TCP_DST = 36
LEN_TCP_DST = 2

TYPE_IP = 0x0800
PROTO_TCP = 6
PROTO_UDP = 17

LB = '('
RB = ')'
SP = ' '
NUL = ''
LSB = '['
RSB = ']'
COMMA = ','
PERCENT = '%'

def mag(v):
    res = 0
    for n in v:
        res = res + n * n 
    return math.sqrt(res)

def cosang(v1, v2):
    v1s = v1
    v2s = v2

    v1 = []
    for c in v1s:
        v1.append(int(c))
    v2 = []
    for c in v2s:
        v2.append(int(c))
        
    dot = numpy.dot(v1,v2)
    cosang = (dot / mag(v1) / mag(v2))
    return cosang

def uniqueAppend(l, item):
    if item in l:
        return False
    l.append(item)
    return True

def intPc(x, tot):
    return int((x*100) / tot)

def loadLearnData():
    global learnData
    global learnDataUpdated
    try:
        learnDataFile = open(LEARNDATAFILE)
        learnDataJson = learnDataFile.readline().rstrip()
        learnData = json.loads(learnDataJson)
        learnDataFile.close()
        learnDataUpdated = False
    except:
        print("could not find or load %s" %LEARNDATAFILE)
        learnData = []

def saveLearnData():
    global learnData
    global learnDataUpdated

    if not learnDataUpdated:
        print("not saving learn data - no updates")
        return 

    try:
        if os.path.isfile(LEARNDATAFILE):
            print("%s exists, OK to overwrite (existing contents already copied)? (Y/n)" %LEARNDATAFILE)
            ans = sys.stdin.readline()
            
            if not (ans[0].upper == 'Y') and not (ans == '\n'):
                print("aborted")
                exit()

        learnDataFile = open(LEARNDATAFILE,"w")
        learnDataJson = json.dumps(learnData)
        learnDataFile.write(learnDataJson)
        learnDataFile.close()
        learnDataUpdated = False
        print("updated learn data in %s" %LEARNDATAFILE)
    except:
        print("could not save %s" %LEARNDATAFILE)

class Conversation:
    def __init__(self):
        self.packets = []
        self.sizes = []
        self.times = []
        self.sizesBySizeIn = {}
        self.sizesBySizeOut = {}
        self.packetsOut = 0
        self.packetsIn = 0
        self.inVector = []
        self.outVector = []
        self.sortedSizesBySizeIn = ()
        self.sortedSizesBySizeOut = ()

    def strIpSrc(self):
        outl = ''
        for b in self.ipSrc:
            outl += str(int(b)) + '.'
        return outl[0:-1]

    def strIpDst(self):
        outl = ''
        for b in self.ipDst:
            outl += str(int(b)) + '.'
        return outl[0:-1]

    def orgBySize(self):
        for packet in self.packets:
            s = packet.len
            if packet.tcpSrc > packet.tcpDst:
                self.packetsOut += 1
                if s in self.sizesBySizeOut:
                    self.sizesBySizeOut[s] += 1
                else:
                    self.sizesBySizeOut[s] = 1
            else:
                self.packetsIn += 1
                if s in self.sizesBySizeIn:
                    self.sizesBySizeIn[s] += 1
                else:
                    self.sizesBySizeIn[s] = 1

        self.sortedSizesBySizeIn = sorted(self.sizesBySizeIn)
        self.sortedSizesBySizeOut = sorted(self.sizesBySizeOut)

        if not terse:
            print("IN:  %d" %self.packetsIn)
            print("OUT: %d" %self.packetsOut)

    def genVectors(self):
        if len(self.sortedSizesBySizeIn) == 0:
            self.orgBySize()

        index = 0
        m = [0,0,0]
        c = [0,0,0]

        for s in self.sortedSizesBySizeIn:
            index += 1
            if self.sizesBySizeIn[s] > c[0]:
                c[2] = c[1]
                c[1] = c[0]
                c[0] = self.sizesBySizeIn[s]
                m[2] = m[1]
                m[1] = m[0]
                m[0] = index
            elif self.sizesBySizeIn[s] > c[1]:
                c[2] = c[1]
                c[1] = self.sizesBySizeIn[s]
                m[2] = m[1]
                m[1] = index
            elif self.sizesBySizeIn[s] > c[2]:
                c[2] = self.sizesBySizeIn[s]
                m[2] = index

        totp = sum(c)
        self.inVector = [index, m[0], m[1], m[2], intPc(c[0],totp), intPc(c[1],totp), intPc(c[2],totp)]

        index = 0
        m = [0,0,0]
        c = [0,0,0]

        for s in self.sortedSizesBySizeOut:
            index += 1
            if self.sizesBySizeOut[s] > c[0]:
                c[2] = c[1]
                c[1] = c[0]
                c[0] = self.sizesBySizeOut[s]
                m[2] = m[1]
                m[1] = m[0]
                m[0] = index
            elif self.sizesBySizeOut[s] > c[1]:
                c[2] = c[1]
                c[1] = self.sizesBySizeOut[s]
                m[2] = m[1]
                m[1] = index
            elif self.sizesBySizeOut[s] > c[2]:
                c[2] = self.sizesBySizeOut[s]
                m[2] = index

        totp = sum(c)
        self.outVector = [index, m[0], m[1], m[2], intPc(c[0],totp), intPc(c[1],totp), intPc(c[2],totp)]

    def printSizes(self):
        if len(self.sortedSizesBySizeIn) == 0:
            self.orgBySize()
        for s in self.sortedSizesBySizeIn:
            if csv:
                print(str(s)+','+str(self.sizesBySizeIn[s]))
            else:
                percent = float(self.sizesBySizeIn[s]) / float(self.packetsIn) * 100.0
                print(str(s) + ': ' + str(self.sizesBySizeIn[s]) + "\t%3.2f%%" %percent)

        for s in self.sortedSizesBySizeOut:
            if csv:
                print(str(s)+','+str(self.sizesBySizeOut[s]))
            else:
                percent = float(self.sizesBySizeOut[s]) / float(self.packetsOut) * 100.0
                print(str(s) + ': ' + str(self.sizesBySizeOut[s]) + "\t%3.2f%%" %percent)

    def printVectors(self):
        global learnData
        global learnDataUpdated
        global detectThreshhold
        global terse

        if len(self.inVector) == 0:
            self.genVectors()

        if learn:
            if uniqueAppend(learnData, self.inVector):
                learnDataUpdated = True
            if uniqueAppend(learnData, self.outVector):
                learnDataUpdated = True
        
        print("IN:  " + str(self.inVector).replace(SP,NUL).replace(LB, NUL).replace(RB,NUL).replace(LSB,NUL).replace(RSB,NUL))
        print("OUT: " + str(self.outVector).replace(SP,NUL).replace(LB, NUL).replace(RB,NUL).replace(LSB,NUL).replace(RSB,NUL))

        if detect:
            for vec1 in self.inVector, self.outVector:
                for vec2 in learnData:
                    pr = cosang(vec1,vec2)
                    if not terse:
                        print ("correlation: " + str(pr))
                    if pr > detectThreshhold:
                        print("SUSPECTED EXFILTRATION")
                        if terse:
                            return

    def printTimes(self):
        timesByTime = {}
        for s in self.times:
            if s in timesByTime:
                timesByTime[s] += 1
            else:
                timesByTime[s] = 1

        for s in sorted(timesByTime):
            print(str(s) + ': ' + str(timesByTime[s]) )

    def label(self, convNum):
        outl = str(convNum) + ': '
        outl += self.strIpSrc() + ":" + str(self.tcpSrc) + "  <=>  "
        outl += self.strIpDst() + ":" + str(self.tcpDst) + "  "
        return outl
#########################
## END CLASS Conversation
#########################

####################
class Conversations:
####################    
    ## conversations is a dictionary of hash, conversation
    
    def __init__(self):
        self.conversations = {}

    def len(self):
        return len(self.conversations)

    def add(self, newPacket):
        if newPacket.etherType != TYPE_IP:
            return
        if newPacket.ipProto != PROTO_TCP:
            return

        cHash = newPacket.getHash()
        if cHash in self.conversations:
            thisConv = self.conversations[cHash]
            prevPacket = thisConv.packets[-1]
            newPacket.deltaTime = newPacket.absTime - prevPacket.absTime
            thisConv.packets.append(newPacket)
            thisConv.sizes.append(newPacket.len)
            thisConv.times.append(newPacket.deltaTime)
        else:
            newPacket.deltaTime = 0
            newPacket.absTime = 0
            newConv = Conversation()
            newConv.ipSrc = newPacket.ipSrc
            newConv.ipDst = newPacket.ipDst
            newConv.tcpSrc = newPacket.tcpSrc
            newConv.tcpDst = newPacket.tcpDst
            newConv.cHash = cHash
            newConv.packets.append(newPacket)
            newConv.sizes.append(newPacket.len)
            
            self.conversations[cHash] = newConv

    def fullReport(self):
        print("FULL REPORT")
        convNum = 0
        for conv in self.conversations.values():
            outl = conv.label(convNum)
            if not terse:
                print(outl)
            packetNum = 0
            for packet in conv.packets:
                outl2 = '%5d' %packetNum
                outl2 += ' %10.2f' %packet.deltaTime
                outl2 += ' %6.0d' %packet.len
                print(outl2)
                packetNum += 1
            convNum += 1

    def summaryReport(self):
        convNum = 0
        for conv in self.conversations.values():
            outl = conv.label(convNum)
            minTime = min(conv.times)
            maxTime = max(conv.times)
            minSize = min(conv.sizes)
            maxSize = max(conv.sizes)
            meanTime = statistics.mean(conv.times)
            meanSize = statistics.mean(conv.sizes)
            try:
                modeTime = statistics.mode(conv.times)
            except statistics.StatisticsError:
                modeTime = -1
            try:
                modeSize = statistics.mode(conv.sizes)
            except statistics.StatisticsError:
                modeSize = -1
            stdTime = statistics.stdev(conv.times)
            stdSize = statistics.stdev(conv.sizes)
            totSize = sum(conv.sizes)
            totTime = sum(conv.times)
            outl += "\n Packets: %8.0f" %(len(conv.packets))
            outl += '\n mean delta Time: %8.0f ' %meanTime
            # outl += ' %8.2f ' %meanTime
            # outl += ' %8.0f ' %maxTime
            # outl += ' %8.0f ' %modeTime
            outl += ' time std dev: %8.2f ' %stdTime
            outl += ' \nSizes:\n  Min: %8.0f ' %minSize
            outl += '\n  Mean: %8.2f ' %meanSize
            outl += '\n  Max: %8.0f ' %maxSize
            outl += '\n  mode: %8.0f ' %modeSize
            outl += '\n  std dev:  %8.2f ' %stdSize
            outl += '\n TOTAL TIME:  %8.2f ' %totTime
            outl += '\n TOTAL SIZE:  %8.2f \n' %totSize

            if not terse:
                print(outl)
            convNum += 1

    def printSizes(self):
        convNum = 0
        for conv in self.conversations.values():
            if not terse: 
                print(conv.label(convNum))
            conv.printSizes()
            if not terse: 
                print("\n\n")
            convNum += 1

    def printVectors(self):
        convNum = 0
        for conv in self.conversations.values():
            if not terse: 
                print(conv.label(convNum))
            conv.printVectors()
            if not terse: 
                print("\n")
            convNum += 1

    def printTimes(self):
        convNum = 0
        for conv in self.conversations.values():
            print(conv.label(convNum))
            conv.printTimes()
            print("\n")
            convNum += 1
##########################            
## END CLASS Conversations
##########################    

def errPrint(msg, end):
    sys.stderr.write(msg+end)

def timeUs(secs, usecs):
    rt = secs * 1000000 + usecs - baseTime
    return rt

def hexPrint(data, len, label):
    outStr = label + ': '
    count = 0
    for b in data:
        if b < 16:
            outStr += '0'+hex(b)[2:] + ' '                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       
        else:
            outStr += hex(b)[2:] + ' '
        count += 1
        if count >= len:
            print(outStr)
            return

class Packet:
    def __init__(self):
        self.convHash = 0
        self.deltaTime = 0
        self.tcpSrc = 0
        self.tcpDst = 0

    def strIpSrc(self):
        outl = ''
        for b in self.ipSrc:
            outl += str(int(b)) + '.'
        return outl[0:-1]

    def strIpDst(self):
        outl = ''
        for b in self.ipDst:
            outl += str(int(b)) + '.'
        return outl[0:-1]

    def getHash(self):
        if self.convHash == 0:
            self.convHash = self.ipSrc.__hash__() * self.ipDst.__hash__() + self.tcpSrc.__hash__() * self.tcpDst.__hash__()
        return self.convHash
    
    def print(self):
        print("PACKET "+ str(self.num)+": time: " + str(self.absTime) + " len:" + str(self.len))
        hexPrint(self.macSrc, LEN_MAC_SRC, "src")
        hexPrint(self.macDst, LEN_MAC_DST, "dst")
        
        if (self.etherType == TYPE_IP):
            hexPrint(self.ipSrc, LEN_IP_SRC, "IP src")
            hexPrint(self.ipDst, LEN_IP_SRC, "IP dst")
            if self.ipProto == PROTO_TCP:
                print("TCP: " + str(self.tcpSrc) + " => " + str(self.tcpDst))
                print("Conversation: " + str(self.getHash()))
            if self.ipProto == PROTO_UDP:
                print("UDP: " + str(self.tcpSrc) + " => " + str(self.tcpDst))
##################
# end class Packet
##################

def openPcap(pcapFile):
    global pReader
    try:    
        pReader = pcapy.open_offline(pcapFile)
    except:
        print("Error reading " + pcapFile)
        exit()

def genNewPacket(pcapLine, pts):
    newPacket = Packet()
    newPacket.len = pcapLine[0].getlen()
    newPacket.num = packetNum
    newPacket.absTime = timeUs(pts[0],pts[1])
    newPacket.macDst = pcapLine[1][OFF_MAC_DST:OFF_MAC_DST+LEN_MAC_DST]
    newPacket.macSrc = pcapLine[1][OFF_MAC_SRC:OFF_MAC_SRC+LEN_MAC_SRC]
    newPacket.etherType = pcapLine[1][OFF_ETHERTYPE] * 256 + pcapLine[1][OFF_ETHERTYPE+1]
    if newPacket.etherType == TYPE_IP:
        newPacket.ipSrc = pcapLine[1][OFF_IP_SRC:OFF_IP_SRC+LEN_IP_SRC]  
        newPacket.ipDst = pcapLine[1][OFF_IP_DST:OFF_IP_DST+LEN_IP_DST]
        newPacket.ipProto = pcapLine[1][OFF_IP_PROTO]    

        if newPacket.ipProto == PROTO_TCP:
            newPacket.tcpSrc = pcapLine[1][OFF_TCP_SRC] * 256 + pcapLine[1][OFF_TCP_SRC+1]
            newPacket.tcpDst = pcapLine[1][OFF_TCP_DST] * 256 + pcapLine[1][OFF_TCP_DST+1]

    return newPacket

###############
# MAIN
###############
try:
    pcapFile = sys.argv[1]

except IndexError:
    print("usage: detector.py <pcapfile> [-verbose] [-brief] [-sizes] [-times] [-vectors] [-learn] [-detect]")
    exit()

verbose = False
printSizes = False
printTimes = False
summary = False
csv = False
vectors = False
nextArgIsPort = False
nextArgIsThresh = False
terse = False
learn = False
detect = False
filterIn = False
filterOut = False
filterPort = 0

for arg in sys.argv:
    if nextArgIsThresh:
        detectThreshhold = float(arg) / 100
    nextArgIsThresh = False
    if nextArgIsPort:
        filterPort = int(arg)
        print("FILTERPORT " + str(filterPort))
    nextArgIsPort = False
    if arg == '-verbose':
        verbose = True
    if arg == '-sizes':
        printSizes = True
    if arg == '-brief':
        summary = True
    if arg == '-times':
        printTimes = True
    if arg == '-port':
        nextArgIsPort = True
    if arg == '-vectors':
        vectors = True
    if arg == '-csv':
        csv = True
    if arg == '-terse':
        terse = True
    if arg == '-in':
        filterIn = True
    if arg == '-out':
        filterOut = True
    if arg == '-learn':
        learn = True
    if arg == '-detect':
        detect = True
        nextArgIsThresh = True

if detect and learn:
    print ("detect and learn cannot be used together")
    exit()

if detect:
    filterPort = 443
    vectors = True
    print ("DETECTION MODE, threshold = " + str(detectThreshhold*100)+PERCENT)

if learn:
    filterPort = 443
    print ("LEARN MODE")
    print ("input file is assumed to contain only exfiltration data")
    print ("continue? (y/N)")
    ans = sys.stdin.readline()
    if not ans[0].upper() == 'Y':
        print("aborted")
        exit()
    vectors = True

if not terse:
    print ("loading learn data from %s" %LEARNDATAFILE)

loadLearnData()
if (detect) and (learnData == []):
    print ("detect not possible - no learned data")

if not terse: 
    print("reading " + pcapFile + "...")

openPcap(pcapFile)
convs = Conversations()

#######################
## PACKET HANDLING LOOP
#######################
pcapLine = pReader.next()
packetNum = 0

while not (pcapLine[0] == None):
    pts = pcapLine[0].getts()
    if packetNum == 0:
        baseTime = 0
        baseTime = timeUs(pts[0], pts[1])

    newPacket = genNewPacket(pcapLine, pts)
    if filterPort == 0 or newPacket.tcpSrc == filterPort or newPacket.tcpDst == filterPort:
        convs.add(newPacket)

    # log progress to stderr
    errPrint("Packets: " + str(packetNum) + "   Conversations: " + str(convs.len()), end='\r')

    pcapLine = pReader.next()
    packetNum += 1

errPrint("\n","\n")

if verbose: 
    convs.fullReport()

if summary:  
    convs.summaryReport()

if printSizes:
    convs.printSizes()

if printTimes:
    convs.printTimes()
    
if vectors:
    convs.printVectors()

if learn:
    saveLearnData()
