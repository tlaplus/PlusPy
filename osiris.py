# Author: Robbert van Renesse, 2020

import sys
import threading
import time
import socket
import pickle
import getopt
import math
import pluspy

# global verbose, membership, proposals, messages, pp, lock, cond, skt, UDP_IP_PORT, uid, my_id
verbose = False
membership = frozenset()
proposals = frozenset()
messages = frozenset()
pp = None
lock = threading.Lock()
cond = threading.Condition(lock)
skt = None
UDP_IP_PORT = 6666
uid = 0
my_id = None

# Report new membership and create new instance of Bosco if member
def report(newuid, newmembers):
    global verbose, membership, proposals, messages, pp, lock, cond, skt, UDP_IP_PORT, uid, my_id

    if uid == 0:
        Retransmitter().start()
        Reader().start()
    uid = newuid
    membership = newmembers
    proposals = frozenset()
    messages = frozenset()
    print("Membership", my_id, uid, pluspy.format(membership))
    if my_id in membership:
        pp = pluspy.PlusPy("Bosco", constants={
                    "Processes": frozenset(membership),
                    "Quorums": quorums()
            })
        pluspy.netEpoch = uid
        pp.init("Init")
    else:
        pp = None

def sendBeacon():
    global verbose, membership, proposals, messages, pp, lock, cond, skt, UDP_IP_PORT, uid, my_id

    beacon = (membership, uid)
    msg = pickle.dumps(beacon)
    skt.sendto(msg, ('<broadcast>', UDP_IP_PORT))

def genQuorums(rem, q, qs):
    if rem == []:
        return frozenset({frozenset(q)}) if len(q) == qs else frozenset()
    else:
        return genQuorums(rem[1:], q + [rem[0]], qs).union(
            genQuorums(rem[1:], q, qs))

def quorums():
    # Determine the size of a threshold quorum
    qs = math.ceil((2 * len(membership) + 1) / 3)
    return genQuorums(list(membership), [], qs)

class Receiver(threading.Thread):
    def run(self):
        global verbose, membership, proposals, messages, pp, lock, cond, skt, UDP_IP_PORT, uid, my_id

        while True:
            data, addr = skt.recvfrom(4096)
            (membership2, uid2) = pickle.loads(data)
            with lock:
                if uid2 > uid:
                    if verbose: 
                        print("RECEIVED REPORT", uid, uid2)
                    report(uid2, membership2)

# Periodically broadcast:
#   - current membership
#   - current UID
class Retransmitter(threading.Thread):
    def run(self):
        global verbose, membership, proposals, messages, pp, lock, cond, skt, UDP_IP_PORT, uid, my_id

        while True:
            time.sleep(1)
            if pp != None:
                sendBeacon()

class Reader(threading.Thread):
    def run(self):
        global verbose, membership, proposals, messages, pp, lock, cond, skt, UDP_IP_PORT, uid, my_id

        while True:
            cmd = input("")
            if len(cmd) == 0 or cmd[0] not in { "+", "-" }:
                print("input should start with + or -")
            elif pp == None:
                print("not a member currently")
            else:
                proposal = pluspy.FrozenDict(
                    { "command": cmd[0], "host": cmd[1:] }
                )
                with lock:
                    props = pp.get("Proposals")
                    x = set(props)
                    x.add(proposal)
                    pp.set("Proposals", frozenset(x))
                    cond.notify()

def usage():
    print("Usage: osiris [options] address:port")
    print("  options: ")
    print("    -h: help")
    print("    -v: verbose output")
    sys.exit(1)

def main():
    global verbose, membership, proposals, messages, pp, lock, cond, skt, UDP_IP_PORT, uid, my_id

    # Get options.  First set default values
    genesis = False
    try:
        opts, args = getopt.getopt(sys.argv[1:], "ghsv", ["help"])
    except getopt.GetoptError as err:
        print(str(err))
        usage()
    for o, a in opts:
        if o in { "-v" }:
            verbose = True
        elif o in { "-g" }:
            genesis = True
        elif o in { "-h", "--help" }:
            usage()
        else:
            assert False, "unhandled option"
    if len(args) != 1:
        usage()
    my_id = args[0]

    pluspy.netInit(my_id)

    if genesis:
        report(1, frozenset({ my_id }))

    skt = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
    skt.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)
    skt.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
    skt.bind(("", UDP_IP_PORT))

    Receiver().start()

    # main loop
    while True:
        with lock:
            # Try to make a step
            if pp != None:
                if pp.next("Proc", my_id):
                    if verbose:
                        print("Next context:", pluspy.format(pp.getall()))
                    continue

                # See if there is a decision
                procs = pp.get("procs")
                state = pluspy.convert(pluspy.funceval(procs, [my_id]))
                if state["round"] == "INFINITY":
                    x = set(membership)
                    c = state["estimate"]
                    if c["command"] == "+":
                        x.add(c["host"])
                    elif c["command"] == "-":
                        x.discard(c["host"])
                    else:
                        print("UNKNOWN COMMAND", c)
                        sys.exit(1)
                    if verbose:
                        print("GOT DECISION", uid)
                    report(uid + 1, frozenset(x))
                    sendBeacon()

            # Wait for some input to arrive
            cond.wait(0.1)

if __name__ == "__main__":
    main()
