#!/usr/bin/env python3

"""
Operational semantics for shadow memory based machine.

TL;DR Using shadow memory frees us from tracking aliases since we
store ownership info in shadow memory with address as key.

PC (program counter): N
Address: N
R (reg file) : String -> Address
M (memory) : Address -> Address  // assume memory is used to store addresses
S (shadow memory): Address -> Value
C (Allocation state of memory) : Unused (-inf) |
                       SharedRO (< 0) | Uniq (0) | SharedRW (>0)
O (Ownership state) : Address -> C

A program state consists of a tuple <PC, R, M, S, O>.


Q> Why does memory map address to addresses?
We assume that memory only stores addresses for simplicity

Q> Why is ownership state needed?
We want to allow re-borrow and re-copy

Q> Why does ownership state need a reference count?
It is not strictly needed in the current design so can be simplified.
OTOH the complexity is hidden in the class State so letting it be there
in case it is needed in the future.

Q> When is shadow memory updated?
It is updated by an "update" operation. The given functions do
not update shadow memory.

Known iffy behaviour allowed now:
1. A borrowed (Uniq) ptr can be copied and immutably borrowed.
   (This can be solved using some idea of fractional permissions.)
2.
"""
from enum import IntEnum
from typing import Dict
import copy

Register = str
Address = int
Value = int

Ownership = int


class OwnType(IntEnum):
    UNIQ = 0


class State(object):

    def __init__(self,
                 pc: int,
                 r: Dict[Register, Address],
                 m: Dict[Address, Address],
                 s: Dict[Address, Value],
                 o: Dict[Address, Ownership]):
        self.pc: int = pc
        self.r: Dict[Register, Value] = r
        self.m: Dict[Address, Value] = m
        self.s: Dict[Address, Value] = s
        self.o: Dict[Address, Ownership] = o

    def ptrptrto(self, p: Register) -> Address:
        return self.m[self.r[p]]

    def canMove(self, a: Address) -> bool:
        return self.o[a] == OwnType.UNIQ

    def canMutBorrow(self, a: Address) -> bool:
        return self.o[a] == OwnType.UNIQ

    def canBorrow(self, a: Address) -> bool:
        return (self.o[a] == OwnType.UNIQ or
                self.o[a] < 0 and
                (self.o[a] > float('-inf')))

    def canCopy(self, a: Address) -> bool:
        return (self.o[a] == OwnType.UNIQ or
                self.o[a] > 0)

    def isBorrowed(self, a: Address) -> bool:
        return (self.o[a] == OwnType.UNIQ or
                (self.o[a] < 0 and
                 (self.o[a] > float('-inf'))))


def init() -> State:
    """
       initialize machine
    """
    # in reality we will set ownership state to -inf for every
    # address
    return State(pc=0, r={}, m={}, s={}, o={})


def alloc(p: Register, s: Value, inState: State) -> State:
    """
        Allocate memory of given size.

        p = alloc s
    """
    if p in inState.r.keys():
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    someAddress = 0  # this will be a fresh address in reality
    outState.r[p] = someAddress
    outState.o[someAddress] = OwnType.UNIQ
    return outState


def die(q0: Register, inState: State) -> State:
    """
        die q0
    """
    # updates reference count and kills name
    if (q0 not in inState.r.keys()):
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    if outState.o[outState.r[q0]] < 0:
        outState.o[outState.r[q0]] += 1
    elif outState.o[outState.r[q0]] > 0:
        outState.o[outState.r[q0]] -= 1
    outState.r.pop(q0, None)
    return outState


def brreg2reg(p0: Register,
              q0: Register,
              p1: Register,
              inState: State) -> State:
    """
    `p1, q0 = brreg2reg p0`

    """
    if (q0 in inState.r.keys() or
        p1 in inState.r.keys() or
            p0 not in inState.r.keys() or
            not inState.canMutBorrow(inState.r[p0])):
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    outState.r[q0] = outState.r[p0]
    # note: P1 is added immediately instead of waiting for
    # q0 to die since we don't want to track aliases
    # for this.
    # Right now I don't know if this is a hindrance
    # to proving equivalence with another machine.
    outState.r[p1] = outState.r[p0]
    outState.r.pop(p0, None)  # p0 is no longer used
    return outState


def brmem2reg(q0: Register,
              pp0: Register,
              inState: State) -> State:
    """
    m1, q0 = brmem2reg pp0, m0
    """
    if (q0 in inState.r.keys() or
            pp0 not in inState.r.keys() or
            not inState.canMutBorrow(inState.ptrptrto(pp0))):
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    outState.r[q0] = outState.m[inState.r[pp0]]
    return outState


def brmem2reg_ro(q0: Register,
                 pp0: Register,
                 inState: State) -> State:
    """
    m1, q0 = brmem2reg_ro pp0, m0
    """
    if (q0 in inState.r.keys() or
            pp0 not in inState.r.keys() or
            not inState.canBorrow(inState.ptrptrto(pp0))):
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    outState.r[q0] = inState.ptrptrto(pp0)
    # ro borrow decrements ownership state of address
    outState.o[inState.r[q0]] -= 1
    return outState


def mvreg2mem(pp0: Register,
              p0: Register,
              inState: State) -> State:
    """
    m1 = mvreg2mem pp0, p0, m0
    """
    if (pp0 not in inState.r.keys() or
        p0 not in inState.r.keys() or
            not inState.canMove(inState.r[p0])):
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    outState.m[outState.r[pp0]] = outState.r[p0]
    # no need to update ownership since it is keyed by address
    outState.r.pop(p0, None)
    return outState


def mvmem2reg(p1: Register,
              pp0: Register,
              inState: State) -> State:
    """
    m1, p1 = mvmem2reg pp0, m0
    """
    if (pp0 not in inState.r.keys() or
        p1 in inState.r.keys() or
            not inState.canMove(inState.ptrptrto(pp0))):
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    outState.r[p1] = outState.m[inState.r[pp0]]
    # no need to update ownership since it is keyed by address
    return outState


def cpmem2reg(q0: Register,
              pp0: Register,
              inState: State) -> State:
    """
    m1, q0 = cpmem2reg_rw pp0, m0
    """
    # inState.r[pp0] need not be an owner
    if (pp0 not in inState.r.keys() or
            q0 in inState.r.keys() or
            not inState.canCopy(inState.ptrptrto(pp0))):
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    outState.r[q0] = outState.m[inState.r[pp0]]
    # copy increments ownership state of address
    outState.o[outState.ptrptrto(pp0)] += 1
    return outState


def cpreg2mem(q0: Register,
              pp0: Register,
              p0: Register,
              inState: State) -> State:
    """
    m1, q0 = cpreg2mem pp0, p0,  m0
    """
    if (p0 not in inState.r.keys() or
        pp0 not in inState.r.keys() or
            not inState.canCopy(inState.r[p0])):
        return inState
    outState = copy.deepcopy(inState)
    outState.pc = outState.pc + 1
    outState.r[q0] = outState.r[p0]
    outState.m[outState.r[pp0]] = outState.r[p0]
    # copy increments ownership state of address
    outState.o[outState.r[p0]] += 1
    return outState
