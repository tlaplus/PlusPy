# pluspy

pluspy is a TLA+ interpreter, written in Python.

Run "./pluspy -h" for basic help.  The output should be something like:

    Usage: pluspy [options] [module]
      options: 
        -c cnt: #times that Next should be evaluated
        -h: help
        -i: Init operator (default Init)
        -n: Next operator (default Next)
        -P path: module directory search path
        -s: silent output
        -S seed: random seed for reproducible tests
        -v: verbose output

You can also invoke pluspy with "-i Spec" where Spec is a full TLA+
specification.  Try for example "./pluspy -i Spec Prime", which
should print the prime numbers.

pluspy is a Bash shell script.  If you can't run it, try "python3 pluspy.py"
instead.

-------- EXAMPLE 1: HourClock --------

Run "./pluspy -c2 HourClock"

The output should be something like:

    Initial context: [ hr: 6 ]
    Next state: 0 [ hr: 7 ]
    Next state: 1 [ hr: 8 ]
    MAIN DONE

You can find the HourClock module in modules/book/HourClock.tla.
The interpreter shows three "contexts", which are assignments of
constants and variables to values.  It first shows the "Initial
context," computed by the "Init" operator in HourClock.tla.  (The
initial value of hr is a random number between 1 and 12.)  Then it
shows two more contexts computed by the "Next" operator in
HourClock.tla.  The number of steps can be controlled with the "-c"
option to pluspy.

You should be able to run Peterson.tla, Prime.tla, and Qsort.tla in
much the same way, but try larger -c counts for those.

-------- EXAMPLE 2: Threads --------

The Peterson module has multiple processes.  PlusPy can run each as
a separate thread.  Run: "./pluspy -c100 -n proc%0 -n proc%1 Peterson".
"proc" is an operator in the Peterson module that takes an argument.
The "-n x%y" argument to pluspy starts a thread that repeatedly evaluates
the x operator with argument y instead of the default "Next".  You may
also want to try: "./pluspy -c100 -n proc%0 Peterson" and 
./pluspy -c100 -n proc%1 Peterson" which each will run just one of the
processes.

Using the new JWait/JSignalReturn interfaces in TLC, threads can use
condition variables.  See modules/other/BoundedQueueSplit.tla for an
example.  Run as follows:

    ./pluspy -n producer%p1 -c100 -n producer%p2 -n producer%p3 \
                -n consumer%c1 -n consumer%c2 -n consumer%c3 TestBQ

(This won't work if you try to run this without threads.)

-------- EXAMPLE 3: Sending and Receiving Messages --------

Open three windows.  Run the following commands, one in each of the windows:

    ./pluspy -c100 -n Proc%localhost:5001 TestBinBosco
    ./pluspy -c100 -n Proc%localhost:5002 TestBinBosco
    ./pluspy -c100 -n Proc%localhost:5003 TestBinBosco

The Proc action takes one argument, the process identifier,

The processes will actually send and receive messages, trying to
solve consensus.  Although BinBosco has no rule to actually decide,
in all likelihood they will each end up with the same estimate after
about five rounds.  Only three of the four processes can do so.  You
can inspect the output and see the state of each of the processes
and the set Messages.  The "processes" variable of localhost:5001
should contain something like the following in the end:

    [
        "localhost:5001" |-> [ estimate |-> "red",  round |-> 5 ],
        "localhost:5002" |-> [ estimate |-> "blue", round |-> 0 ],
        "localhost:5003" |-> [ estimate |-> "red",  round |-> 0 ],
        "localhost:5004" |-> [ estimate |-> "blue", round |-> 0 ]
    ]

Similarly, the "processes" variable of localhost:5002 might contain:

    [
        "localhost:5001" |-> [ estimate |-> "red",  round |-> 0 ],
        "localhost:5002" |-> [ estimate |-> "red",  round |-> 5 ],
        "localhost:5003" |-> [ estimate |-> "red",  round |-> 0 ],
        "localhost:5004" |-> [ estimate |-> "blue", round |-> 0 ]
    ]

Note that all processes end up with the same estimate, probably
around round 5.  Running BinBosco this way is a little odd, as each
pluspy process only updates part of what is really supposed to be
a global state.  You can imagine there being a refinement mapping
to the virtual global state, where the local state of TLA+ process
i in pluspy process i maps to the state of TLA+ process i in the
global state.

Messaging is specified in the modules/lib/Messaging.tla module.
Besides the message interface variable mi, there are the following
three operators exported:

    Init                        \* initializes mi
    Send(msgs)                  \* sends the given << destination, payload >> messages
    Receive(p, Deliver(_, _))   \* wait for a message for p and call Deliver(p, payload)

The spec proper is specified after the comment "\*++:SPEC".  If you look further
you'll find a second comment "\*++:PlusPy".  This is where the implementation of
the messaging module starts.  It uses the IO module described below.

-------- The IO module --------

PlusPy exports a module in modules/lib/IO.tla that allows processes to do various
kinds of I/O.  There are currently three kinds of interfaces defined: "fd", "tcp",
and "local".  For "fd", there are three muxes: "stdin", "stdout", and "stderr".
For example IOPut("fd", "stdout", "hello") prints hello.  Note that all I/O is
"deferred": it is only performed if the action in which it occurs evaluates to TRUE.

The modules/lib/Input.tla module shows how one can read from standard input.
The Input.tla module is "pure TLA+" -- it has no implied variable.  It also
provides an example of the "\*++:SPEC" and "\*++:PlusPy" sections.

To send and receive TCP messages, use the "tcp" interface and use as "mux" a
TCP/IP address of the form "x.x.x.x:port".

The "local" interface is a little like the IP loopback interface.  It allows
sending messages to self.

-------- TLA+ value representations in Python --------

The basic values are booleans, numbers, and strings:

    FALSE:      False
    TRUE:       True
    number:     number
    string:     string

TLA+ sets are represented as Python frozensets,  A frozenset is like
a Python set but is hashable because it cannot be modified.

Essentially, a tuple is represented as a tuple, and a record as a
pluspy.FrozenDict.

However, to ensure that equal values have the same representation,
records that are tuples (because their keys are in the range 1..len)
are represented as tuples, and tuples that are strings (because all
their elements are characters) are represented as strings.  In
particular, empty records and tuples are represented as the empty
string.

There is also a "Nonce" type for "CHOOSE x: x \notin S" expressions.

Note that in Python False == 0 and True == 1.  This can lead to
weird behaviors.

For example, { False, 0 } == { False } == { 0 } == { 0, False }.

-------- PlusPy Module --------
PlusPy can also be used as a Python module, so you integrate Python and
TLA+ programs quite easily.  The interface is as follows:

    pp = pluspy.PlusPy(module, constants={})
        'module' is a string containing either a file name or the
        name of a TLA+ module.  Constants is a dictionary that maps
        constant names to values (see TLA+ value represenations.)

    pp.init(Init)
        'Init' is a string containing the name of the 'init' operator
        in the TLA+ formula: "Spec == Init /\ [][Next]".  You can also
        pass the "Spec" operator, but it will not give back control
        until "Next" evaluates to FALSE.  Also, does not implement
        environment variables at the moment.

    pp.next(Next, arg=None)
        'Next' is a string containing the name of the 'Next' operator
        in the TLA+ formula: "Spec == Init /\ [][Next]".  If Next takes
        an argument, "arg" contains its value.  It returns True if some
        action was enabled and False if no action was enabled.  Typically
        pp.next() is called within a loop.  Interface state variables
        can be changed in the loop if desired.

    pp.unchanged()
        Checks to see if the state has changed after pp.next()

    value = pp.get(variable)
        "variable" is a string containing the name of a variable.  Its
        value is returned.  For the representation of TLA+ values, see
        below.

    value = pp.getall():
        returns a single record value containing all variables

    pp.set(variable, value)
        "variable" is a string containing the name of a variable.  Its
        value is set to "value".  For the representation of TLA+ values,
        see below.

    v = pluspy.format(v):
        Convert a value to a string formatted in TLA+ format

    v = pluspy.convert(v):
        Convert a value to something a little more normal and better for
        handling in Python.  In particular, it turns records into dictionaries,
        and frozensets into lists

-------- PlusPy Wrappers --------

PlusPy allows operators in specified modules to be replaced by Python
code.  You can specify this in the pluspy.wrappers variable.  For example:

    class LenWrapper(pluspy.Wrapper):
        def eval(self, id, args):
            assert id == "Len"
            assert len(args) == 1
            return len(args[0])

    pluspy.wrappers["Sequences"] = {
        "Len": LenWrapper()
    }

The IO module is implemented using a wrapper.

-------- Discussion of interfacing between Python and TLA+ --------

PlusPy allows TLA+ and Python to interface in a variety of ways, as demonstrated
above.  It is important to try to avoid ad hoc solutions.  The Messaging and Input
modules provide a clean separation between the TLA+ world and the Python world.
They can be used with the TLC model checker or TLAPS to validate your code.  The
IO module is outside the TLA+ world, so if you extend it, try to do it through a
module that has clean semantics.

Similarly, while it is possible to invoke operators other than "Spec" directly from
Python, and while it is possible to write state variables directly from Python, this
circumvents the TLA+ framework.  Use caution.
