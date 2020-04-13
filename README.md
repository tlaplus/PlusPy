# pluspy

pluspy is a TLA+ interpreter, written in Python.

Run "./pluspy -h" for basic help.  The output should be something like:

	Usage: pluspy [options] [module]
	  options: 
		-c cnt: #times that Next should be evaluated
		-h: help
		-i: Init operator (default Init)
		-n: Next operator (default Next)
		-p: argument to Next operator
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
MAIN DONE None

The interpreter shows three "contexts", which are assignments of
constants and variables to values.  It first shows the "Initial
context," computed by the "Init" operator in HourClock.tla.  (The
initial value of hr is a random number between 1 and 12.)  Then it
shows two more contexts computed by the "Next" operator in
HourClock.tla.  The number of steps can be controlled with the "-c"
option to pluspy.

You should be able to run Peterson.tla and Prime.tla in much the
same way.

-------- EXAMPLE 2: TestBinBosco.tla --------

Looking at TestBinBosco.tla is instructive.  pluspy does not allow
the main module (argument to pluspy, or standard input if no argument
is given) to have constants.  TestBinBosco instantiates BinBosco
with arguments.  You should be able to run

    ./pluspy -c100 -plocalhost:5001 TestBinBosco

However, you should notice that pluspy does not terminate but hangs.

The -p argument specifies the TCP/IP address that pluspy uses.  By
specifying -p, the Messaging module is overridden by Python code that
actually sends messages over the network.  The reason pluspy hangs is
because it has started some threads that deal with messaging.

You can terminate pluspy by hitting <control>C.

-------- EXAMPLE 3: Sending and Receiving Messages --------

Open four windows.  Run the following commands, one in each of the windows:

	./pluspy -c100 -n Proc -p localhost:5001 TestBinBosco
	./pluspy -c100 -n Proc -p localhost:5002 TestBinBosco
	./pluspy -c100 -n Proc -p localhost:5003 TestBinBosco
	./pluspy -c100 -n Proc -p localhost:5004 TestBinBosco

The "-n" option tell pluspy not to evaluate the Next action, buth the
Proc action.  The Proc action takes one argument, the process identifier,
which is specified using the "-p" option.

The processes will actually send and receive messages, trying to solve
consensus.  Although BinBosco has no rule to actually decide, in all
likelihood they will each end up with the same estimate after about five
rounds.  Only three of the four processes can do so.  You can inspect
the output and see the state of each of the processes and the set Messages.

Running BinBosco this way is a little odd, as each pluspy only updates
part of what is really supposed to be a global state.

-------- TLA+ value representations in Python --------

The basic values are booleans, numbers, and strings:

	FALSE:		False
	TRUE:		True
	number:		number
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

-------- EXAMPLE 4: Osiris membership service --------

Open four windows.  Run the following commands, one in each of the windows:

	window A: python3 osiris.py -g localhost:5001
	window B: python3 osiris.py localhost:5002
	window C: python3 osiris.py localhost:5003
	window D: python3 osiris.py localhost:5004

The -g flag in window A starts the membership service with a single member
at TCP/IP address localhost:5001.  The others are just waiting.  Now type
"+localhost:5002" in window A.  This adds B to the membership.  You can
now type "+localhost:5003" in either window A or window B to add member C.
Now try typing "-localhost:5001" in one of the first three windows.  This
removes A from the membership.

Osiris uses Bosco.tla to run consensus.  It instantiates Bosco for each
membership.

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
