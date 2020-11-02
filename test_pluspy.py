import pluspy
import unittest


class TestLexer(unittest.TestCase):
    def test_ignore_preamble(self):
        s = '''
        This is some prose preceding the module definition.

        \* WORKAROUND: Comment prose before the module definition.
        
        ---- MODULE AsyncGameOfLifeDistributed -----
        
        VARIABLE x
        Spec == x = TRUE /\ [][x'\in BOOLEAN]_x
        ====
        '''

        results = pluspy.lexer(s, "nofile.tla")
        assert pluspy.lexeme(results[0]) == "----"
