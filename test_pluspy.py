import pluspy
import unittest


class TestLexer(unittest.TestCase):
    def test_ignore_preamble(self):
        cases = [
            {
                "name": "preamble",
                "input": '''
                         This is some prose preceding the module definition.
   
                         \* WORKAROUND: Comment prose before the module definition.
                         
                         ---- MODULE AsyncGameOfLifeDistributed -----
                         
                         VARIABLE x
                         Spec == x = TRUE /\ [][x'\in BOOLEAN]_x
                         ====
                         ''',
            },
            {
                "name": "preamble with four dashes",
                "input": '''
                         ---- What is this 
    
                         \* A comment 
                         
                         And more preamble there is.
                         
                         ------------------------------- MODULE Somename -------------------------------
                         ''',
            },
            {
                "name": "preamble with commented module",
                "input": ''''
                         ---- What is this 
        
                         \* A comment  
                         \* ---- MODULE foo ---- 
                         And more preamble there is. 
                          
                         -------------------------------  MODULE Foo -------------------------------
                          
                          
                         ================================ =============================================
                '''
            },
        ]

        for case in cases:
            results = pluspy.lexer(case["input"], "nofile.tla")
            a, b, _, d = results[0], results[1], results[2], results[3]
            self.assertEqual(
                "----", pluspy.lexeme(a),
                "failed test {} expected {}, actual {}".format(
                    case["name"], "----", a
                ),
            )
            self.assertEqual(
                "MODULE", pluspy.lexeme(b),
                "failed test {} expected {}, actual {}".format(
                    case["name"], "MODULE", b
                ),
            )
            self.assertEqual(
                "----", pluspy.lexeme(d),
                "failed test {} expected {}, actual {}".format(
                    case["name"], "----", a
                ),
            )


