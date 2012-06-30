import unittest
from xml_parser_helper import load_xml_model
import spl_claferanalyzer

class TestSpl_claferanalyzer(unittest.TestCase):

    def setUp(self):
        self.xml_model = load_xml_model("../unit_test_data/telematics_multi_objective_optimization.xml")
        self.SPL = spl_claferanalyzer.get_top_level_SPL_model(self.xml_model)
    
    def test_load_xml_model(self):
        self.assertTrue(self.xml_model != None)

    def test_get_top_level_SPL_model(self):        
        self.assertTrue(self.SPL != None)

    def test_get_max_value_property(self):
        max_integer =   spl_claferanalyzer.get_max_value_property(self.SPL, ["cost", "mass"])
        self.assertEqual(max_integer, 37, "The maximum possible integer should be 37 in telematics test case, got %s " % max_integer)



if __name__ == '__main__':
    unittest.main()
