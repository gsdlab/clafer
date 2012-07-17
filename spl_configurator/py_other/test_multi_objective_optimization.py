import unittest
from xml_parser_helper import load_xml_model
import spl_claferanalyzer

class TestSPL_ClaferAnalyzer(unittest.TestCase):

    def setUp(self):
        self.spl_transformer = spl_claferanalyzer.SPL_ClaferAnalyzer("../unit_test_data/telematics_multi_objective_optimization.xml")
        
        
    def test_load_xml_model(self):
        self.assertTrue(self.spl_transformer.xml_model != None)

    def test_get_top_level_SPL_model(self):        
        self.assertTrue(self.spl_transformer.SPL != None)

    def test_compute_nonfunctional_properties(self):
        self.assertIn("cost", self.spl_transformer.get_non_functional_properties_listing(), "cost was parsed as nonfunctional property.")
        self.assertIn("mass", self.spl_transformer.get_non_functional_properties_listing(), "mass was parsed as nonfunctional property.")
        
    def test_get_max_value_property(self):
        max_integer =   self.spl_transformer.get_max_value_property()

        self.assertEqual(max_integer, 37, "The maximum possible integer should be 37 in telematics test case, got %s " % max_integer)

    def test_get_features_as_xml_elements(self):
        features_xml_elements = self.spl_transformer.get_features_as_xml_elements()
        self.assertSetEqual(set(["channel", "single", "dual","extraDisplay"]), set([self.spl_transformer.get_clafer_Id(x) for x in features_xml_elements]), "Should show exactly all features.")
        
    def test_get_set_extra_integers_from_feature_model(self):
        set_extra_integers = self.spl_transformer.get_set_extra_integers_from_feature_model()
        print set_extra_integers
        self.assertGreater(len(set_extra_integers), 1, "At least one integer in set of integers.")

if __name__ == '__main__':
    unittest.main()
