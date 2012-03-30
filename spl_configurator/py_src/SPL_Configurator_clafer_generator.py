import argparse
from xml.etree import ElementTree

from xml_parser_helper import load_xml_model
import spl_claferanalyzer
import math

_namespaces = {'c1': 'http://gsd.uwaterloo.ca/clafer', 'xsi': 'http://www.w3.org/2001/XMLSchema-instance'}


def execute_main():

    parser = argparse.ArgumentParser(description='Reads an XML file of a feature tree created in for a Software Product and generates the required alloy partial instance block to speed up analysis  for this model.')
        
    parser.add_argument('clafer_feature_model_xml_filename', metavar='F', type=str, nargs=1,
                       help='XML file of Software Product Line feature model in clafer to open.')
        
    args = parser.parse_args()
        
    xml_model = load_xml_model(args.clafer_feature_model_xml_filename[0])

    SPL = spl_claferanalyzer.get_top_level_SPL_model(xml_model)
    
    print "inst partial_speedup {"
    print "    1"
    
    # Compute the maximum bit width for integers, first compute the highest possible 
    max_integer = 0
    for clafer_features in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces):
        if spl_claferanalyzer.get_clafer_Id(clafer_features)!='total_footprint':
            max_integer = max_integer + max(int(spl_claferanalyzer.get_footprint(clafer_features)), 0)

    # Compute Bidwithd, we have to add 1 to max_integer due to "0", and 1 to the total due to negative numbers.
    max_bitwidth = math.ceil(math.log(max_integer+1, 2)) + 1 
    
    
    print "    , %s  int" % max(4, int(max_bitwidth))
    
    # Print partial instances of individual features, children of IMeasurable.
    for clafer_features in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces):
        if spl_claferanalyzer.get_clafer_Id(clafer_features)!='total_footprint':
            print "   , %s in partial_%s" %  (spl_claferanalyzer.get_clafer_UniqueId(clafer_features), spl_claferanalyzer.get_clafer_UniqueId(clafer_features) )    
    footprint_clafer = [x for x in xml_model.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces) if spl_claferanalyzer.get_clafer_Id(x) =='footprint'][0]
    
    
    # Print footprint for specific Element.
    print "    ,  %s in " % spl_claferanalyzer.get_clafer_UniqueId(footprint_clafer), 
    list_of_IMeasurableChildren = []
    for clafer_features in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces):
        if spl_claferanalyzer.get_clafer_Id(clafer_features)!='total_footprint':
            list_of_IMeasurableChildren.append("footprint_for_%s_of_%s" % (spl_claferanalyzer.get_clafer_UniqueId(clafer_features), spl_claferanalyzer.get_footprint(clafer_features).replace('-', 'minus') )  )
    print ' + '.join(list_of_IMeasurableChildren)

    
    # Print Feature  to specific  footprint   relation.
    print '    , r_%s in ' % spl_claferanalyzer.get_clafer_UniqueId(footprint_clafer), 
    print ' + '.join([ "partial_%s->footprint_for_%s_of_%s" % (spl_claferanalyzer.get_clafer_UniqueId(clafer_features), spl_claferanalyzer.get_clafer_UniqueId(clafer_features) , spl_claferanalyzer.get_footprint(clafer_features).replace('-', 'minus') )   \
                 for clafer_features in \
                 [x for x in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces) if spl_claferanalyzer.get_clafer_Id(x)!='total_footprint']])

    # Print Footprint  to specific  number   relation.
    print '    , %s_ref in ' % spl_claferanalyzer.get_clafer_UniqueId(footprint_clafer), 
    print ' + '.join([ "footprint_for_%s_of_%s-> %s" % ( spl_claferanalyzer.get_clafer_UniqueId(clafer_features) , spl_claferanalyzer.get_footprint(clafer_features).replace('-', 'minus'),  spl_claferanalyzer.get_footprint(clafer_features) )   \
                 for clafer_features in \
                 [x for x in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces) if spl_claferanalyzer.get_clafer_Id(x)!='total_footprint']])

    
    print "}"

    print "run show for partial_speedup"
execute_main()