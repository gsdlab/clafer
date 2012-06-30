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

    parser.add_argument('--property', type=str, default="footprint", help='Quality property to reason about, by default it uses footprint.')
            
    parser.add_argument('--alloy4compatible', default=False, action="store_true", 
                        dest="alloy4compatible",  help='Generate partial instance block compatible with alloy4 which uses int instead of Int.')
    
    parser.add_argument('--sparseintegers', default=False, action="store_true", 
                        dest="sparseintegers",  help="Use support for partial integers, and hence don't specify bitwidth.")
       
    args = parser.parse_args()
        
    xml_model = load_xml_model(args.clafer_feature_model_xml_filename[0])

    SPL = spl_claferanalyzer.get_top_level_SPL_model(xml_model)
    
    assert SPL != None # check SPL is correctly parsed by  spl_claferanalyzer.get_top_level_SPL_model(xml_model)

    if  args.sparseintegers == True:
        print "sig bag_extra_ints{"
        print "  extra_ints : set Int"
        print "}"
        
        

    print "inst partial_speedup {"
    print "    1"


    args.property = ["cost", "mass"]
    
    # Compute the maximum bit width for integers, first compute the highest possible 
    max_integer =   spl_claferanalyzer.get_max_value_property(SPL, args.property)
    
    #print "MAX_INTEGER = %s " % max_integer 
    
    # Compute Bitwidth, we have to add 1 to max_integer due to "0", and 1 to the total due to negative numbers.
    max_bitwidth = math.ceil(math.log(max_integer+1, 2)) + 1         

    if args.sparseintegers == True:
        extra_integers = spl_claferanalyzer.get_set_extra_integers_from_feature_model(SPL, args.property)        
        print "    ,bag_extra_ints = concrete_int_bag"
        print "    , extra_ints = ",
        print ' + '.join(["concrete_int_bag -> %s " % (extra_integer,)  for extra_integer in extra_integers])
    else:            
        if args.alloy4compatible == True:
            # In allyo4 we must use small int to set bitwidth.
            print "    , %s  int" % max(4, int(max_bitwidth))
        else:
            # In allyo4.2 we must use large Int to set bitwidth, "int" is no longer a keyword nor allowed, only "Int".
            print "    , %s  Int" % max(4, int(max_bitwidth))
    
    # Print partial instances of individual features, children of IMeasurable.
    for clafer_features in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces):
        if spl_claferanalyzer.get_clafer_Id(clafer_features)!=('total_%s' % args.property):
            print "   , %s in partial_%s" %  (spl_claferanalyzer.get_clafer_UniqueId(clafer_features), spl_claferanalyzer.get_clafer_UniqueId(clafer_features) )    
    footprint_clafer = [x for x in xml_model.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces) if spl_claferanalyzer.get_clafer_Id(x) == args.property][0]
    
    
    # Print footprint for specific Element.
    print "    ,  %s in " % spl_claferanalyzer.get_clafer_UniqueId(footprint_clafer), 
    list_of_IMeasurableChildren = []
    for clafer_features in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces):
        if spl_claferanalyzer.get_clafer_Id(clafer_features)!= ('total_%s'%args.property):
            list_of_IMeasurableChildren.append("%s_for_%s_of_%s" % (args.property,spl_claferanalyzer.get_clafer_UniqueId(clafer_features), spl_claferanalyzer.get_property(clafer_features, args.property).replace('-', 'minus') )  )
    print ' + '.join(list_of_IMeasurableChildren)

    
    # Print Feature  to specific  footprint   relation.
    print '    , r_%s in ' % spl_claferanalyzer.get_clafer_UniqueId(footprint_clafer), 
    print ' + '.join([ "partial_%s->%s_for_%s_of_%s" % (spl_claferanalyzer.get_clafer_UniqueId(clafer_features),args.property, spl_claferanalyzer.get_clafer_UniqueId(clafer_features) , spl_claferanalyzer.get_property(clafer_features, args.property).replace('-', 'minus') )   \
                 for clafer_features in \
                 [x for x in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces) if spl_claferanalyzer.get_clafer_Id(x)!=('total_%s'  % args.property) ]])

    # Print Footprint  to specific  number   relation.
    print '    , %s_ref in ' % spl_claferanalyzer.get_clafer_UniqueId(footprint_clafer), 
    print ' + '.join([ "%s_for_%s_of_%s-> %s" % ( args.property ,spl_claferanalyzer.get_clafer_UniqueId(clafer_features) , spl_claferanalyzer.get_property(clafer_features, args.property).replace('-', 'minus'),  spl_claferanalyzer.get_property(clafer_features, args.property) )   \
                 for clafer_features in \
                 [x for x in SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces) if spl_claferanalyzer.get_clafer_Id(x)!=('total_%s' % args.property)]])

    
    print "}"

    print "run show for partial_speedup optimize o_global"

execute_main()
