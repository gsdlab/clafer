import argparse
from xml.etree import ElementTree

from xml_parser_helper import load_xml_model
from splconqueror_analyzer import get_parent_element, \
get_parent_id, compute_tab_level, has_siblings_constraints, \
get_mandatory_base_features, compute_is_optional, get_fully_qualified_name, \
compute_group_cardinality, get_footprint, set_List_Mandatory_Base_Features, get_List_Mandatory_Base_Features

def print_abstract_IMeasurable(args):
	print "// Adapated from Scalable Prediction of Non-functional Properties in Software Product Lines."
	print "// Scaled down by dividing numbers by %s and rounding." % args.scaledownby
	print "//To execute in alloy: run  show for ..."
	print "\n"
	print "abstract IMeasurable"
	print "\tfootprint : integer\n\n"


def execute_main():

	parser = argparse.ArgumentParser(description='Reads an xml model of a Software Product Line generated for the tool SPLConqueror and generate a clafer model.')
	
	parser.add_argument('--scaledownby', type=int, default=1, help='Scaled the footprint by SCALEDOWNBY.')
	
	parser.add_argument('feature_model_xml_filename', metavar='F', type=str, nargs=1,
	                   help='SPLConqeuror Feature model in xml file to open.')
	
	parser.add_argument('feature_nonfunctional_properties_xml_filename', metavar='NF', type=str, nargs=1,
	                   help='SPLConqueror xml file with non functional  model of the software product line.')
	
	parser.add_argument('--fabricatebasefeature', type=str, default='',
	                   help='Fabricate a Base feature, in case there are no required features. It requires to be given a SPLConqueror XML file with detailed measurements of configurations (e.g configurations.xml)  of the software product line.')
	
	parser.add_argument('--clear_repeated_base_values', action='store_true',
						help='When there is more than one feature that is always required and they all have the same footprint, then clear all to zero except the first one.')
	
	args = parser.parse_args()
	
	
	print_abstract_IMeasurable(args)
	
	 
	xml_model = load_xml_model(args.feature_model_xml_filename[0])
	xml_model_nfp = load_xml_model(args.feature_nonfunctional_properties_xml_filename[0])
	
	if args.fabricatebasefeature != '':
		xml_model_configurations = load_xml_model(args.fabricatebasefeature)
	
	tab_dictionary = {}
	Constraint_Summation = []
	
	
	List_Mandatory_Base_Features = get_mandatory_base_features(xml_model)
	set_List_Mandatory_Base_Features(List_Mandatory_Base_Features)
	
	
	print "abstract %s" % xml_model.get('name')
	
	features_and_code_units = xml_model.findall("element[@type='feature']")
	features_and_code_units.extend(xml_model.findall("element[@type='code unit']") )
	features_and_code_units = sorted(features_and_code_units, key=lambda element: int(element.get('id')))
	
	for featureelement in features_and_code_units:
		# Got Indentation level.
		num_tabs = compute_tab_level(tab_dictionary, featureelement)
	
		group_cardinality, is_exclusive_or_partial, is_or_partial  =  compute_group_cardinality(xml_model, featureelement)
		is_optional = compute_is_optional(featureelement)
		
	
		for tmp in range(num_tabs): print "\t",
		print "%s%s : IMeasurable %s" % (group_cardinality, featureelement.get('name').replace("=","_EQ_"), is_optional)
	
		
		# Print any exlcudes constraint.
		for excludes_ref  in featureelement.findall("constraints/constraint[@type='excludes']/constraint_element"):
			for tmp in range(num_tabs): print "\t",
			print "\t[ !%s ]" % ( excludes_ref.find('name').text,)
	
		# TODO Print any requires constraint.
		all_requires_constraint = featureelement.findall("constraints/constraint[@type='requires']/constraint_element")
		if all_requires_constraint != []:
			for tmp in range(num_tabs): print "\t",
			print "\t[ %s ]" %  ' && '.join([constraint_requires.find('name').text for constraint_requires  in  all_requires_constraint])
	
		
		# Print footprint, for now just print [this.footprint = 0].
		for tmp in range(num_tabs): print "\t",
		footprint = get_footprint(xml_model_nfp, featureelement, args)
			
		print "\t[ this.footprint = %s]" %  footprint 
	
		# Add to the list of required summations.	
		Constraint_Summation.append( get_fully_qualified_name(xml_model,featureelement)  + '.footprint')
			
		
	if args.fabricatebasefeature != '' and len(get_mandatory_base_features(xml_model))==0:
		
		print "\tSYNTETHIC_BASE_FEATURE : IMeasurable"
		print "\t\t [ this.footprint = %s ]" % get_empty_features_footprint(xml_model_configurations)
		
	print "\ttotal_footprint : integer"
	print "\t[ total_footprint = %s ]" % ' + '.join(Constraint_Summation)
	
	print "\nsimpleConfig : %s " % xml_model.get('name')
	
	
	print "\n\n//Mandatory Features all configurations will have: %s " %  str(' '.join([x.get('name') for x in get_mandatory_base_features(xml_model)]))


execute_main()