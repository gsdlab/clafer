import argparse
from xml.etree import ElementTree

from xml_parser_helper import load_xml_model

from splconqueror_analyzer import get_features_and_code_units


def execute_main():

	parser = argparse.ArgumentParser(description='Reads an xml model of a Software Product Line generated for the tool SPLConqueror and generate a clafer model.')
	
	parser.add_argument('--property', type=str, default="footprint", help='Function property to annotate feature model with')
	
	parser.add_argument('feature_model_xml_filename', metavar='F', type=str, nargs=1,
	                   help='SPLConqeuror Feature model in xml.')
	
	parser.add_argument('measurment_results_xml_filename', metavar='MR', type=str, nargs=1,
	                   help='SPLConqueror xml file with quality properties feature values.')
	
	args = parser.parse_args()
		
	xml_model = load_xml_model(args.feature_model_xml_filename[0])
	xml_model_measurementresuelt = load_xml_model(args.measurment_results_xml_filename[0])
	
	featureValues = {}
	for row in xml_model_measurementresuelt.findall('row'):
		featureValues[row.find("data[@columnname='Name']").text] = row.find("data[@columnname='Value']").text.replace(",", ".")

	for feature in get_features_and_code_units(xml_model):
		print "\t<%s id=\"%s\">" %  ( feature.get('name'), feature.get('id'))
		print "\t\t<clearedValue>%s</clearedValue>" % featureValues.get(feature.get('name'), 0)
		print "\t</%s>" % feature.get('name')

	print "</measured_values>"

execute_main()
