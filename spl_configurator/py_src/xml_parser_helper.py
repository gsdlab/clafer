
from xml.etree import ElementTree

def load_xml_model(filename):
    xml_model_string = ''.join( open(filename).readlines())
    return ElementTree.fromstring(xml_model_string)