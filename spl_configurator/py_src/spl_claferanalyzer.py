from xml_parser_helper import load_xml_model

_namespaces = {'c1': 'http://clafer.org/ir', 
     'xsi': 'http://www.w3.org/2001/XMLSchema-instance'}

class SPL_ClaferAnalyzer():
    def __init__(self, feature_model_xml_filename):
        self.xml_model = load_xml_model(feature_model_xml_filename)
        self.SPL = self.get_top_level_SPL_model()
        self.non_functional_properties =  self.compute_nonfunctional_properties()
        assert self.SPL != None

    def get_top_level_SPL_model(self):
        top_level_spl_model = None
        
        assert len (self.xml_model.findall('./c1:Declaration', namespaces=_namespaces)) > 0
        
        for top_level_clafer in self.xml_model.findall('./c1:Declaration', namespaces=_namespaces):
            if top_level_spl_model == None and \
            top_level_clafer.find('c1:IsAbstract', namespaces=_namespaces).text == 'true' \
            and  top_level_clafer.find('c1:Id',namespaces=_namespaces).text != 'IMeasurable':
                top_level_spl_model = top_level_clafer
                
        return top_level_spl_model
    
    def get_clafer_Id(self, element):
        return element.find('c1:Id',namespaces=_namespaces).text

    def get_clafer_UniqueId(self, element):
        return element.find('c1:UniqueId',namespaces=_namespaces).text

    def compute_nonfunctional_properties(self):
        top_level_clafers = self.xml_model.findall('./c1:Declaration', namespaces=_namespaces)
        
        non_functional_properties = {}
        
        
        IMeasurableClafers = [clafer for clafer in top_level_clafers if  \
                              clafer.find('c1:IsAbstract', namespaces=_namespaces) !=None and \
                              clafer.find('c1:IsAbstract', namespaces=_namespaces).text == 'true' and 
                              clafer.find('c1:Id',namespaces=_namespaces).text == 'IMeasurable' ][0]
        
        for nonfunctional_property in IMeasurableClafers.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces):
            non_functional_properties[self.get_clafer_Id(nonfunctional_property)] = self.get_clafer_UniqueId(nonfunctional_property)
            
        return non_functional_properties 

    def get_non_functional_properties_listing(self):
        return self.non_functional_properties.keys()
    
    def get_non_functional_property_unique_id(self, non_functional_property):
        return self.non_functional_properties.get(non_functional_property)
                
    def extract_integer(self, element):
        """
        Extracts an integer from the second argument for the constraint of form [this.property = <number>]  or [this.property = - <number>]
        
        E.g Element must be either -<number> or just <number>.
        """
        extacted_integer = 10
        if element.find("c1:Exp[@xsi:type='cl:IFunctionExp']/c1:Operation", namespaces=_namespaces)!=None and \
            element.find("c1:Exp[@xsi:type='cl:IFunctionExp']/c1:Operation", namespaces=_namespaces).text =='-':
                # we have this.footprint = - <number>
                extacted_integer = '-' + element.find("c1:Exp[@xsi:type='cl:IFunctionExp']/c1:Argument/c1:Exp/c1:IntLiteral", namespaces=_namespaces).text
        else:
            # we have just <number>
            extacted_integer = element.find("c1:Exp/c1:IntLiteral", namespaces=_namespaces).text
        return extacted_integer


    def get_property_value(self, element, property):
        property_val = 0
        for constraint in element.findall("./c1:Declaration[@xsi:type='cl:IConstraint']", namespaces=_namespaces):
            constraint_operation = constraint.find("c1:ParentExp/c1:Exp[@xsi:type='cl:IFunctionExp']/c1:Operation", namespaces=_namespaces)
            constraint_arguments = constraint.findall("c1:ParentExp/c1:Exp[@xsi:type='cl:IFunctionExp']/c1:Argument", namespaces=_namespaces)
    
            if constraint_operation != None and constraint_operation.text == '=' and  len(constraint_arguments)==2:
                first_argument =  constraint_arguments[0]
                second_argument = constraint_arguments[1]
    
                first_argument_sub_arguments = first_argument.findall("c1:Exp[@xsi:type='cl:IFunctionExp']/c1:Argument", namespaces=_namespaces)
                first_argument_sub_operation = first_argument.findall("c1:Exp[@xsi:type='cl:IFunctionExp']/c1:Operation", namespaces=_namespaces)                
                
                if len(first_argument_sub_arguments) == 2 and \
                    len(first_argument_sub_operation)>0 and  first_argument_sub_operation[0] != None and first_argument_sub_operation[0].text == '.' and \
                    \
                    first_argument_sub_arguments[0].find("c1:Exp[@xsi:type='cl:IClaferId']/c1:Id", namespaces=_namespaces) != None and \
                    first_argument_sub_arguments[0].find("c1:Exp[@xsi:type='cl:IClaferId']/c1:Id", namespaces=_namespaces).text == 'this' and \
                    \
                    first_argument_sub_arguments[1].find("c1:Exp[@xsi:type='cl:IClaferId']/c1:Id", namespaces=_namespaces) != None and \
                    first_argument_sub_arguments[1].find("c1:Exp[@xsi:type='cl:IClaferId']/c1:Id", namespaces=_namespaces).text == self.get_non_functional_property_unique_id(property)  and \
                    second_argument.find("c1:Type[@xsi:type='cl:IInteger']", namespaces=_namespaces)!= None:
                    
                        property_val = self.extract_integer(second_argument)
        return property_val

    def get_max_value_property(self):
            """
            Returns the maximum integer value for a nonfunctional in the Software Product Line Feature Model.
            """
            max_integer = 0
            for feature in self.get_features_as_xml_elements():
                for nonfunctional_property in self.get_non_functional_properties_listing():
                    nonfunctional_property_value = self.get_property_value(feature, nonfunctional_property)
                                                
                    max_integer = max_integer + max(int(nonfunctional_property_value), 0)
            return max_integer
        
    def get_features_as_xml_elements(self):
        return [feature for feature in self.SPL.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces) if \
            self.get_clafer_Id(feature) not in  ["total_%s" % nonfunctional_property for nonfunctional_property  in self.get_non_functional_properties_listing()]]         
        
    def get_set_extra_integers_from_feature_model(self):
        """
        Returns a set of all integers that are not referenced in the feature model, but that might be
        needed to represent the quality properties of a configuration of the feature model.
        """
        from collections import Counter
        
        bag_integers_in_spl_model = Counter()
        for clafer_features in self.get_features_as_xml_elements():
                # Eg add the integer to the bag.
            for nonfunctional_property in self.get_non_functional_properties_listing():                        
                bag_integers_in_spl_model.update([int(self.get_property_value(clafer_features, nonfunctional_property))])
        
        set_integers_derived_from_spl_model = set()
        
        for feature_number in bag_integers_in_spl_model.elements(): # expand the bag (e.g BAG = {1, 1 , 1, 2} expands to 1,1,1,2 .
            tmp_numbers_to_add = set()
            for existing_numbers in set_integers_derived_from_spl_model:
                tmp_numbers_to_add.add(existing_numbers + feature_number)
            tmp_numbers_to_add.add(feature_number)
            # For each number of the bag x, 
            #     set_integers_derived_from_spl_model += x + each element of  set_integers_derived_from_spl_model .
            set_integers_derived_from_spl_model.update(tmp_numbers_to_add)
    
        return set_integers_derived_from_spl_model.difference(set(bag_integers_in_spl_model))
    
