_namespaces = {'c1': 'http://gsd.uwaterloo.ca/clafer', 'xsi': 'http://www.w3.org/2001/XMLSchema-instance'}

def get_clafer_Id(element):
    return element.find('c1:Id',namespaces=_namespaces).text
def get_clafer_UniqueId(element):
    return element.find('c1:UniqueId',namespaces=_namespaces).text
        
def get_top_level_SPL_model(xml_model):
    top_level_spl_model = None
    for top_level_clafer in xml_model.findall('./c1:Declaration', namespaces=_namespaces):
        if top_level_spl_model == None and \
        top_level_clafer.find('c1:IsAbstract', namespaces=_namespaces).text == 'true' \
        and  top_level_clafer.find('c1:Id',namespaces=_namespaces).text != 'IMeasurable':
            top_level_spl_model = top_level_clafer
            
    return top_level_spl_model

def get_parent_element(xml_model, current_element):
    """
    Get a Reference to current_element  parent  or None if it has no parent.
    """
    pass
def get_parent_id(current_element):
    pass


def compute_tab_level(tab_dictionary, current_element):
    pass

def has_siblings_constraints(feature_element):
    """
    Tells you whether a given feature has alternative and/or commutative constraints.
    """
    pass

def get_mandatory_base_features(xml_model, SPLModelName):
    """
    Get the set of all features that in any configuration will have to be included
    """
    print xml_model.find()

def compute_is_optional(current_element):
    pass

def get_fully_qualified_name(xml_model, current_element):
    """
    Get the fully qualified name for a given element. (e.g a path from root joined by . finalizing with the element).
    """
    pass

def compute_group_cardinality(xml_model, current_element):
    pass

def extract_integer(element):
    """
    Extracts an integer from the second argument for the constraint of form [this.footprint = <number>]  or [this.footprint = - <number>]
    
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


def get_property(element, property="footprint"):
    footprint_val = 0
    
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
                first_argument_sub_arguments[0].find("c1:Exp[@xsi:type='cl:IClaferId']/c1:Id", namespaces=_namespaces) != None and \
                first_argument_sub_arguments[0].find("c1:Exp[@xsi:type='cl:IClaferId']/c1:Id", namespaces=_namespaces).text == 'this' and \
                first_argument_sub_arguments[1].find("c1:Exp[@xsi:type='cl:IClaferId']/c1:Id", namespaces=_namespaces) != None and \
                first_argument_sub_arguments[1].find("c1:Exp[@xsi:type='cl:IClaferId']/c1:Id", namespaces=_namespaces).text == ('c2_%s' % property)  and \
                second_argument.find("c1:Type[@xsi:type='cl:IInteger']", namespaces=_namespaces)!= None:
                
                    footprint_val = extract_integer(second_argument)
    return footprint_val

def get_empty_features_footprint(xml_model_configurations, args):
    pass



def get_max_value_property(SPL_Model, property):
        """
        Returns the maximum integer value  for a nonfunctional in the Software Product Line Feature Model.
        """
        max_integer = 0
        for clafer_features in SPL_Model.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces):
            if get_clafer_Id(clafer_features)!=  ("total_%s" % property):
                max_integer = max_integer + max(int(get_property(clafer_features, property)), 0)
        return max_integer
def get_set_extra_integers_from_feature_model(SPL_Model, property):
    """
    Returns a set of all integers that are not referenced in the feature model, but that might be
    needed to represent the quality properties of a configuration of the feature model.
    """
    from collections import Counter
    
    bag_integers_in_spl_model = Counter()
    for clafer_features in SPL_Model.findall(".//c1:Declaration[@xsi:type='cl:IClafer']", namespaces=_namespaces):
        if get_clafer_Id(clafer_features)!=  ("total_%s" % property):    
            # Eg add the integer to the bag.
            bag_integers_in_spl_model.update([int(get_property(clafer_features, property))])
    
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
    
