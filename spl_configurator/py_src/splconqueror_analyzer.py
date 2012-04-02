_List_Mandatory_Base_Features  = []
def set_List_Mandatory_Base_Features(List_Mandatory_Base_Features):
    global _List_Mandatory_Base_Features 
    _List_Mandatory_Base_Features = List_Mandatory_Base_Features
def get_List_Mandatory_Base_Features():
    return _List_Mandatory_Base_Features

    
def get_parent_element(xml_model, current_element):
    """
    Get a Reference to current_element  parent  or None if it has no parent.
    """
    if get_parent_id(current_element) == None:
        parent_element = None
    else:
        parent_element = xml_model.find(".//element[@id='%s']" % get_parent_id(current_element))
        
    return parent_element

def get_parent_id(current_element):
    parent_id_element = current_element.find('parentElement/id')
    if parent_id_element == None:
        parent_id = None
    else:
        parent_id = parent_id_element.text

    return parent_id


def compute_tab_level(tab_dictionary, current_element):
    parent_id = current_element.find('parentElement/id')
    if parent_id == None:
        num_tabs = 1
    else:
        num_tabs = 1 + tab_dictionary.get(parent_id.text)
    tab_dictionary[current_element.get('id')] = num_tabs
    return num_tabs


def has_siblings_constraints(feature_element):
    """
    Tells you whether a given feature has alternative and/or commutative constraints.
    """
    has_sibling_xor_constraints = feature_element.find("constraints/constraint[@type='alternative']/constraint_element")!= None
    has_sibling_or_constraints = feature_element.find("constraints/constraint[@type='alternative']/constraint_element")!= None
    
    return has_sibling_xor_constraints or has_sibling_or_constraints


def get_mandatory_base_features(xml_model):
    """
    Get the set of all features that in any configuration will have to be included
    """
    list_base_features = []
    for feature_element in xml_model.findall("element[@type='feature']"):
        if get_parent_element(xml_model, feature_element)==None and feature_element.get('optional')=='false':
            list_base_features.append(feature_element)
        elif feature_element.get('optional')=='false' and has_siblings_constraints(feature_element)==False:
            # Check to see if  its chain of ancestors are all mandatory as well.
            all_parents_mandatory = True

            parent_element = get_parent_element(xml_model, feature_element)
            
            if parent_element.get('optional')!='false' or has_siblings_constraints(parent_element)!=False:
                all_parents_mandatory = False
                            
            while (all_parents_mandatory == True and parent_element!=None and get_parent_element(xml_model, parent_element)!=None):
                parent_element = get_parent_element(xml_model, parent_element)!=None
                if parent_element.get('optional')!='false' or has_siblings_constraints(parent_element)!=False:
                    all_parents_mandatory = False

            if all_parents_mandatory == True:
                list_base_features.append(feature_element)
                
    return list_base_features

def compute_is_optional(current_element):
    if current_element.get('optional') == 'true':
        is_optional = " ?"
    else:
        is_optional = ""
    return is_optional


def get_fully_qualified_name(xml_model, current_element):
    """
    Get the fully qualified name for a given element. (e.g a path from root joined by . finalizing with the element).
    """
    tmp_element = current_element
    path_from_root = []
    while(get_parent_element(xml_model,tmp_element)!=None):
        path_from_root.append(get_parent_element(xml_model,tmp_element).get('name'))
        tmp_element = get_parent_element(xml_model,tmp_element)
    path_from_root.reverse()
    
    path_from_root.append(current_element.get('name').replace("=","_EQ_"))
    
    return '.'.join(path_from_root)


def compute_group_cardinality(xml_model, current_element):
    # Check if there is a XOR  (Alternative)  or an OR (Commutative) that encompasses ALL CHILDREN.

    # Check if there is a total XOR group cardinality.
    is_exclusive_or = False
    has_child_wout_xor_constraint = False
    group_cardinality = ""
    for element_children_ref  in current_element.findall('childElements/child'):
        element_child_id = element_children_ref.find('id').text
        element_child = xml_model.find(".//element[@id='%s']" % element_child_id )
        if element_child.find("constraints/constraint[@type='alternative']/constraint_element") != None:
            is_exclusive_or = True
        else:
            has_child_wout_xor_constraint = True
            
    if is_exclusive_or == True and has_child_wout_xor_constraint == False:
        group_cardinality = "xor "
    
    # Check if there is a total OR group cardinality.
    is_or = False
    has_child_wout_or_constraint = False
    for element_children_ref  in current_element.findall('childElements/child'):
        element_child_id = element_children_ref.find('id').text
        element_child = xml_model.find(".//element[@id='%s']" % element_child_id )
        #print "Seaching element_child %s " % element_child.get('name')

        if element_child.find("constraints/constraint[@type='commulative']/constraint_element") != None:
            is_or = True
        else:
            has_child_wout_or_constraint = True
        
    
    if is_or == True and has_child_wout_or_constraint==False:
        group_cardinality = "or "
        
    
    return (group_cardinality, is_exclusive_or and  has_child_wout_xor_constraint, is_or and has_child_wout_or_constraint)



def get_footprint(xml_model_nfp, current_element, args):
    footprint_element = xml_model_nfp.find(".//*[@id='%s']/clearedValue" % current_element.get('id')) 
    if footprint_element == None:
        footprint = "0"
    else:
        footprint = footprint_element.text
        footprint = str(int(round( float(footprint)/ float(args.scaledownby) , 0)))

    if args.clear_repeated_base_values == True and current_element in _List_Mandatory_Base_Features and \
        current_element!=_List_Mandatory_Base_Features[0] and footprint == get_footprint(xml_model_nfp, _List_Mandatory_Base_Features[0], args):
        footprint = "0"
        
    return footprint

def get_empty_features_footprint(xml_model_configurations, args):
    """
    Gets the footprint of a SPL with no elements.
    """
    if xml_model_configurations.find("configuration[@features='0']") == None:
        base_footprint = "0"
    else:
        base_footprint = xml_model_configurations.find("configuration[@features='0']").get('measuredValue')
        base_footprint = str(int(round( float(base_footprint)/ float(args.scaledownby) , 0)))
    return base_footprint
