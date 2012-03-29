
from xml.etree import ElementTree

fp_nfp_model = open("/Users/rafaelolaechea/Downloads/rawMaterial/Violet/perFeature/nfpmodel.xml")
xml_model = ''.join(fp_nfp_model.readlines())

clafer_model = open("Violet.cfr")
clafer_model = clafer_model.readlines()

parsed_xml_model = ElementTree.fromstring(xml_model)
measured_values = parsed_xml_model.iter('measured_values').next()
i =1
while i < len(clafer_model):
	while(i < len(clafer_model) and clafer_model[i].find('[')!=-1):
		print clafer_model[i],
		i = i + 1
	if (i < len(clafer_model)):
		print clafer_model[i],
		text_without_tabs = clafer_model[i].lstrip()
		text_without_tabs_bothsides = clafer_model[i].strip()
		tabs  = clafer_model[i][:clafer_model[i].find(text_without_tabs_bothsides)]
		try:
			item_xml = measured_values.iter(text_without_tabs_bothsides).next()
			print "%s\tfootprint=%s" % (tabs, item_xml.find('clearedValue').text)		
		except StopIteration:
			print "%s\tfootprint=0" % tabs
			pass
		i = i + 1

clafer_model = open("violet.cfr")
clafer_model = clafer_model.readlines()

for line in clafer_model:
	if line.find(']') == -1 and line.find('abstract') and len(line.strip()) > 0:
		if line.find('?')==-1:
			print "%s : IMeasurable"  % (line[:-1],)
		else:
			print "%s : IMeasurable ?"  % (line[0:line.find('?')],)			
	else:
		print line,
# To create the sum:
i = 0
father_first = ""
father_second = ""
for line in clafer_model:
	if line.find('IMeasurable') != -1 and line.find('abstract')==-1 and line.find('//')==-1 and line.find('[')==-1:
		text_without_tabs = clafer_model[i].lstrip()
		text_without_tabs_bothsides = clafer_model[i].strip()
		tabs  = clafer_model[i][:clafer_model[i].find(text_without_tabs_bothsides)]
		if len(tabs)==1:			
			print "%s.footprint +" % text_without_tabs_bothsides[:text_without_tabs_bothsides.find(": IMeasurable")].strip().replace("or ",""),
			father_first = text_without_tabs_bothsides[:text_without_tabs_bothsides.find(": IMeasurable")].strip().replace("or ","") 
		elif len(tabs) == 2:
			print "%s.%s.footprint +" % (father_first, text_without_tabs_bothsides[:text_without_tabs_bothsides.find(": IMeasurable")].strip().replace("or ","")),
			father_second = text_without_tabs_bothsides[:text_without_tabs_bothsides.find(": IMeasurable")].strip().replace("or ","") 
		elif len(tabs)==3:
			print "%s.%s.%s.footprint +" % (father_first, father_second, text_without_tabs_bothsides[:text_without_tabs_bothsides.find(": IMeasurable")].strip().replace("or ","")),
	i = i + 1	
