import java.io.File;
import java.io.IOException;
import javax.xml.transform.Source;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

/**
 * Reads in a XSD schema and a XML file and validates the document
 * against the schema.
 *
 * @author Jimmy Liang
 */
public class XsdCheck {

    public static void main(String[] args) throws IOException {
        if (args.length < 2) {
            System.out.println("Requires two arguments: <xsd-file> <xml-file>");
            System.exit(1);
        }

        File xsd = new File(args[0]);
        File xml = new File(args[1]);

        SchemaFactory factory = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");

        try {
            Schema schema = factory.newSchema(xsd);

            Validator validator = schema.newValidator();

            Source source = new StreamSource(xml);

            validator.validate(source);
        } catch (SAXParseException e) {
            System.out.println("XML Validation error on line " + e.getLineNumber() + ", column " + e.getColumnNumber());
            System.out.println(e.getMessage());
        } catch (SAXException e) {
            System.out.println("XML Validation error.");
            System.out.println(e.getMessage());
        }
    }
}

