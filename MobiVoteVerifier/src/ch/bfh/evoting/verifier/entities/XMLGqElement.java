package ch.bfh.evoting.verifier.entities;

import org.simpleframework.xml.Element;


public class XMLGqElement {

	@Element
	private String value;
	
	public XMLGqElement(){}
	
	public XMLGqElement(String value) {
		this.value = value;
	}
	
	public String getValue() {
		return value;
	}
	public void setValue(String value) {
		this.value = value;
	}
}
