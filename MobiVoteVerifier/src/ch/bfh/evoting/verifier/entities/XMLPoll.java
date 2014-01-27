package ch.bfh.evoting.verifier.entities;

import java.util.List;

import org.simpleframework.xml.Element;
import org.simpleframework.xml.ElementList;

public class XMLPoll {

	@Element
	private String question;
	@ElementList
	private List<XMLOption> options;
	@ElementList
	private List<XMLParticipant> participants;

	@Element
	private String p;
	@Element
	private XMLGqElement generator;
	
	public XMLPoll(){}
	
	public XMLPoll(String question, List<XMLOption> options,
			List<XMLParticipant> participants, String p, XMLGqElement generator) {
		super();
		this.question = question;
		this.options = options;
		this.participants = participants;
		this.p = p;
		this.generator = generator;
	}
	
	public String getQuestion() {
		return question;
	}
	public void setQuestion(String question) {
		this.question = question;
	}
	public List<XMLOption> getOptions() {
		return options;
	}
	public void setOptions(List<XMLOption> options) {
		this.options = options;
	}
	public List<XMLParticipant> getParticipants() {
		return participants;
	}
	public void setParticipants(List<XMLParticipant> participants) {
		this.participants = participants;
	}
	public String getP() {
		return p;
	}
	public void setP(String p) {
		this.p = p;
	}
	public XMLGqElement getGenerator() {
		return generator;
	}
	public void setGenerator(XMLGqElement generator) {
		this.generator = generator;
	}	
	
}
