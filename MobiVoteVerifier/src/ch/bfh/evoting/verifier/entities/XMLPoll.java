/* 
 * MobiVoteVerifier
 * 
 *  MobiVoteVerifier: Verification application for MobiVote
 *  Copyright (C) 2014 Bern
 *  University of Applied Sciences (BFH), Research Institute for Security
 *  in the Information Society (RISIS), E-Voting Group (EVG) Quellgasse 21,
 *  CH-2501 Biel, Switzerland
 * 
 *  GNU Affero General Public License (AGPL) v3
 *   
 *   This program is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Affero General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Affero General Public License for more details.
 *
 *   You should have received a copy of the GNU Affero General Public License
 *   along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * For further information contact us: http://e-voting.bfh.ch/
 *
 * Redistributions of files must retain the above copyright notice.
 */
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
	private XMLElement generator;
	
	public XMLPoll(){}
	
	public XMLPoll(String question, List<XMLOption> options,
			List<XMLParticipant> participants, String p, XMLElement generator) {
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
	public XMLElement getGenerator() {
		return generator;
	}
	public void setGenerator(XMLElement generator) {
		this.generator = generator;
	}	
	
}
