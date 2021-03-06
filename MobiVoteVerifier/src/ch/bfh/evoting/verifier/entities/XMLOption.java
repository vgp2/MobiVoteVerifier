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
 
import org.simpleframework.xml.Element;


public class XMLOption {

	@Element
	private String text;
	@Element
	private int votes;
	@Element
	private XMLElement representation;
	
	public XMLOption(){}
	
	public XMLOption(String text, int votes, XMLElement representation) {
		super();
		this.text = text;
		this.votes = votes;
		this.representation = representation;
	}
	
	public String getText() {
		return text;
	}
	public void setText(String text) {
		this.text = text;
	}
	public int getVotes() {
		return votes;
	}
	public void setVotes(int votes) {
		this.votes = votes;
	}
	public XMLElement getRepresentation() {
		return representation;
	}
	public void setRepresentation(XMLElement representation) {
		this.representation = representation;
	}
	
	
}
