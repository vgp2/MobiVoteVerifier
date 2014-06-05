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

import org.apache.commons.codec.binary.Base64;
import org.simpleframework.xml.Element;

import ch.bfh.unicrypt.helper.array.ByteArray;
import ch.bfh.unicrypt.helper.bytetree.ByteTree;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Group;


public class XMLElement {

	@Element
	private String value;
	
	public XMLElement(){}
	
	public XMLElement(ch.bfh.unicrypt.math.algebra.general.interfaces.Element element) {
		this.value = Base64.encodeBase64String(element.getByteTree().getByteArray().getAll());
	}
	
	public ch.bfh.unicrypt.math.algebra.general.interfaces.Element getValue(Group group) {
		return group.getElementFrom(ByteTree.getInstanceFrom(ByteArray.getInstance(Base64.decodeBase64(value))));
	}
}