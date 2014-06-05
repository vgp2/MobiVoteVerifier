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
package ch.bfh.evoting.verifier;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Array;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.security.DigestInputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.codec.binary.Base64;
import org.simpleframework.xml.Serializer;
import org.simpleframework.xml.core.Persister;

import ch.bfh.evoting.verifier.entities.XMLOption;
import ch.bfh.evoting.verifier.entities.XMLParticipant;
import ch.bfh.evoting.verifier.entities.XMLPoll;
import ch.bfh.unicrypt.crypto.proofsystem.classes.ElGamalEncryptionValidityProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.PreimageEqualityProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.PreimageProofSystem;
import ch.bfh.unicrypt.crypto.schemes.commitment.classes.StandardCommitmentScheme;
import ch.bfh.unicrypt.crypto.schemes.encryption.classes.ElGamalEncryptionScheme;
import ch.bfh.unicrypt.helper.array.ByteArray;
import ch.bfh.unicrypt.math.algebra.concatenative.classes.ByteArrayElement;
import ch.bfh.unicrypt.math.algebra.concatenative.classes.ByteArrayMonoid;
import ch.bfh.unicrypt.math.algebra.dualistic.classes.N;
import ch.bfh.unicrypt.math.algebra.dualistic.classes.Z;
import ch.bfh.unicrypt.math.algebra.dualistic.classes.ZMod;
import ch.bfh.unicrypt.math.algebra.general.classes.FiniteByteArrayElement;
import ch.bfh.unicrypt.math.algebra.general.classes.ProductGroup;
import ch.bfh.unicrypt.math.algebra.general.classes.Subset;
import ch.bfh.unicrypt.math.algebra.general.classes.Tuple;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Element;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Group;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModElement;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModSafePrime;
import ch.bfh.unicrypt.math.function.classes.ProductFunction;
import ch.bfh.unicrypt.math.function.interfaces.Function;
import ch.bfh.unicrypt.random.classes.PseudoRandomOracle;
import ch.bfh.unicrypt.random.classes.ReferenceRandomByteSequence;

/**
 * Class implementing a verifier for MobiVote HKRS12 application
 * @author Philémon von Bergen
 *
 */
public class Verifier {

	private static final boolean DEBUG = false;
	private static GStarModSafePrime G_q;
	private static ZMod Z_q;
	private static Element generator;
	private static XMLPoll poll;
	private static Element[] representations;
	private static Tuple otherInput;
	private static Element[] a;
	private static Element[] b;
	private static Element[] h;
	private static Element[] hHat;
	private static Element[] hHatPowX;
	private static Element[] proofForX;
	private static Element[] validityProof;
	private static Element[] equalityProof;

	private static boolean recoveryNeeded = false;
	private static Z Zgroup;

	/**
	 * This program is a verifier for MobiVote application with HKRS12 protocol
	 * You have to indicate the XML file exported from the application as argument for this program.
	 * You can also indicate the files of different participants. In this case, there will be checked if all files contain the same values.
	 * @param args the file(s) containing the values of the protocol
	 */
	public static void main(String[] args) {
	
		/*
		 * Reading files given as parameters
		 */
		if(args.length<1){
			//Not enough arguments
			System.out.println("You must indicate the location of the XML file containing the data to verify! You can also indicate the files of different participants.");
			return;
		} else if (args.length>1){
			//Make a digest of all files and compare them
			List<byte[]> digests = new ArrayList<byte[]>();
			for(String s : args){
				try {
					MessageDigest md = MessageDigest.getInstance("SHA-256");

					InputStream is = Files.newInputStream(Paths.get(s));
					DigestInputStream dis = new DigestInputStream(is, md);
					@SuppressWarnings("unused")
					int numBytes = -1;
					while((numBytes = dis.read()) != -1){
						dis.read();
					}
					
					byte[] digest = md.digest();
					digests.add(digest);

				} catch (IOException e) {
					System.out.println("One of the given files does not exists!");
					return;
				} catch (NoSuchAlgorithmException e1) {
					System.out.println("Unable to compute the digest of the file!");
					return;
				}
			}
			System.out.print("Checking the similarity of the files...");
			for(byte[] b : digests){
				for(byte[] b2 : digests){
					if(!Arrays.equals(b, b2)){
						System.out.print("\t\t\t\t\t\t\t\t\t\tWRONG\n");
						System.out.println("The given files are not all identical! This means the content received by the participants was not the same.");
						return;
					}
				}
			}
			System.out.print("\t\t\t\t\t\t\t\t\t\tOK\n\n");
		} else if (args.length==1){
			//Print a warning
			System.out.println("BE CAREFUL: checking only one file ensure that the cryptographic values of the protocol are correct.\n" +
					"But, it does NOT ensure that all users have the same result. This could happen when a participant missed some messages.\n" +
					"This case is only covered by this verifier by giving multiple files as argument.\n");
		}
		
		Serializer serializer = new Persister();
		File source = new File(args[0]);

		poll = null;
		System.out.print("Reading file...");
		try {
			poll = serializer.read(XMLPoll.class, source);
			System.out.print("\t\t\t\t\t\t\t\t\t\t\t\t\tOK\n");
		} catch (Exception e) {
			System.out.print("\t\t\t\t\t\t\t\t\t\t\t\t\tFAILED\n");
			e.printStackTrace();
			return;
		}

		/*
		 * Create the initializations needed by the protocol
		 */
		G_q = GStarModSafePrime.getInstance(new BigInteger(poll.getP()));
		Z_q = G_q.getZModOrder();
		Zgroup = Z.getInstance();
		generator = poll.getGenerator().getValue(G_q);


		representations = new Element[poll.getOptions().size()];
		int i=0;
		for(XMLOption op:poll.getOptions()){
			representations[i]= op.getRepresentation().getValue(Z_q);
			i++;
		}

		System.out.println();
		System.out.println("Verifying vote: \""+poll.getQuestion()+"\"");
		
		/*
		 * Verify the dependence between cryptographic values and the vote properties
		 */
		//Not used anymore, implicitly done with otherInputs of proofs
		//verifyDependencyTextCrypto();


		/*
		 * Verify the proofs for the user
		 */
		System.out.println();
		System.out.println("Verifying the proof for the participants...");
		a = new Element[poll.getParticipants().size()];
		b = new Element[poll.getParticipants().size()];
		h = new Element[poll.getParticipants().size()];
		hHat = new Element[poll.getParticipants().size()];
		hHatPowX = new Element[poll.getParticipants().size()];
		proofForX = new Element[poll.getParticipants().size()];
		validityProof = new Element[poll.getParticipants().size()];
		equalityProof = new Element[poll.getParticipants().size()];
		Tuple pollTuple = preparePollOtherInput(poll, representations, generator);

		int k=0;
		for(XMLParticipant p : poll.getParticipants()){
			System.out.println("\tParticipant "+p.getIdentification()+" ("+p.getUniqueId()+")");

			if(p.getAi()!=null){
				a[k] = p.getAi().getValue(G_q);
				if(DEBUG)System.out.println("Value a: "+a[k]);
			}
			if(p.getHi()!=null){
				h[k] = p.getHi().getValue(G_q);
				if(DEBUG)System.out.println("Value h: "+h[k]);
			}
			if(p.getBi()!=null){
				b[k] = p.getBi().getValue(G_q);
				if(DEBUG)System.out.println("Value b: "+b[k]);
			}
			if(p.getHiHat()!=null){
				hHat[k] = p.getHiHat().getValue(G_q);
				if(DEBUG)System.out.println("Value h hat: "+hHat[k]);
			}
			if(p.getHiHatPowXi()!=null){
				hHatPowX[k] = p.getHiHatPowXi().getValue(G_q);
				if(DEBUG)System.out.println("Value h hat ^ x: "+hHatPowX[k]);
			}

			if(p.getProofForXi()!=null){
				ProductGroup group = ProductGroup .getInstance(G_q,Zgroup,Z_q);
				
				proofForX[k] = p.getProofForXi().getValue(group);
			}
			
			if(p.getProofValidVote()!=null){
				
				Group[] tripleElement1Groups = new Group[poll.getOptions().size()];
				Group[] tripleElement2Groups = new Group[poll.getOptions().size()];
				Group[] tripleElement3Groups = new Group[poll.getOptions().size()];
				for(i=0; i<poll.getOptions().size();i++){
					tripleElement1Groups[i]= ProductGroup.getInstance(G_q,G_q);
					tripleElement2Groups[i]=Zgroup;
					tripleElement3Groups[i]=Z_q;
				}
				ProductGroup tripleElement1 = ProductGroup.getInstance(tripleElement1Groups);
				ProductGroup tripleElement2 = ProductGroup.getInstance(tripleElement2Groups);
				ProductGroup tripleElement3 = ProductGroup.getInstance(tripleElement3Groups);
				ProductGroup group = ProductGroup.getInstance(tripleElement1, tripleElement2, tripleElement3);
				
				validityProof[k] = p.getProofValidVote().getValue(group);
			
				if(DEBUG)System.out.println("Proof of validity: "+validityProof[k]);		
			}
			
			if(p.getProofForHiHat()!=null){
				recoveryNeeded = true;
				ProductGroup group = ProductGroup.getInstance(ProductGroup.getInstance(G_q, G_q),Zgroup,Z_q);
				
				equalityProof[k] = p.getProofForHiHat().getValue(group);
			}

			Tuple participantTuple = prepareParticipantOtherInput(p);
			otherInput = Tuple.getInstance(participantTuple, pollTuple);

			/*
			 * Verify proof of knowledge 
			 */
			System.out.print("\t\tVerifying proof of knowledge of x value...");
			verifyProofOfKnowledgeOfX(k);

			/*
			 * Verify proof of validity 
			 */
			if(validityProof[k]!=null){
				System.out.print("\t\tVerifying proof of valid vote...");
				verifyValidityProof(k);
			}

			/*
			 * Verify proof of equality 
			 */
			if(equalityProof[k]!=null){
				System.out.print("\t\tVerifying proof of equality between discrete logarithm g^x and h_hat^x...");
				verifyEqualityProof(k);
			}
			k++;
		}

		/**
		 * Computing the result
		 */
		System.out.println();
		System.out.print("Computing the result...");
		computeResult();


	}


//	/**
//	 * Verify the dependence between cryptographic values and the vote properties
//	 */
//	private static void verifyDependencyTextCrypto() {
//		System.out.println();
//		System.out.print("Verifying the dependence between cryptographic values and the vote properties...");
//		String texts = poll.getQuestion();
//
//		for(XMLOption op:poll.getOptions()){
//			texts += op.getText();
//		}
//
//		Tuple tuple = Tuple.getInstance(representations);
//		ByteArray representationsElement = tuple.getHashValue();
//		ByteArrayElement textElement = ByteArrayMonoid.getInstance().getElement(texts.getBytes());
//
//		ByteBuffer buffer = ByteBuffer.allocate(textElement.getValue().getLength()+representationsElement.getLength());
//		buffer.put(textElement.getValue().getAll());
//		buffer.put(representationsElement.getAll());
//		buffer.flip(); 
//
//		ReferenceRandomByteSequence rrs = PseudoRandomOracle.getInstance().getReferenceRandomByteSequence(ByteArray.getInstance(buffer.array()));
//		GStarModElement verificationGenerator = G_q.getIndependentGenerator(1, rrs);
//
//		if(G_q.areEquivalent(generator, verificationGenerator)){
//			System.out.print("\t\t\t\tOK\n");
//		} else {
//			System.out.print("\t\t\t\tFAILED\n");
//			System.out.println("The given poll and the given cryptographic values don't match together.");
//		}
//
//	}

	/**
	 * Verify the proof of knowledge of the x value
	 */
	private static void verifyProofOfKnowledgeOfX(int k) {
		if(DEBUG)System.out.println("\n\t\t\tValue of a: "+a[k]);
		if(DEBUG)System.out.println("\t\t\tValue of proof: "+proofForX[k]);
		if(DEBUG)System.out.println("\t\t\tValue of generator: "+generator);

		//Proof of knowledge of xi
		StandardCommitmentScheme cs = StandardCommitmentScheme.getInstance(generator);
		if(DEBUG)System.out.println("\t\t\tStandardCommitmentScheme: "+cs);

		if(DEBUG)System.out.println("\t\t\tOtherInput: "+otherInput);

		PreimageProofSystem spg = PreimageProofSystem.getInstance(cs.getCommitmentFunction(), otherInput);
		
		//Generator and index of the participant has also to be hashed in the proof
		if(DEBUG)System.out.println("\t\t\tVerify proof: "+spg.verify(proofForX[k], a[k]));
		if(DEBUG)System.out.println();
		if(!DEBUG){
			if(spg.verify(proofForX[k], a[k])){
				System.out.print("\t\t\t\t\t\t\tCORRECT\n");
			} else {
				System.out.print("\t\t\t\t\t\t\tWRONG\n");
			}
		}
	}


	/**
	 * Verify the validity proof of the vote
	 */
	private static void verifyValidityProof(int k) {
		Element[] possibleVotes = new Element[poll.getOptions().size()];
		for(int j=0; j<possibleVotes.length;j++){
			possibleVotes[j] = generator.selfApply(representations[j]);
		}

		ElGamalEncryptionScheme ees = ElGamalEncryptionScheme.getInstance(generator);

		Subset possibleVotesSet = Subset.getInstance(G_q, possibleVotes);
		ElGamalEncryptionValidityProofSystem vpg = ElGamalEncryptionValidityProofSystem.getInstance(
				ees, h[k], possibleVotesSet, otherInput);

		//simulate the ElGamal cipher text (a,b) = (ai,bi);
		Tuple publicInput = Tuple.getInstance(a[k], b[k]);
		
		if(DEBUG) System.out.println("Validity proof: "+ validityProof[k]);
		if(vpg.verify(validityProof[k], publicInput)){
			System.out.print("\t\t\t\t\t\t\t\tCORRECT\n");
		} else {
			System.out.print("\t\t\t\t\t\t\t\tWRONG\n");
		}
	}

	/**
	 * Verify the proof of equality between discrete logarithms
	 */
	private static void verifyEqualityProof(int k) {
		//Function g^r
		StandardCommitmentScheme cs3 = StandardCommitmentScheme.getInstance(generator);
		Function f1 = cs3.getCommitmentFunction();

		//Function h_hat^r
		StandardCommitmentScheme cs4 = StandardCommitmentScheme.getInstance(hHat[k]);
		Function f2 = cs4.getCommitmentFunction();

		ProductFunction f3 = ProductFunction.getInstance(f1, f2);

		PreimageEqualityProofSystem piepg = PreimageEqualityProofSystem.getInstance(f3, otherInput);

		Tuple publicInput3 = Tuple.getInstance(a[k], hHatPowX[k]);

		if(piepg.verify(equalityProof[k], publicInput3)){
			System.out.print("\t\t\tCORRECT\n");
		} else {
			System.out.print("\t\t\tWRONG\n");
		}
	}

	/**
	 * Recompute the result with the values contained in the XML file, and compare the obtained result
	 * with the result described in the XML file
	 */
	private static void computeResult() {
		Element product1 = G_q.getElement(BigInteger.valueOf(1));
		for(int j=0; j< poll.getParticipants().size(); j++){
			if(b[j]==null)continue;
			
			if(recoveryNeeded){
				
				if(hHatPowX[j]==null){
					//this was an excluded participant so we don't care about his values in the tally
					continue;
				}
				product1=product1.apply(b[j]);
				product1=product1.apply(hHatPowX[j]);
			} else {
				product1=product1.apply(b[j]);
			}
		}
		
		Element sumVote = Z_q.getElement(BigInteger.valueOf(0));
		for(int j=0; j<poll.getOptions().size();j++){
			sumVote = sumVote.apply(representations[j].selfApply(poll.getOptions().get(j).getVotes()));
		}

		Element product2 = generator.selfApply(sumVote);

		if(G_q.areEquivalent(product1, product2)){
			System.out.print("\t\t\t\t\t\t\t\t\t\t\t\tCORRECT\n");
			System.out.println("\tQuestion was: "+poll.getQuestion());
			System.out.println("\tResult was:");
			for(XMLOption op : poll.getOptions()){
				String votesText = " votes";
				if(op.getVotes()==1){
					votesText = " vote";
				}
				System.out.println("\t\t"+op.getText()+": "+op.getVotes()+votesText);
			}
		} else {
			System.out.print("\t\t\t\t\t\t\t\t\t\t\t\tWRONG\n");
		}
	}

	/**
	 * Return all the important data of the participant that should be used in the hash used in ZK proofs
	 * @param p participant
	 * @return all the important data of the participant that should be used in the hash used in ZK proofs
	 */
	private static Tuple prepareParticipantOtherInput(XMLParticipant p) {
		Element index = N.getInstance().getElement(BigInteger.valueOf(p.getProtocolParticipantIndex()));
		ByteArrayElement proverId = ByteArrayMonoid.getInstance().getElement(p.getUniqueId().getBytes());

		return Tuple.getInstance(index, proverId);
	}

	/**
	 * Return all the important data of the poll that should be used in the hash used in ZK proofs
	 * @param poll Poll object
	 * @param optionsRepresentations Representation values of the options
	 * @param generator Generator used in the protocol
	 * @return Return all the important data of the poll that should be used in the hash used in ZK proofs
	 */
	private static Tuple preparePollOtherInput(XMLPoll poll, Element[] optionsRepresentations, Element generator) {
		String otherHashInputString = poll.getQuestion();
		for(XMLOption op:poll.getOptions()){
			otherHashInputString += op.getText();
		}
		for(XMLParticipant p:poll.getParticipants()){
			otherHashInputString += p.getUniqueId()+p.getIdentification();
		}

		ByteArrayElement otherHashInput = ByteArrayMonoid.getInstance().getElement(otherHashInputString.getBytes());
		Tuple optionsRepresentationsTuple = Tuple.getInstance(optionsRepresentations);
		return Tuple.getInstance(optionsRepresentationsTuple, otherHashInput, generator);

	}

}
