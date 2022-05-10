package sjdb;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

public class Estimator implements PlanVisitor {

	private int Cost = 0;
	public Estimator() {
		// empty constructor
	}

	/* 
	 * Create output relation on Scan operator
	 *
	 * Example implementation of visit method for Scan operators.
	 */
	public void visit(Scan op) {
		Relation input = op.getRelation();
		Relation output = new Relation(input.getTupleCount());
		
		Iterator<Attribute> iter = input.getAttributes().iterator();
		while (iter.hasNext()) {
			output.addAttribute(new Attribute(iter.next()));
		}
		
		op.setOutput(output);
		Cost += output.getTupleCount();
	}
    /*
     * (non-Javadoc)
     * @see sjdb.PlanVisitor#visit(sjdb.Project)
     * T(羽 A (R)) = T(R) 
     */
	public void visit(Project op) {
		Relation input = op.getInput().getOutput();
		//get input relation
		Relation output = new Relation(input.getTupleCount()); //T(羽 A (R)) = T(R)
		//create an output ralation
		List<Attribute> Attr = op.getAttributes();
		  // reletion attributes
		Iterator<Attribute> iter1 = op.getAttributes().iterator();  //the attribute in sql need to be projected
		// if the relation attribute is equal to the attribute in sql need to be projected, add the attribute to output
		while(iter1.hasNext()) {
			Attribute attr = iter1.next();
			Iterator<Attribute> iter = input.getAttributes().iterator();
			while(iter.hasNext()) {
				Attribute attr1 = iter.next();
				if(attr1.equals(attr)) {
					output.addAttribute(new Attribute(attr1));
					break;
				}
			}
			//if (Attr.contains(attr)) {
			//	output.addAttribute(new Attribute(attr));
			//}
			
		}
		op.setOutput(output);
		Cost += output.getTupleCount();
	}
	/*
	 * (non-Javadoc)
	 * @see sjdb.PlanVisitor#visit(sjdb.Select)
	 * T(考 A=c (R)) = T(R)/V(R,A), V(考 A=c (R), A) = 1
	 * T(考 A=B (R)) = T(R)/max(V(R,A),V(R,B)), V(考 A=B (R), A) = V(考 A=B (R), B) = min(V(R, A), V(R, B)
	 */
	public void visit(Select op) {
		//cteata input and output ralation
		Relation input = op.getInput().getOutput(); // get the previous SQL's output relation
		Relation output;
		
		Predicate predicate = op.getPredicate(); // 
		Iterator<Attribute> iter = input.getAttributes().iterator();
		Attribute left = input.getAttribute(predicate.getLeftAttribute());
		//1.attr=val
		if (predicate.equalsValue()) {
			int Tuplecount = input.getTupleCount();  //get T(R)
			int Value;
			//Attribute left = input.getAttribute(predicate.getLeftAttribute());
			int left_value = left.getValueCount(); //rightvalue
			Value= left_value;  //get V(R,A)
			output = new Relation(Tuplecount/Value); //
			while(iter.hasNext()) {
				Attribute attr = iter.next();
				if(attr.equals(left)) {
					output.addAttribute(new Attribute(attr.getName(), 1));
				}
				else {
					output.addAttribute(new Attribute(attr));
				}
			}
		}
		//2.attr=attr
		else {
			int Tuplecount = input.getTupleCount(); //get T(R)

			Attribute right = input.getAttribute(predicate.getRightAttribute());
			int Valuea = left.getValueCount(); //V(R,A)
			int Valueb = right.getValueCount(); //V(R,B)
			int maxvalue = Math.max(Valuea, Valueb);
			int minvalue = Math.min(Valuea, Valueb);
			output = new Relation(Tuplecount/maxvalue); //
			while(iter.hasNext()) {
				Attribute attr = iter.next();
				if(attr.equals(left)) {
					int valuecount = minvalue;
					output.addAttribute(new Attribute(attr.getName(), valuecount));
				}
				else if(attr.equals(right)){
					int valuecount = minvalue;
					output.addAttribute(new Attribute(attr.getName(), valuecount));
				}
				else {
					output.addAttribute(new Attribute(attr));
				}
			}
		}
		op.setOutput(output);
		Cost += output.getTupleCount();
	}
	
	/*
	 * (non-Javadoc)
	 * T(R ℅ S) = T(R)T(S)
	 * @see sjdb.PlanVisitor#visit(sjdb.Product)
	 */
	public void visit(Product op) {
		//get left and right relation
		Relation left_rel = op.getLeft().getOutput();
		Relation right_rel = op.getRight().getOutput();
		int tupleleft = left_rel.getTupleCount();  //T(R)
		int tupleright = right_rel.getTupleCount(); //T(S)
		Relation output = new Relation(tupleleft*tupleright); //
		
		//add left attribute
		Iterator<Attribute> iterleft = left_rel.getAttributes().iterator();
		while(iterleft.hasNext()) {
			output.addAttribute(new Attribute(iterleft.next()));
		}
		
		//add right attributr
		Iterator<Attribute> iterright = right_rel.getAttributes().iterator();
		while(iterright.hasNext()) {
			output.addAttribute(new Attribute(iterright.next()));
		}
		op.setOutput(output);
		Cost += output.getTupleCount();
	}
	
	/*
	 * (non-Javadoc)
	 * @see sjdb.PlanVisitor#visit(sjdb.Join)
	 * T(R** A=B S) = T(R)T(S)/max(V(R,A),V(S,B)), V(R** A=B S, A) = V(R** A=B S, B) = min(V(R, A), V(S, B))
	 */
	public void visit(Join op) {
		//get right and left relation
		Relation left_rel = op.getLeft().getOutput();
		Relation right_rel = op.getRight().getOutput();
		int tupleft = left_rel.getTupleCount();  //T(R)
		int tupleright = right_rel.getTupleCount();  //T(S)
		Predicate pred = op.getPredicate();
		
		//get right and left attribute
		Attribute left_attr = new Attribute(pred.getLeftAttribute().getName());
		Attribute right_attr = new Attribute(pred.getRightAttribute().getName());
		List<Attribute> att = new ArrayList<>();
		att.addAll(left_rel.getAttributes());
		att.addAll(right_rel.getAttributes());
		//get countvalue
		for(Attribute attr1 : att){
			if(attr1.equals(left_attr)){
				String name = attr1.getName();
				int count = attr1.getValueCount();
				left_attr = new Attribute(name,count);
			}
		}
		for(Attribute attr1 : att){
			if(attr1.equals(right_attr)){
				String name = attr1.getName();
				int count = attr1.getValueCount();
				right_attr = new Attribute(name,count);
			}
		}
		int left_val = left_attr.getValueCount();  //V(R,A)
		int right_val = right_attr.getValueCount(); //V(S,B)
		int max_val = Math.max(left_val, right_val);
		int min_val = Math.min(right_val, left_val);
		Relation output = new Relation(tupleft*tupleright/max_val);
		
		// add left attribute
		Iterator<Attribute> iterleft = left_rel.getAttributes().iterator();
		while(iterleft.hasNext()) {
			Attribute attr = iterleft.next();
			if(attr.equals(left_attr)) {
				int valuecount = min_val;
				output.addAttribute(new Attribute(attr.getName(),valuecount));
			}
			else {
				output.addAttribute(attr);
			}
		}
		
		// add right attribute
		Iterator<Attribute> iterright = right_rel.getAttributes().iterator();
		while(iterright.hasNext()) {
			Attribute attr = iterright.next();
			if(attr.equals(right_attr)) {
				int valuecount = min_val;
				output.addAttribute(new Attribute(attr.getName(),valuecount));
			}
			else {
				output.addAttribute(attr);
			}
		}
		op.setOutput(output);
		Cost += output.getTupleCount();
	}
	public int getCost(Operator plan) {
		this.Cost = 0;
		plan.accept(this);
		return this.Cost;
	}
}
