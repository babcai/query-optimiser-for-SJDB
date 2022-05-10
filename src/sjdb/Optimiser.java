package sjdb;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.*;
import java.util.stream.Collectors;

public class Optimiser implements PlanVisitor{
	/*
	 * push down selection
	 * Reorde join
	 * create join
	 * push down projection
	 */
	private ArrayList<Attribute> topattributes = new ArrayList<>();
	private ArrayList<Attribute> allattributes = new ArrayList<>();
	private ArrayList<Relation> allRelations = new ArrayList<>();
	private ArrayList<Predicate> allpredicates = new ArrayList<>();
	private ArrayList<Scan> allScans= new ArrayList<>();
	private Catalogue catalogue;
	private ArrayList<Operator> reorderOperators = new ArrayList<>();
	public Optimiser(Catalogue catalogue) {
		this.catalogue = catalogue;
	}
	
	public Operator optimise(Operator plan) {
		//Push Selects down
		plan.accept(this); // get all predicates attributes and scans
		Operator operator = pushDown(plan);
		//Reorder join
		operator = reordeJoin(operator,0);
		//Combine × and σ to create ⨝
		operator = createJoin(operator);
		operator = pushProject(operator);
		return operator ;
	}
	
	/*
	 *  Method to push select down
	 */
	private Operator pushDown(Operator op) {
		String operatortype = splitOperator(op);
		switch (operatortype){
			case "Scan"	:
				Scan scan = (Scan)op;
				Scan scanoutput = new Scan((NamedRelation)scan.getRelation());
				Operator sp = outputOperator(scanoutput);
				ArrayList<Predicate> acPredicate = acceptPredicate(scan.getRelation());
				Iterator<Predicate> iter = acPredicate.iterator();
				while (iter.hasNext()){
					Predicate pre = iter.next();
					sp = outputOperator(new Select(sp,pre));
				}
				allpredicates.removeAll(acPredicate);
				return sp;
			case "Project":
				Project project = (Project)op;
				Operator operator = pushDown(project.getInput());  // get previous operator
				Project projoutput = new Project(operator,project.getAttributes());  // get new project operator
				return outputOperator(projoutput);
			case "Product":
				Product product = (Product)op;
				Operator leftoperator = pushDown(product.getLeft());
				Operator rightoperator = pushDown(product.getRight());
				Product prodoutput = new Product(leftoperator,rightoperator);
				ArrayList<Predicate> acPredicate1 = acceptPredicate(product.getOutput());
				Operator sp1 = outputOperator(prodoutput);
				Iterator<Predicate> iter1 = acPredicate1.iterator();
				while (iter1.hasNext()){
					Predicate pre = iter1.next();
					sp1 = outputOperator(new Select(sp1,pre));
				}
				allpredicates.removeAll(acPredicate1);
				return sp1;
			case "Select":
				Select select = (Select)op;
				if(select.getPredicate().equalsValue()){
					//Predicate pre = new Predicate(select.getPredicate().getLeftAttribute(),select.getPredicate().getRightValue());
					//outputOperator(select);
					return pushDown(select.getInput());
				}else{
					//outputOperator(select);
					return pushDown(select.getInput());
				}
			case "Join":
				Join join = (Join)op;
				Operator leftjoin = pushDown(join.getLeft());
				Operator rightjoin = pushDown(join.getRight());
				Join joinoutput = new Join(leftjoin,rightjoin,join.getPredicate());
				ArrayList<Predicate> acPredicate2 = acceptPredicate(join.getOutput());
				Operator sp2 = outputOperator(joinoutput);
				Iterator<Predicate> iter2 = acPredicate2.iterator();
				while (iter2.hasNext()){
					Predicate pre = iter2.next();
					sp2 = outputOperator(new Select(sp2,pre));
				}
				allpredicates.removeAll(acPredicate2);
				return sp2;
		}

		// add all predicate
		return outputOperator(op);
	}

	/*
	 *  subtrees to put most restrictive σ first
	 */
	private Operator reordeJoin(Operator op, int flag) {
		if(op instanceof Scan) {
			Scan scan = (Scan) op;
			reorderOperators.add(op);  // add the scan in product
		} else if (op instanceof Project) {
			Project project = (Project) op;
			reordeJoin(project.getInput(),1);
		} else if (op instanceof Product) {
			Product product = (Product) op;
			reordeJoin(product.getLeft(),1);
			reordeJoin(product.getRight(),1);
		} else if (op instanceof Select){
			Select select = (Select) op;
			Operator input = op;
			while(((Select)input).getInput() instanceof Select){
				input = ((Select)input).getInput();
			}
			if (((Select)input).getInput() instanceof Scan){
				reorderOperators.add(op);
			}else{
				allpredicates.add(select.getPredicate());   // add predicates that is not be used
				reordeJoin(select.getInput(),1);
			}
	    } else if (op instanceof Join) {
			Join join = (Join) op;
			reordeJoin(join.getLeft(),1);
			reordeJoin(join.getRight(),1);
		}
		if (flag == 0) {
			op = newSelect(op, allpredicates, reorderOperators);
		}
		return op;
	}
	/*
	Create new Select with product
	 */
	private Operator newSelect(Operator op, ArrayList<Predicate> pre, ArrayList<Operator> Ops){
		// if the operators and predicates is empty or not enough
		if (Ops.isEmpty() || pre.isEmpty()){
			return op;
		}
		if(pre.size()<2){
			return op;
		}
		//sport operator by tuple count of each relation
		Ops.sort(Comparator.comparingInt(
				o -> (o.getOutput().getTupleCount() )));
		Iterator<Operator> iter = Ops.iterator();
        ArrayList<Predicate> accaptPredicates = new ArrayList<>();
		Operator thislop = iter.next();   //left first
		while(iter.hasNext()){
			Operator thisrop = iter.next();   //right next
			//add select above product
            thislop = outputOperator(new Product(thislop,thisrop));
			accaptPredicates = acceptPredicate(thislop.getOutput());
            Iterator<Predicate> aciter= accaptPredicates.iterator();
			while(aciter.hasNext()){
				Predicate p = aciter.next();
				thislop = outputOperator(new Select(thislop,p));
			}
			allpredicates.removeAll(accaptPredicates);
		}
		// add the top project
		return outputOperator(new Project(thislop,topattributes));
	}

    /*
    Combine × and σ to create ⨝
     */
	private Operator createJoin(Operator op) {
		if(op instanceof Scan){
			return outputOperator(new Scan((NamedRelation)((Scan) op).getRelation()));
		}else if (op instanceof Project){
			return outputOperator(new Project(createJoin(((Project) op).getInput()),((Project) op).getAttributes()));
		}else if (op instanceof Product) {
			return outputOperator(new Product(createJoin(((Product) op).getLeft()),createJoin(((Product) op).getRight())));
		}else if (op instanceof Join) {
			return outputOperator(new Join(((Join) op).getLeft(),((Join) op).getRight(),((Join) op).getPredicate()));
		}else if (op instanceof Select) {
			if(((Select) op).getInput() instanceof Product){
				Product product = (Product) ((Select) op).getInput();
				Operator left = createJoin(product.getLeft());
                Operator right = createJoin(product.getRight());
				return outputOperator(new Join(left,right,((Select) op).getPredicate()));
			}
			Operator operator = createJoin(((Select) op).getInput());
			return outputOperator(new Select(operator,((Select) op).getPredicate()));
		}
		return op;
	}
	/*
	Push project down
	 */
	private Operator pushProject(Operator op){
		if(op instanceof Scan){
			Scan scan = (Scan) op;
			scan = new Scan((NamedRelation) scan.getRelation());
            List<Attribute> acAttrs = acceptAttributes(scan.getOutput().getAttributes());
			if (acAttrs.size()>0 && !acAttrs.equals(scan.getOutput().getAttributes())){
				return outputOperator(new Project(scan,acAttrs));
			}else{
				return outputOperator(scan);
			}
		}else if (op instanceof Project) {
			Operator out = outputOperator(new Project(pushProject(((Project) op).getInput()),((Project) op).getAttributes()));
			if(((Project) out).getInput() instanceof Project){
				while (((Project) out).getInput() instanceof Project){
					out = ((Project) out).getInput();
				}
				out = new Project(((Project) out).getInput(),((Project) op).getAttributes());
				return out;
			}else{
				return out;
			}
		}else if (op instanceof Select) {
			Select select = (Select) op;
			Operator acselect;
			if(select.getInput() instanceof Scan){
				Scan inscan = (Scan) select.getInput();
				inscan = new Scan((NamedRelation) inscan.getRelation());
				acselect = outputOperator(new Select(outputOperator(inscan),select.getPredicate()));
			}else{
				acselect = outputOperator(new Select(pushProject(select.getInput()),select.getPredicate()));
			}
			List<Attribute> acAttributes = acceptAttributes(select.getOutput().getAttributes());
			if (acAttributes.size()>0 && !acAttributes.equals(select.getOutput().getAttributes())){
				return outputOperator(new Project(acselect,acAttributes));
			}else{
				return acselect;
			}
		}else if (op instanceof Product) {
			Product product = (Product) op;
			product = new Product(pushProject(product.getLeft()),pushProject(product.getRight()));
			List<Attribute> acAttrs = acceptAttributes(product.getOutput().getAttributes());
			if (acAttrs.size()>0 && !acAttrs.equals(product.getOutput().getAttributes())){
				return outputOperator(new Project(product,acAttrs));
			}else{
				return outputOperator(product);
			}
		}else if (op instanceof Join) {
			Join join = (Join) op;
			Operator join1 = outputOperator(new Join(pushProject(join.getLeft()),pushProject(join.getRight()),join.getPredicate()));
			List<Attribute> acAttrs = acceptAttributes(join1.getOutput().getAttributes());
			if (acAttrs.size()>0 && !acAttrs.equals(join1.getOutput().getAttributes())){
				return outputOperator(new Project(join1,acAttrs));
			}else{
				return join1;
			}
		}
		return op;
	}
	/*
     accept operator
	 */
	private Operator outputOperator(Operator op) {
		op.accept(new Estimator());
		return op;
	}

	/*
	get the predicate for one relation
	 */
	private ArrayList<Predicate> acceptPredicate(Relation relation){
		ArrayList<Predicate> acceptpredicates = new ArrayList<>();
		Iterator<Predicate> iter = allpredicates.iterator();
		while(iter.hasNext()){
			Predicate pre = iter.next();
			if(relation.getAttributes().contains(pre.getLeftAttribute()) && pre.equalsValue()){
				acceptpredicates.add(pre);
			}else if(relation.getAttributes().contains(pre.getLeftAttribute()) && relation.getAttributes().contains(pre.getRightAttribute())){
				acceptpredicates.add(pre);
			}
		}
        // sort predicate by estimator
		acceptpredicates.sort(Comparator.comparingInt(
				o -> (o.equalsValue() ? relation.getTupleCount() / relation.getAttribute(o.getLeftAttribute()).getValueCount() :
						(relation.getTupleCount() / Math.max(
						relation.getAttribute(o.getLeftAttribute()).getValueCount(),
						relation.getAttribute(o.getRightAttribute()).getValueCount())))));
		return acceptpredicates;
	}

	/*
	get the attributes to create new product
	 */
	private List<Attribute> acceptAttributes(List<Attribute> attrs){
		List<Attribute> acattributes = new ArrayList<>();
        for(Attribute attr:attrs){
				if(allattributes.contains(attr)){
					acattributes.add(attr);
			}
		}
		return acattributes;
	}
	/*
	 * method to get the operator type
	 */
	private String splitOperator(Operator operator) {
		return operator.getClass().getName().split("\\.")[1];
	}

    public void visit(Scan op) {
		allScans.add(new Scan((NamedRelation)op.getRelation()));
		allRelations.add(op.getRelation());
    }
    public void visit(Project op) {
		allattributes.addAll(op.getAttributes());
		topattributes.addAll(op.getOutput().getAttributes());
    }
    public void visit(Select op) {
        allpredicates.add(op.getPredicate());
		allattributes.add(op.getPredicate().getLeftAttribute());
		if(!op.getPredicate().equalsValue()){
			allattributes.add(op.getPredicate().getRightAttribute());
		}

    }
    public void visit(Product op) {
    }
    public void visit(Join op) {
		allattributes.add(op.getPredicate().getLeftAttribute());
		if(!op.getPredicate().equalsValue()){
			allattributes.add(op.getPredicate().getRightAttribute());
		}
    }
}