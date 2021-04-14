package comp0012.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.sql.Struct;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Stack;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.*;
import org.apache.bcel.util.InstructionFinder;


public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;

	JavaClass original = null;
	JavaClass optimized = null;

	Stack<Number> constantStack = null;

	public ConstantFolder(String classFilePath)
	{
		try{
			this.parser = new ClassParser(classFilePath);
			this.original = this.parser.parse();
			this.gen = new ClassGen(this.original);
		} catch(IOException e){
			e.printStackTrace();
		}
	}

	private void safelyDeleteInst(InstructionHandle handle, InstructionList instList){
		//Delete Dead instructions without raising exceptions
		try {
			instList.delete(handle);
		} catch (TargetLostException e) {
			//redirect deleted targets to existing targets
			InstructionHandle[] targets = e.getTargets();
			InstructionHandle new_target = instList.getStart();
			for (InstructionHandle target : targets) {
				InstructionTargeter[] targeters = target.getTargeters();
				for (InstructionTargeter targeter : targeters)
					targeter.updateTarget(target, new_target);
			}
		}
	}

	private void safelyDeleteInst(InstructionHandle handle1, InstructionHandle handle2, InstructionList instList){
		//overloading method to delete multiple handles
		try {
			instList.delete(handle1, handle2);
		} catch (TargetLostException e) {
			InstructionHandle[] targets = e.getTargets();
			InstructionHandle new_target = instList.getStart();
			for (InstructionHandle target : targets) {
				InstructionTargeter[] targeters = target.getTargeters();
				for (InstructionTargeter targeter : targeters)
					targeter.updateTarget(target, new_target);
			}
		}
	}


	public void optimize()
	{
		ClassGen cgen = new ClassGen(original);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		// Implement your optimization here
		System.out.println("Starting optimisation on class " + cgen.getClassName());

		// Set major version to allow for a non-updated StackMapTable that BCEL cannot generate.
		cgen.setMajor(50);

		// Get the methods in the class.
		Method[] methods = cgen.getMethods();
		for (Method m : methods) {
			// Loop through each method, optimizing each.
			System.out.println("* Optimizing method " + m.getName() + "...");
			optimizeMethod(cgen, cpgen, m);
		}

		this.optimized = cgen.getJavaClass();
	}

	private void optimizeMethod(ClassGen cgen, ConstantPoolGen cpgen, Method method)
	{
		// Get the Code of the method, which is a collection of bytecode instructions
		Code methodCode = method.getCode();

		// Now get the actualy bytecode data in byte array,
		// and use it to initialise an InstructionList
		InstructionList instList = new InstructionList(methodCode.getCode());

		// Initialise a method generator with the original method as the baseline
		MethodGen mg = new MethodGen(method.getAccessFlags(), method.getReturnType(), method.getArgumentTypes(), null, method.getName(), cgen.getClassName(), instList, cpgen);

		doSimpleFolding(cgen, cpgen, instList);

		//Constant Var Folding is included in the DynamicFolding Method
		//but it still provides result that keeps the folded
		//doConstantVariableFolding(cgen,cpgen,instList);

		doDynamicFolding(cgen,cpgen,instList);
		removeunnecessaryLDCs(instList);
		mg.removeNOPs();
		//doDynamicFolding(cgen, cpgen, instList);
		instList.setPositions(true);

		// set max stack/local
		mg.setMaxStack();
		mg.setMaxLocals();

		// generate the new method with replaced iconst
		Method newMethod = mg.getMethod();
		// replace the method in the original class
		cgen.replaceMethod(method, newMethod);
		instList.dispose();
	}


	private void doSimpleFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList instList) {
		constantStack = new Stack<Number>();
		ArrayList<InstructionHandle> InstructionToRemove = new ArrayList<>();

		for (InstructionHandle handle:instList.getInstructionHandles()){
			InstructionHandle next = handle.getNext();
			Instruction inst = handle.getInstruction();
			boolean nextMatches = false;
			boolean isArithOp = inst instanceof ArithmeticInstruction;
			boolean isCmp = inst instanceof IfInstruction;
			boolean isLCMP = inst instanceof LCMP;
			if (next == null){
				nextMatches = false;
			} else {
				Instruction nextInst = next.getInstruction();
				if (nextInst instanceof ConversionInstruction || nextInst instanceof LDC || nextInst instanceof LDC2_W || nextInst instanceof ConstantPushInstruction || nextInst instanceof ArithmeticInstruction || nextInst instanceof IfInstruction || nextInst instanceof LCMP){
					nextMatches = true;
					//Only consider the simplest case: 2 continueous LDCs followed with an arithmeticInstruction, LCMP or ifInstruction (might have conversion between them)
				}
			}

			Number constant = null;
			//for simple folding, only LDC, LDC2_W, ConstantPush have to be considered.
			if (inst instanceof LDC && nextMatches){
				constant = (Number)((LDC)inst).getValue(cpgen);
				constantStack.push(constant);
				//push the constant to the stack, when an arithmetical or logical operation is met, the top 2 constant will be pop from the stack.
				InstructionToRemove.add(handle);
			} else if (inst instanceof LDC2_W && nextMatches){
				constant = (Number)((LDC2_W)inst).getValue(cpgen);
				constantStack.push(constant);
				InstructionToRemove.add(handle);
			} else if (inst instanceof ConstantPushInstruction && nextMatches){
				constant = ((ConstantPushInstruction)inst).getValue();
				constantStack.push(constant);
				InstructionToRemove.add(handle);
			} else if (isArithOp){
				if (constantStack.size() == 1){
					constantStack.pop();
					InstructionToRemove.clear();
					continue;
				} else if (constantStack.size() == 0) {
					InstructionToRemove.clear();
					continue;
				}
				//Avoid messing up the stack. This is because that store and load instructions are ignored.
				doArithOp(inst);

				for (InstructionHandle remove:InstructionToRemove){
					safelyDeleteInst(remove, instList);
					//remove the previous LDCs and Constantpushes that are already calculated.
				}
				Number result = constantStack.pop();

				if (result instanceof Integer){
					instList.insert(handle, new LDC(cpgen.addInteger((Integer)result)));
					//Pre-compute these arithmetical instructions, and then replace the arithmetical instructions with LDCs.
				} else if (result instanceof Float){
					instList.insert(handle, new LDC(cpgen.addFloat((Float)result)));
				} else if (result instanceof Double){
					instList.insert(handle, new LDC2_W(cpgen.addDouble((Double)result)));
				} else if (result instanceof Long){
					instList.insert(handle, new LDC2_W(cpgen.addLong((Long)result)));
				}
				constantStack.push(result);
				safelyDeleteInst(handle, instList);
				InstructionToRemove.clear();
			} else if (inst instanceof ConversionInstruction && nextMatches){
				InstructionToRemove.add(handle);
				//Delete the conversion, because the result is already calculated
			} else if (isCmp){
				if (constantStack.size() == 1 && !(inst instanceof IFLE)){
					//IFLE is a special case to be considered because it only requires to pop one constant from the stack
					constantStack.pop();
					InstructionToRemove.clear();
					continue;
				} else if (constantStack.size() == 0) {
					InstructionToRemove.clear();
					continue;
				}
				InstructionHandle ifTarget = ((IfInstruction) handle.getInstruction()).getTarget();
				InstructionHandle gotoHandle = handle.getNext();
				while (!(gotoHandle.getInstruction() instanceof GOTO)){
					gotoHandle = gotoHandle.getNext();
					if (gotoHandle == null){
						//goto not found, no else part
						if (doLogicOp(handle)){
							safelyDeleteInst(handle, instList);
							//If the comparison succeed, remove the ifnstruction.
						} else {
							safelyDeleteInst(handle, ifTarget.getPrev(), instList);
							//else remove the if part.
						}
					}
				}

				InstructionHandle gotoTarget = ((GotoInstruction) gotoHandle.getInstruction()).getTarget();

				if (gotoTarget.getPosition() < gotoHandle.getPosition()){
					constantStack.clear();
					InstructionToRemove.clear();
					continue;
					//do not consider loops
				}

				if (doLogicOp(handle)){
					safelyDeleteInst(gotoHandle, ifTarget, instList);
					safelyDeleteInst(handle, instList);
					//If the comparison succeed, remove the else part.
				} else {
					safelyDeleteInst(handle, gotoHandle, instList);
					//else remove the if part.
				}
				for (InstructionHandle remove:InstructionToRemove){
					safelyDeleteInst(remove, instList);
				}
				InstructionToRemove.clear();
			} else if (isLCMP){
				if (constantStack.size() == 1){
					constantStack.pop();
					InstructionToRemove.clear();
					continue;
				} else if (constantStack.size() == 0) {
					InstructionToRemove.clear();
					continue;
				}

				Number first = constantStack.pop();
				Number second = constantStack.pop();
				Number result;

				if ((Long) first > (Long) second) {
					result = 1;
				} else if ((Long) first < (Long) second) {
					result = -1;
				} else {
					result = 0;
				}

				constantStack.push(result);

				for (InstructionHandle remove:InstructionToRemove){
					safelyDeleteInst(remove, instList);
				}

				safelyDeleteInst(handle, instList);
				InstructionToRemove.clear();

			}
		}
	}

	private void doSimpleFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList instList, InstructionHandle endHandle) {
		//only fold part of the instructions
		constantStack = new Stack<Number>();
		ArrayList<InstructionHandle> InstructionToRemove = new ArrayList<>();
		for (InstructionHandle handle:instList.getInstructionHandles()){
			if (handle.equals(endHandle)){
				break;
			}
			InstructionHandle next = handle.getNext();
			Instruction inst = handle.getInstruction();
			boolean nextMatches = false;
			boolean isArithOp = inst instanceof ArithmeticInstruction;
			boolean isCmp = inst instanceof IfInstruction;
			boolean isLCMP = inst instanceof LCMP;
			if (next == null){
				nextMatches = false;
			} else {
				Instruction nextInst = next.getInstruction();
				if (nextInst instanceof ConversionInstruction || nextInst instanceof LDC || nextInst instanceof LDC2_W || nextInst instanceof ConstantPushInstruction || nextInst instanceof ArithmeticInstruction || nextInst instanceof IfInstruction || nextInst instanceof LCMP){
					nextMatches = true;
					//Only consider the simplest case: 2 continueous LDCs followed with an arithmeticInstruction, LCMP or ifInstruction (might have conversion between them)
				}
			}

			Number constant = null;
			//for simple folding, only LDC, LDC2_W, ConstantPush have to be considered.
			if (inst instanceof LDC && nextMatches){
				constant = (Number)((LDC)inst).getValue(cpgen);
				constantStack.push(constant);
				//push the constant to the stack, when an arithmetical or logical operation is met, the top 2 constant will be pop from the stack.
				InstructionToRemove.add(handle);
			} else if (inst instanceof LDC2_W && nextMatches){
				constant = (Number)((LDC2_W)inst).getValue(cpgen);
				constantStack.push(constant);
				InstructionToRemove.add(handle);
			} else if (inst instanceof ConstantPushInstruction && nextMatches){
				constant = ((ConstantPushInstruction)inst).getValue();
				constantStack.push(constant);
				InstructionToRemove.add(handle);
			} else if (isArithOp){
				if (constantStack.size() == 1){
					constantStack.pop();
					InstructionToRemove.clear();
					continue;
				} else if (constantStack.size() == 0) {
					InstructionToRemove.clear();
					continue;
				}
				//Avoid messing up the stack. This is because that store and load instructions are ignored.
				doArithOp(inst);

				for (InstructionHandle remove:InstructionToRemove){
					safelyDeleteInst(remove, instList);
					//remove the previous LDCs and Constantpushes that are already calculated.
				}
				Number result = constantStack.pop();

				if (result instanceof Integer){
					instList.insert(handle, new LDC(cpgen.addInteger((Integer)result)));
					//Pre-compute these arithmetical instructions, and then replace the arithmetical instructions with LDCs.
				} else if (result instanceof Float){
					instList.insert(handle, new LDC(cpgen.addFloat((Float)result)));
				} else if (result instanceof Double){
					instList.insert(handle, new LDC2_W(cpgen.addDouble((Double)result)));
				} else if (result instanceof Long){
					instList.insert(handle, new LDC2_W(cpgen.addLong((Long)result)));
				}
				constantStack.push(result);
				safelyDeleteInst(handle, instList);
				InstructionToRemove.clear();
			} else if (inst instanceof ConversionInstruction && nextMatches){
				InstructionToRemove.add(handle);
				//Delete the conversion, because the result is already calculated
			} else if (isCmp){
				if (constantStack.size() == 1 && !(inst instanceof IFLE)){
					//IFLE is a special case to be considered because it only requires to pop one constant from the stack
					constantStack.pop();
					InstructionToRemove.clear();
					continue;
				} else if (constantStack.size() == 0) {
					InstructionToRemove.clear();
					continue;
				}
				InstructionHandle ifTarget = ((IfInstruction) handle.getInstruction()).getTarget();
				InstructionHandle gotoHandle = handle.getNext();
				while (!(gotoHandle.getInstruction() instanceof GOTO)){
					gotoHandle = gotoHandle.getNext();
					if (gotoHandle == null){
						//goto not found, no else part
						if (doLogicOp(handle)){
							safelyDeleteInst(handle, instList);
							//If the comparison succeed, remove the ifnstruction.
						} else {
							safelyDeleteInst(handle, ifTarget.getPrev(), instList);
							//else remove the if part.
						}
					}
				}

				InstructionHandle gotoTarget = ((GotoInstruction) gotoHandle.getInstruction()).getTarget();

				if (gotoTarget.getPosition() < gotoHandle.getPosition()){
					constantStack.clear();
					InstructionToRemove.clear();
					continue;
					//do not consider loops
				}

				if (doLogicOp(handle)){
					safelyDeleteInst(gotoHandle, ifTarget, instList);
					safelyDeleteInst(handle, instList);
					//If the comparison succeed, remove the else part.
				} else {
					safelyDeleteInst(handle, gotoHandle, instList);
					//else remove the if part.
				}
				for (InstructionHandle remove:InstructionToRemove){
					safelyDeleteInst(remove, instList);
				}
				InstructionToRemove.clear();
			} else if (isLCMP){
				if (constantStack.size() == 1){
					constantStack.pop();
					InstructionToRemove.clear();
					continue;
				} else if (constantStack.size() == 0) {
					InstructionToRemove.clear();
					continue;
				}

				Number first = constantStack.pop();
				Number second = constantStack.pop();
				Number result;

				if ((Long) first > (Long) second) {
					result = 1;
				} else if ((Long) first < (Long) second) {
					result = -1;
				} else {
					result = 0;
				}

				constantStack.push(result);

				for (InstructionHandle remove:InstructionToRemove){
					safelyDeleteInst(remove, instList);
				}

				safelyDeleteInst(handle, instList);
				InstructionToRemove.clear();

			}
		}
	}

	private HashMap<Integer, Boolean> findConstantVar(ClassGen cgen, ConstantPoolGen cpgen, InstructionList instList){
		InstructionHandle start = instList.getStart();
		InstructionHandle end = instList.getEnd();

		HashMap<Integer, Boolean> Vars = new HashMap<>();

		InstructionFinder finder = new InstructionFinder(instList);
		String keyword = "StoreInstruction | IINC";

		for (Iterator it = finder.search(keyword, start); it.hasNext();) {
			InstructionHandle[] handles = (InstructionHandle[]) it.next();

			if (handles[0].getPosition() > end.getPosition()) {
				continue;
			}

			int localIdx = -1;

			if (handles[0].getInstruction() instanceof IINC) {
				localIdx = ((IINC) handles[0].getInstruction()).getIndex();
			} else if (handles[0].getInstruction() instanceof StoreInstruction) {
				localIdx = ((StoreInstruction) handles[0].getInstruction()).getIndex();
			}

			if (localIdx == -1) {
				System.err.println("FATAL: doConstantVariableFolding: localIdx not assigned.");
			}

			if (!Vars.containsKey(localIdx)) {
				Vars.put(localIdx, true);
			} else {
				Vars.put(localIdx, false);
				doDynamicFolding(cgen, cpgen, instList);
				break;
				//do dynamic only when dynamic variable is found
			}
		}
		return Vars;
	}


	private void doConstantVariableFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList instList){

		HashMap<Integer,Number> literalValues = new HashMap<>();
		HashMap<Integer, Boolean> constantVars = new HashMap<>();

		constantVars = findConstantVar(cgen, cpgen, instList);

		boolean folding = true;
		while (folding){
			InstructionFinder finder = new InstructionFinder(instList);
			String pattern = "(LDC | LDC2_W | LDC_W | ConstantPushInstruction) (DSTORE | FSTORE | ISTORE | LSTORE)";
			folding = false;
			doSimpleFolding(cgen,cpgen,instList);
			finder = new InstructionFinder(instList);

			for (Iterator it = finder.search(pattern); it.hasNext();){
				InstructionHandle[] set = (InstructionHandle[]) it.next();
				PushInstruction push = (PushInstruction) set[0].getInstruction();
				StoreInstruction store = (StoreInstruction) set[1].getInstruction();
				Number val = null;

				//skip if store is not constant
				if (!constantVars.containsKey(store.getIndex()) || !constantVars.get(store.getIndex())) {
					continue;
				}

				if(push instanceof LDC){
					val = (Number) ((LDC) push).getValue(cpgen);
				}
				else if (push instanceof LDC2_W){
					val = ((LDC2_W) push).getValue(cpgen);
				}
				else if (push instanceof ConstantPushInstruction){
					val = ((ConstantPushInstruction) push).getValue();
				}

				if (val == null){
					System.err.println("FATAL: Could not obtain literal value for unknown type");
				}

				literalValues.put(store.getIndex(), val);
			}

			//finder = new InstructionFinder(instList);
			String patternAlt = "(DLOAD | FLOAD | ILOAD | LLOAD)";

			for (Iterator itAlt = finder.search(patternAlt); itAlt.hasNext();) {
				InstructionHandle[] set = (InstructionHandle[]) itAlt.next();

				// set[0] expected to be LoadInstruction, as specified in the pattern (it's the superclass of the specified pattern).
				LoadInstruction load = (LoadInstruction) set[0].getInstruction();

				// Check if the index exists in the hashmap.
				if (literalValues.containsKey(load.getIndex())) {
					Instruction added = null;

					Number val = literalValues.get(load.getIndex());

					if (load.getType(cpgen) == Type.FLOAT) {
						added = new LDC(cpgen.addFloat(val.floatValue()));
					} else if (load.getType(cpgen) == Type.DOUBLE) {
						added = new LDC2_W(cpgen.addDouble(val.doubleValue()));
					} else if (load.getType(cpgen) == Type.LONG) {
						added = new LDC2_W(cpgen.addLong(val.longValue()));
					} else if (load.getType(cpgen) == Type.INT) {
						if (false && Math.abs(val.intValue()) < Byte.MAX_VALUE) {
							added = new BIPUSH(val.byteValue());
						} else if (false && Math.abs(val.intValue()) < Short.MAX_VALUE) {
							added = new SIPUSH(val.shortValue());
						} else {
							added = new LDC(cpgen.addInteger(val.intValue()));
						}
					}

					// Assert that there's an instruction to add.
					assert added != null;

					InstructionHandle instructionAddedHandle = instList.insert(set[0], added);

					try {
						// Delete old instructions (loadInstruction)
						instList.delete(set[0]);
					} catch (TargetLostException e) {
						for (InstructionHandle target : e.getTargets()) {
							for (InstructionTargeter targeter : target.getTargeters()) {
								targeter.updateTarget(target, instructionAddedHandle);
							}
						}
					}
					folding = true;
				}
			}
		}
	}

	private HashMap<Integer, Boolean> findLoadStore(ClassGen cgen, ConstantPoolGen cpgen, InstructionList instList){
		HashMap<Integer, Boolean> inLoop = new HashMap<>();
		for (InstructionHandle handle:instList.getInstructionHandles()){
			Instruction inst = handle.getInstruction();
			if (inst instanceof GOTO){
				if (((GotoInstruction)inst).getTarget().getPosition() < handle.getPosition()){
					InstructionHandle inLoopLoad = ((GotoInstruction)inst).getTarget();
					inLoop.put(((LoadInstruction)inLoopLoad.getInstruction()).getIndex(), true);
					//find all load and store instructions that are used for loops, do not remove them.
				}
			}
		}
		return inLoop;
	}

	private void doDynamicFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList instList){
		HashMap<Integer, Boolean> inLoopLoadsAndStores = new HashMap<>();
		HashMap<Integer, Number> variables = new HashMap<>();

		inLoopLoadsAndStores = findLoadStore(cgen,cpgen,instList);

		Stack<Number> constantStack = new Stack<>();
		Stack<InstructionHandle> handlesToRemove = new Stack<>();
		boolean optimisationEnds = false;

		while(!optimisationEnds){

			optimisationEnds = true;
			//repeat until all the store and load instructions are removed

			for (InstructionHandle handle:instList.getInstructionHandles()){
				Instruction inst = handle.getInstruction();
				InstructionHandle next = handle.getNext();
				boolean nextIsStore = false;
				boolean nextInLoop = false;

				if (next != null){
					Instruction nextInst = next.getInstruction();
					if (nextInst instanceof StoreInstruction){
						nextIsStore = true;
						if (inLoopLoadsAndStores.containsKey(((StoreInstruction)nextInst).getIndex())){
							nextInLoop = true;
						}
						//only consider those LDCs followed with a store instruction
					}
				}

				if (inst instanceof LDC && nextIsStore && (!nextInLoop)){
					Number constant = (Number)((LDC)inst).getValue(cpgen);
					constantStack.push(constant);
					//push the constant to the stack, pop one when a store is met.
					handlesToRemove.push(handle);
				} else if (inst instanceof LDC2_W && nextIsStore && (!nextInLoop)){
					Number constant = (Number)((LDC2_W)inst).getValue(cpgen);
					constantStack.push(constant);
					handlesToRemove.push(handle);
				} else if (inst instanceof ConstantPushInstruction && nextIsStore && (!nextInLoop)){
					Number constant = ((ConstantPushInstruction)inst).getValue();
					constantStack.push(constant);
					handlesToRemove.push(handle);
				}

				if (inst instanceof StoreInstruction && !(inLoopLoadsAndStores.containsKey(((StoreInstruction)inst).getIndex()))){

					if (constantStack.size() == 0){
						optimisationEnds = false;
						//Not yet able to get this store value, skip
						doSimpleFolding(cgen, cpgen, instList, handle);
						//fold the previous instructions
						break;
						//end this loop and start a new one
					}

					Number value = constantStack.pop();
					int key = ((StoreInstruction)inst).getIndex();

					if (variables.containsKey(key)){
						variables.replace(key, value);
						//replace the previous value
					} else {
						variables.put(key, value);
					}
					safelyDeleteInst(handlesToRemove.pop(), instList);
					//remove the previous LDC used to store
					safelyDeleteInst(handle, instList);
					//remove the unnecessary store instruction
				}

				if (inst instanceof LoadInstruction && !(inst instanceof ALOAD) && !(inLoopLoadsAndStores.containsKey(((LoadInstruction)inst).getIndex()))){

					int key = ((LoadInstruction)inst).getIndex();
					Number value = variables.get(key);

					if (value instanceof Integer){
						instList.insert(handle, new LDC(cpgen.addInteger((Integer)value)));
					} else if (value instanceof Float){
						instList.insert(handle, new LDC(cpgen.addFloat((Float)value)));
					} else if (value instanceof Double){
						instList.insert(handle, new LDC2_W(cpgen.addDouble((Double)value)));
					} else if (value instanceof Long){
						instList.insert(handle, new LDC2_W(cpgen.addLong((Long)value)));
					}
					//replace the load instructions with LDCs
					safelyDeleteInst(handle, instList);
				}
			}
		}
		doSimpleFolding(cgen, cpgen, instList);
		removeunnecessaryLDCs(instList);
		//After all store and load are removed, generally do a simple folding.
		redirectTargetsInLoops(instList);
		//Sometimes removing instructions could cause a ifInstruction of a loop to lose its target, fix it.
	}

	private void removeunnecessaryLDCs(InstructionList instList){
		for (InstructionHandle handle:instList.getInstructionHandles()){
			InstructionHandle next = handle.getNext();

			if (next != null){
				if ((handle.getInstruction() instanceof LDC || handle.getInstruction() instanceof LDC2_W) && (next.getInstruction() instanceof LDC || next.getInstruction() instanceof LDC2_W)){
					if (next.getNext() != null && next.getNext().getInstruction() instanceof IfInstruction){
						continue;
					}
					safelyDeleteInst(handle, instList);
				}
			}
		}
	}

	private void doArithOp(Instruction inst){

		if (constantStack.size() < 2){ return; }
		Number first = constantStack.pop();
		Number second = constantStack.pop();
		Number result = null;

		//Do calculation.
		if (inst instanceof IADD) {
			result = second.intValue() + first.intValue();
			constantStack.push(result);
		} else if (inst instanceof LADD) {
			result = second.longValue() + first.longValue();
			constantStack.push(result);
		} else if (inst instanceof FADD) {
			result = second.floatValue() + first.floatValue();
			constantStack.push(result);
		} else if (inst instanceof DADD) {
			result = second.doubleValue() + first.doubleValue();
			constantStack.push(result);
		} else if (inst instanceof IMUL) {
			result = second.intValue() * first.intValue();
			constantStack.push(result);
		} else if (inst instanceof LMUL) {
			result = second.longValue() * first.longValue();
			constantStack.push(result);
		} else if (inst instanceof FMUL) {
			result = second.floatValue() * first.floatValue();
			constantStack.push(result);
		} else if (inst instanceof DMUL) {
			result = second.doubleValue() * first.doubleValue();
			constantStack.push(result);
		} else if (inst instanceof ISUB) {
			result = second.intValue() - first.intValue();
			constantStack.push(result);
		} else if (inst instanceof LSUB) {
			result = second.longValue() - first.longValue();
			constantStack.push(result);
		} else if (inst instanceof FSUB) {
			result = second.floatValue() - first.floatValue();
			constantStack.push(result);
		} else if (inst instanceof DSUB) {
			result = second.doubleValue() - first.doubleValue();
			constantStack.push(result);
		} else if (inst instanceof IDIV) {
			result = second.intValue() / first.intValue();
			constantStack.push(result);
		} else if (inst instanceof LDIV) {
			result = second.longValue() / first.longValue();
			constantStack.push(result);
		} else if (inst instanceof FDIV) {
			result = second.floatValue() / first.floatValue();
			constantStack.push(result);
		} else if (inst instanceof DDIV) {
			result = second.doubleValue() / first.doubleValue();
			constantStack.push(result);
		}
	}

	private boolean doLogicOp(InstructionHandle handle) {
		//
		Instruction inst = handle.getInstruction();

		if (inst instanceof IFLE) {
			Number value1 = constantStack.pop();
			return (Integer) value1 <= 0;
			//IFLE only needs one pop
		}

		Number first = constantStack.pop();
		Number second = constantStack.pop();
		boolean result = false;

		//get the result of the comparison
		if (inst instanceof IF_ICMPEQ) {
			if (first.equals(second)) {
				result = true;
			}
		} else if (inst instanceof IF_ICMPGE) {
			if ((Integer) first >= (Integer) second) {
				result = true;
			}
		} else if (inst instanceof IF_ICMPGT) {
			if ((Integer) first > (Integer) second) {
				result = true;
			}
		} else if (inst instanceof IF_ICMPLE) {
			if ((Integer) first <= (Integer) second) {
				result = true;
			}
		} else if (inst instanceof IF_ICMPLT) {
			if ((Integer) first < (Integer) second) {
				result = true;
			}
		} else if (inst instanceof IF_ICMPNE) {
			if (!first.equals(second)) {
				result = true;
			}
		}
		return result;
	}

	public void redirectTargetsInLoops(InstructionList instList){
		int loopCount = 0;
		for (InstructionHandle handle:instList.getInstructionHandles()){
			Instruction inst = handle.getInstruction();
			if (inst instanceof GOTO){
				loopCount++;
				//record which goto it is, and find the corresponding if.
				if (((GotoInstruction)inst).getTarget().getPosition() < handle.getPosition()){
					int thisCount = loopCount;
					InstructionHandle ifHandle = null;
					InstructionHandle prev = handle.getPrev();
					while (prev != null && thisCount > 0){
						if (prev.getInstruction() instanceof IfInstruction){
							ifHandle = prev;
							thisCount--;
						}
						prev = prev.getPrev();
					}
					if (ifHandle != null){
						Instruction ifInst = ifHandle.getInstruction();
						//replace the old ifInstruction with a new one targeting the instruction next to the goto
						if (ifInst instanceof IF_ICMPEQ){
							instList.insert(ifHandle, new IF_ICMPEQ(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IF_ICMPGE){
							instList.insert(ifHandle, new IF_ICMPGE(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IF_ICMPGT){
							instList.insert(ifHandle, new IF_ICMPGT(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IF_ICMPLE){
							instList.insert(ifHandle, new IF_ICMPLE(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IF_ICMPLT){
							instList.insert(ifHandle, new IF_ICMPLT(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IF_ICMPNE){
							instList.insert(ifHandle, new IF_ICMPNE(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IFEQ){
							instList.insert(ifHandle, new IFEQ(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IFGE){
							instList.insert(ifHandle, new IFGE(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IFGT){
							instList.insert(ifHandle, new IFGT(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IFLE){
							instList.insert(ifHandle, new IFLE(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IFLT){
							instList.insert(ifHandle, new IFLT(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						} else if(ifInst instanceof IFNE){
							instList.insert(ifHandle, new IFNE(handle.getNext()));
							safelyDeleteInst(ifHandle, instList);
						}
					}
				}
			}
		}
	}

	public void write(String optimisedFilePath)
	{
		this.optimize();

		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
	}
}