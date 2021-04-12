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
	HashMap<Integer, Number> vars = null;

	public static final String OP_ADD = "add";
	public static final String OP_SUB = "sub";
	public static final String OP_MUL = "mul";
	public static final String OP_DIV = "div";


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

	private ArrayList<Integer> findLoops(InstructionList instList)
	{
		ArrayList<Integer> loopPosition = new ArrayList<>();

		for (InstructionHandle handle : instList.getInstructionHandles()) {
			Instruction inst = handle.getInstruction();

			if (inst instanceof IINC) {
				InstructionHandle nextInstructionHandle = handle.getNext();
				Instruction nextInstruction = nextInstructionHandle.getInstruction();
				Integer index = ((IINC) inst).getIndex();
				if (nextInstruction instanceof GotoInstruction) {
					InstructionHandle targetHandle = ((GotoInstruction) nextInstruction).getTarget();
					Integer start = targetHandle.getPosition() - 2;
					loopPosition.add(start);
					loopPosition.add(nextInstructionHandle.getPosition());
					loopPosition.add(index);
				}
			}

		}
		return loopPosition;
	}

	private void safelyDeleteInst(InstructionHandle handle, InstructionList instList){
		try {
			instList.delete(handle);
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
		doConstantVariableFolding(cgen,cpgen,instList);
		mg.removeNOPs();
		constantStack = new Stack<Number>();
		vars = new HashMap<Integer, Number>();

		boolean skipNextArith = false;

		boolean justDeletedIf = false;

		int constants = 0;
		ArrayList<Integer> arrayForLoops = findLoops(instList);

		doSimpleFolding(cgen, cpgen, instList);
		// InstructionHandle is a wrapper for actual Instructions

		// setPositions(true) checks whether jump handles
		// are all within the current method
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
		System.out.println("* * Optimization 01: Simple Folding --------------");
		constantStack = new Stack<Number>();
		for (InstructionHandle handle:instList.getInstructionHandles()){
			InstructionHandle next = handle.getNext();
			boolean nextIsStore = false;
			if (next != null && next.getInstruction() instanceof StoreInstruction){
				nextIsStore = true;
				//do not consider store and load since it is only simple folding.
			}
			Instruction inst = handle.getInstruction();
			Number constant = null;
			boolean isArithOp = (inst instanceof ArithmeticInstruction);
			//for simple folding, only LDC, LDC2_W, BIPUSH, SIPUSH and ConstantPush have to be considered.
			if (inst instanceof LDC && !nextIsStore){
				constant = (Number)((LDC)inst).getValue(cpgen);
				constantStack.push(constant);
				//push the constant to the stack, when an arithmetical or logical operation is met, the top 2 constant will be pop from the stack.
			} else if (inst instanceof LDC2_W && !nextIsStore){
				constant = (Number)((LDC2_W)inst).getValue(cpgen);
				constantStack.push(constant);
			} else if (inst instanceof BIPUSH && !nextIsStore){
				constant = ((BIPUSH)inst).getValue();
				constantStack.push(constant);
			} else if (inst instanceof SIPUSH && !nextIsStore){
				constant = ((SIPUSH)inst).getValue();
				constantStack.push(constant);
			} else if (inst instanceof ConstantPushInstruction && !nextIsStore){
				constant = ((ConstantPushInstruction)inst).getValue();
				constantStack.push(constant);
			} else if (isArithOp){
				if (constantStack.size() == 1){
					constantStack.pop();
					continue;
				} else if (constantStack.size() == 0) { continue; }
				//Avoid messing up the stack. This is because that store and load instructions are ignored.
				performArithOp(inst);
				removePrevLDCs(handle, instList, 2);//remove the previous 2 LDCs because the arithmetical instruction on these two is already computed.
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
			}
		}
	}

	/*private void doConstantVariableFold(ClassGen cgen, ConstantPoolGen cpgen, InstructionList il, InstructionHandle startHandle, InstructionHandle endHandle) {
		System.out.println("* * Optimization 02: Constant Variable Folding --------------");

		// Fill defaults
		if (startHandle == null) {
			startHandle = il.getStart();
		}
		if (endHandle == null) {
			endHandle = il.getEnd();
		}

		// This hashmap stores all literal values that we know about.
		HashMap<Integer,Number> literalValues = new HashMap<>();

		// This hashmap stores a list of local variables that are *constant* for this method.
		// constantVariables.get(index) is TRUE if the variable is constant.
		HashMap<Integer, Boolean> constantVariables = new HashMap<>();

		// Locate constant local variables that do not change for this method.
		InstructionFinder f = new InstructionFinder(il);
		String pattern = "StoreInstruction | IINC";
		for (Iterator it = f.search(pattern, startHandle); it.hasNext(); ) {
			InstructionHandle[] match = (InstructionHandle[]) it.next();

			if (match[0].getPosition() > endHandle.getPosition()) {
				continue;
			}

			int localVariableIndex = -1;

			// match[0] expected to be StoreInstruction or IINC, as specified in the pattern.
			if (match[0].getInstruction() instanceof StoreInstruction) {
				localVariableIndex = ((StoreInstruction) match[0].getInstruction()).getIndex();
			} else if (match[0].getInstruction() instanceof IINC) {
				localVariableIndex = ((IINC) match[0].getInstruction()).getIndex();
			}

			// Assert we've assigned a value to localVariableIndex.
			if (localVariableIndex == -1) {
				System.err.println("FATAL: doConstantVariableFolding: localVariableIndex not assigned.");
			}

			System.out.format("storeInstruction: %s index: %s\n", match[0].getInstruction().getClass().getSimpleName(), localVariableIndex);

			// See if we've already tracked this local variable.
			if (!constantVariables.containsKey(localVariableIndex)) {
				constantVariables.put(localVariableIndex, true);
			} else {
				// We've seen this index before.. mark it as NOT constant.
				constantVariables.put(localVariableIndex, false);
			}
		}

		// The loop will end when there are no longer any LoadInstructions whose index exists in the literalValues hashmap.
		boolean foldedLoadInstruction;
		do {
			// Run simple folding to get as many literals as possible.
			doSimpleFolding(cgen, cpgen, il);

			// Store all literals in the hashmap.
			// e.g. LDC #2, ISTORE_1
			// e.g. SIPUSH 1234, ISTORE_2
			f = new InstructionFinder(il);
			String pattern2 = "(LDC | LDC2_W | LDC_W | ConstantPushInstruction) (DSTORE | FSTORE | ISTORE | LSTORE)";
			for (Iterator it = f.search(pattern2); it.hasNext(); ) {
				InstructionHandle[] match = (InstructionHandle[]) it.next();

				// match[0] expected to be PushInstruction, as specified in the pattern (it's the superclass of the specified pattern).
				PushInstruction pushInstruction = (PushInstruction) match[0].getInstruction();

				// match[1] expected to be StoreInstruction, as specified in the pattern.
				StoreInstruction storeInstruction = (StoreInstruction) match[1].getInstruction();

				// Check if this store instruction is for a constant variable.
				if (!constantVariables.containsKey(storeInstruction.getIndex()) || !constantVariables.get(storeInstruction.getIndex())) {
					// If the variable isn't constant, skip this iteration.
					continue;
				}

				Number literalValue = null;

				// Get the constant value pushed.
				if (pushInstruction instanceof ConstantPushInstruction) {
					literalValue = ((ConstantPushInstruction) pushInstruction).getValue();
				} else if (pushInstruction instanceof LDC) {
					// LDC must be Number since we only accept ILOAD, FLOAD, etc.
					literalValue = (Number) ((LDC) pushInstruction).getValue(cpgen);
				} else if (pushInstruction instanceof LDC2_W) {
					literalValue = ((LDC2_W) pushInstruction).getValue(cpgen);
				}

				// Assert that we've assigned a value to literalValue.
				if (literalValue == null) {
					System.err.format("FATAL: Could not obtain literal value for unknown type %s.\n", pushInstruction.getClass().getSimpleName());
				}

				System.out.format("pushInstruction: %s storeInstruction: %s index: %d value: %f\n", pushInstruction.getClass().getSimpleName(), storeInstruction.getClass().getSimpleName(), storeInstruction.getIndex(), literalValue.doubleValue());

				// Store the literal value in the literalValues hashmap.
				literalValues.put(storeInstruction.getIndex(), literalValue);
			}

			// Look for LoadInstruction and check if the index exists in the hashmap.
			// If it does, replace the LoadInstruction with the literal value.
			foldedLoadInstruction = false;
			f = new InstructionFinder(il);
			String pattern3 = "(DLOAD | FLOAD | ILOAD | LLOAD)";
			for (Iterator it = f.search(pattern3); it.hasNext(); ) {
				InstructionHandle[] match = (InstructionHandle[]) it.next();

				// match[0] expected to be LoadInstruction, as specified in the pattern (it's the superclass of the specified pattern).
				LoadInstruction loadInstruction = (LoadInstruction) match[0].getInstruction();

				System.out.format("loadInstruction: %s index: %s\n", loadInstruction.getClass().getSimpleName(), loadInstruction.getIndex());

				// Check if the index exists in the hashmap.
				if (literalValues.containsKey(loadInstruction.getIndex())) {
					// Yes, it does!
					// Replace the LoadInstruction with the literal value.

					Number literalValue = literalValues.get(loadInstruction.getIndex());

					Instruction instructionAdded = null;

					if (loadInstruction.getType(cpgen) == Type.INT) {
						if (false && Math.abs(literalValue.intValue()) < Byte.MAX_VALUE) {
							instructionAdded = new BIPUSH(literalValue.byteValue());
						} else if (false && Math.abs(literalValue.intValue()) < Short.MAX_VALUE) {
							instructionAdded = new SIPUSH(literalValue.shortValue());
						} else {
							// We need to add to the constant pool.
							instructionAdded = new LDC(cpgen.addInteger(literalValue.intValue()));
						}
					} else if (loadInstruction.getType(cpgen) == Type.FLOAT) {
						// Need to add to the constant pool.
						instructionAdded = new LDC(cpgen.addFloat(literalValue.floatValue()));
					} else if (loadInstruction.getType(cpgen) == Type.DOUBLE) {
						// Need to add to the constant pool.
						instructionAdded = new LDC2_W(cpgen.addDouble(literalValue.doubleValue()));
					} else if (loadInstruction.getType(cpgen) == Type.LONG) {
						// Need to add to the constant pool.
						instructionAdded = new LDC2_W(cpgen.addLong(literalValue.longValue()));
					}

					// Assert that there's an instruction to add.
					assert instructionAdded != null;

					InstructionHandle instructionAddedHandle = il.insert(match[0], instructionAdded);

					try {
						// Delete old instructions (loadInstruction)
						il.delete(match[0]);
					} catch (TargetLostException e) {
						for (InstructionHandle target : e.getTargets()) {
							for (InstructionTargeter targeter : target.getTargeters()) {
								targeter.updateTarget(target, instructionAddedHandle);
							}
						}
						//e.printStackTrace();
					}

					foldedLoadInstruction = true;

					System.out.format("Replaced %s %d with %s %f.\n", loadInstruction.getClass().getSimpleName(), loadInstruction.getIndex(), instructionAdded.getClass().getSimpleName(), literalValue.doubleValue());
				}
			}
		} while (foldedLoadInstruction);

//		// setPositions(true) checks whether jump handles
//		// are all within the current method
//		il.setPositions(true);
//
//		// Recompute max stack/locals.
//		methodGen.setMaxStack();
//		methodGen.setMaxLocals();
//
//		// Generate the new method.
//		Method newMethod = methodGen.getMethod();
//
//		// Replace the method in the original class.
//		cgen.replaceMethod(m, newMethod);
//
//		// Dispose so that instruction handles can be reused. (Just good practice.)
//		il.dispose();
	}*/


	private void doConstantVariableFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList instList){
		InstructionHandle start = instList.getStart();
		InstructionHandle end = instList.getEnd();

		HashMap<Integer,Number> literalValues = new HashMap<>();
		HashMap<Integer, Boolean> constantVars = new HashMap<>();


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

			if (!constantVars.containsKey(localIdx)) {
				constantVars.put(localIdx, true);
			} else {
				constantVars.put(localIdx, false);
			}
		}

		boolean folding = true;
		while (folding){

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


	private void removePrevLDCs(InstructionHandle handle, InstructionList instList, int deleteCount){
		if (deleteCount > 2){
			deleteCount = 2;
		}
		InstructionHandle prev = handle.getPrev();
		if (prev == null) { return; }
		while (deleteCount > 0){
			if (prev.getInstruction() instanceof LDC || prev.getInstruction() instanceof LDC2_W){
				if (prev.getPrev() == null){
					safelyDeleteInst(prev, instList);
					break;
				} // reaching the start of the list
				prev = prev.getPrev();
				safelyDeleteInst(prev.getNext(), instList);
				deleteCount--;
			} else {
				if (prev.getPrev() == null) { break; }
				prev = prev.getPrev();
			}
		}
	}

	private void performArithOp(Instruction inst){
		if (constantStack.size() < 2){ return; }
		Number first = constantStack.pop();
		Number second = constantStack.pop();
		Number newValue = null;
		//Do calculation.
		if (inst instanceof IADD) {
			newValue = second.intValue() + first.intValue();
			constantStack.push(newValue);
		} else if (inst instanceof LADD) {
			newValue = second.longValue() + first.longValue();
			constantStack.push(newValue);
		} else if (inst instanceof FADD) {
			newValue = second.floatValue() + first.floatValue();
			constantStack.push(newValue);
		} else if (inst instanceof DADD) {
			newValue = second.doubleValue() + first.doubleValue();
			constantStack.push(newValue);
		} else if (inst instanceof IMUL) {
			newValue = second.intValue() * first.intValue();
			constantStack.push(newValue);
		} else if (inst instanceof LMUL) {
			newValue = second.longValue() * first.longValue();
			constantStack.push(newValue);
		} else if (inst instanceof FMUL) {
			newValue = second.floatValue() * first.floatValue();
			constantStack.push(newValue);
		} else if (inst instanceof DMUL) {
			newValue = second.doubleValue() * first.doubleValue();
			constantStack.push(newValue);
		} else if (inst instanceof ISUB) {
			newValue = second.intValue() - first.intValue();
			constantStack.push(newValue);
		} else if (inst instanceof LSUB) {
			newValue = second.longValue() - first.longValue();
			constantStack.push(newValue);
		} else if (inst instanceof FSUB) {
			newValue = second.floatValue() - first.floatValue();
			constantStack.push(newValue);
		} else if (inst instanceof DSUB) {
			newValue = second.doubleValue() - first.doubleValue();
			constantStack.push(newValue);
		} else if (inst instanceof IDIV) {
			newValue = second.intValue() / first.intValue();
			constantStack.push(newValue);
		} else if (inst instanceof LDIV) {
			newValue = second.longValue() / first.longValue();
			constantStack.push(newValue);
		} else if (inst instanceof FDIV) {
			newValue = second.floatValue() / first.floatValue();
			constantStack.push(newValue);
		} else if (inst instanceof DDIV) {
			newValue = second.doubleValue() / first.doubleValue();
			constantStack.push(newValue);
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