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

	private void safelyDeleteInst(InstructionHandle handle1, InstructionHandle handle2, InstructionList instList){
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
		doConstantVariableFolding(cgen,cpgen,instList);
		removeunnecessaryLDCs(instList);
		mg.removeNOPs();
		constantStack = new Stack<Number>();
		vars = new HashMap<Integer, Number>();

		boolean skipNextArith = false;

		boolean justDeletedIf = false;

		int constants = 0;
		ArrayList<Integer> arrayForLoops = findLoops(instList);

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
			//for simple folding, only LDC, LDC2_W, BIPUSH, SIPUSH and ConstantPush have to be considered.
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

	private boolean doLogicOp(InstructionHandle handle)
    {
        Instruction inst = handle.getInstruction();
        if (inst instanceof IFLE) {
            Number value1 = constantStack.pop();
            return (Integer) value1 <= 0;
        }

        Number first = constantStack.pop();
        Number second = constantStack.pop();

        // identify what kind of operation it is, and then perform the op.
        boolean result = false;
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