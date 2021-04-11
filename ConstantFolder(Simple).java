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