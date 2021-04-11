package comp0012.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
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

	private ArrayList<Integer> findLoops(InstructionList iList)
	{
		ArrayList<Integer> lPos = new ArrayList<>();

		for (InstructionHandle handle : iList.getInstructionHandles()) {
			Instruction inst = handle.getInstruction();

			if (inst instanceof IINC) {
				InstructionHandle nextInstructionHandle = handle.getNext();
				Instruction nextInstruction = nextInstructionHandle.getInstruction();
				Integer index = ((IINC) inst).getIndex();
				if (nextInstruction instanceof GotoInstruction) {
					InstructionHandle targetHandle = ((GotoInstruction) nextInstruction).getTarget();
					Integer start = targetHandle.getPosition() - 2;
					lPos.add(start);
					lPos.add(nextInstructionHandle.getPosition());
					lPos.add(index);
				}
			}

		}
		return lPos;
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


	private void doSimpleFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList il) {
		System.out.println("* * Optimization 01: Simple Folding --------------");

		boolean optimizationPerformed;
		do {
			InstructionFinder f = new InstructionFinder(il);
			// ConstantPushInstruction: BIPUSH, SIPUSH, ICONST, etc.
			// ConversionInstruction: I2D, D2F, etc.
			String pattern = "(LDC|LDC2_W|ConstantPushInstruction) ConversionInstruction? (LDC|LDC2_W|ConstantPushInstruction) ConversionInstruction? ArithmeticInstruction";

			// Info: InstructionHandle is a wrapper for actual Instructions

			optimizationPerformed = false;
			for (Iterator it = f.search(pattern); it.hasNext(); /* empty increment */) {
				InstructionHandle[] match = (InstructionHandle[]) it.next();

				System.out.println("Instruction len: " + match.length);
				for (InstructionHandle ih : match) {
					System.out.println("Instruction: " + ih.getInstruction().getClass().getSimpleName());
				}

				Number leftNum = null;
				Number rightNum = null;
				ArithmeticInstruction operator = null;
				ConversionInstruction conversionInstruction1 = null;	// May be null
				ConversionInstruction conversionInstruction2 = null;	// May be null

				int idx = 0;

				// Check type of left operand.
				if (match[idx].getInstruction() instanceof ConstantPushInstruction) {
					leftNum = ((ConstantPushInstruction) match[idx].getInstruction()).getValue();
				} else if (match[idx].getInstruction() instanceof LDC) {
					leftNum = (Number) ((LDC) match[idx].getInstruction()).getValue(cpgen);
				} else if (match[idx].getInstruction() instanceof LDC2_W) {
					leftNum = (Number) ((LDC2_W) match[idx].getInstruction()).getValue(cpgen);
				}

				idx++;

				// [OPTIONAL] Check if optional ConversionInstruction is present.
				if (match[idx].getInstruction() instanceof ConversionInstruction) {
					conversionInstruction1 = (ConversionInstruction) match[idx].getInstruction();
					idx++;
				}

				// Check type of right operand.
				if (match[idx].getInstruction() instanceof ConstantPushInstruction) {
					rightNum = ((ConstantPushInstruction) match[idx].getInstruction()).getValue();
				} else if (match[idx].getInstruction() instanceof LDC) {
					rightNum = (Number) ((LDC) match[idx].getInstruction()).getValue(cpgen);
				} else if (match[idx].getInstruction() instanceof LDC2_W) {
					rightNum = (Number) ((LDC2_W) match[idx].getInstruction()).getValue(cpgen);
				}

				idx++;

				// [OPTIONAL] Check if optional ConversionInstruction is present.
				if (match[idx].getInstruction() instanceof ConversionInstruction) {
					conversionInstruction2 = (ConversionInstruction) match[idx].getInstruction();
					idx++;
				}

				// Check operator type
				if (match[idx].getInstruction() instanceof ArithmeticInstruction) {
					operator = (ArithmeticInstruction) match[idx].getInstruction();
				}

				// Assert that we have the right types.
				if (leftNum == null || rightNum == null || operator == null) {
					System.err.println("FATAL: Operands or operator of unexpected type!");
				};

				// Fold the constant by type.
				Type operatorType = operator.getType(cpgen);
				String operationStr = operator.getName().substring(1);    // 'iadd', 'fmul', etc. -> 'add', 'mul', 'sub', 'div'

				System.out.println("leftNum: " + leftNum + " rightNum: " + rightNum + " type: " + operatorType + " operation: " + operationStr);

				Number foldedValue = doArithmeticOperation(leftNum, rightNum, operatorType, operationStr);

				if (foldedValue != null) {
					System.out.println("Folded value: " + foldedValue + " type: " + foldedValue.getClass().getName());

					// The index of the new value
					int cpIndex = -1;

					// Add result to constant pool.
					if (operatorType == Type.INT) {
						cpIndex = cpgen.addInteger(foldedValue.intValue());
					} else if (operatorType == Type.FLOAT) {
						cpIndex = cpgen.addFloat(foldedValue.floatValue());
					} else if (operatorType == Type.LONG) {
						cpIndex = cpgen.addLong(foldedValue.longValue());
					} else if (operatorType == Type.DOUBLE) {
						cpIndex = cpgen.addDouble(foldedValue.doubleValue());
					}

					System.out.println("New constant pool entry with index " + cpIndex + " and value " + foldedValue);

					if (cpIndex > -1) {
						// Insert new LDC instruction to load from our new constant pool entry.

						InstructionHandle instructionAddedHandle = null;
						if (operatorType == Type.INT || operatorType == Type.FLOAT) {
							instructionAddedHandle = il.insert(match[0], new LDC(cpIndex));
						} else if (operatorType == Type.LONG || operatorType == Type.DOUBLE) {
							instructionAddedHandle = il.insert(match[0], new LDC2_W(cpIndex));
						}

						// Use reflection to dynamically instantiate the right class.
						/*Constructor<?> ldcConstructor;
						CPInstruction cpInstruction = null;
						try {
							ldcConstructor = match[0].getInstruction().getClass().getConstructor(Integer.TYPE);
							cpInstruction = (CPInstruction) ldcConstructor.newInstance(cpIndex);
						} catch (Exception e) {
							e.printStackTrace();
						}
						il.insert(match[0], cpInstruction);*/

						try {
							// Delete old instructions (LDC ConversionInstruction? LDC ConversionInstruction? OP)
							il.delete(match[0], match[idx]);
						} catch (TargetLostException e) {
							for (InstructionHandle target : e.getTargets()) {
								for (InstructionTargeter targeter : target.getTargeters()) {
									if (instructionAddedHandle != null) {
										targeter.updateTarget(target, instructionAddedHandle);
									} else {
										System.err.println("Failed to fix targets to this instruction");
										e.printStackTrace();
									}
								}
							}
							//e.printStackTrace();
						}

						optimizationPerformed = true;
						System.out.println("Optimization performed.");
					}

				} else {
					System.out.format("WARNING: Folding fallthrough. Unsupported type %s - no optimization performed.\n", operatorType);
				}
			}
		} while (optimizationPerformed);
	}



	private Number doArithmeticOperation(Number lhs, Number rhs, Type operatorType, String operationStr) {
		Number result = null;
		switch (operationStr) {
			case OP_ADD:
				if (operatorType == Type.INT) {
					result = lhs.intValue() + rhs.intValue();
				} else if (operatorType == Type.LONG) {
					result = lhs.longValue() + rhs.longValue();
				} else if (operatorType == Type.FLOAT) {
					result = lhs.floatValue() + rhs.floatValue();
				} else if (operatorType == Type.DOUBLE) {
					result = lhs.doubleValue() + rhs.doubleValue();
				}
				break;
			case OP_SUB:
				if (operatorType == Type.INT) {
					result = lhs.intValue() - rhs.intValue();
				} else if (operatorType == Type.LONG) {
					result = lhs.longValue() - rhs.longValue();
				} else if (operatorType == Type.FLOAT) {
					result = lhs.floatValue() - rhs.floatValue();
				} else if (operatorType == Type.DOUBLE) {
					result = lhs.doubleValue() - rhs.doubleValue();
				}
				break;
			case OP_MUL:
				if (operatorType == Type.INT) {
					result = lhs.intValue() * rhs.intValue();
				} else if (operatorType == Type.LONG) {
					result = lhs.longValue() * rhs.longValue();
				} else if (operatorType == Type.FLOAT) {
					result = lhs.floatValue() * rhs.floatValue();
				} else if (operatorType == Type.DOUBLE) {
					result = lhs.doubleValue() * rhs.doubleValue();
				}
				break;
			case OP_DIV:
				if (operatorType == Type.INT) {
					result = lhs.intValue() / rhs.intValue();
				} else if (operatorType == Type.LONG) {
					result = lhs.longValue() / rhs.longValue();
				} else if (operatorType == Type.FLOAT) {
					result = lhs.floatValue() / rhs.floatValue();
				} else if (operatorType == Type.DOUBLE) {
					result = lhs.doubleValue() / rhs.doubleValue();
				}
				break;
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