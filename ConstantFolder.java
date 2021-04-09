package comp0012.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Iterator;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.util.InstructionFinder;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.TargetLostException;



public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;

	JavaClass original = null;
	JavaClass optimized = null;

	Stack<Number> constantStack = null;
	HashMap<Integer, Number> vars = null;

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

		// Do your optimization here
		Method[] methods = cgen.getMethods();
		for (Method m : methods)
		{
			optimizeMethod(cgen, cpgen, m);

		}

		this.optimized = gen.getJavaClass();
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


		// InstructionHandle is a wrapper for actual Instructions
		for (InstructionHandle handle : instList.getInstructionHandles())
		{
			// if the instruction inside is iconst
			if (handle.getInstruction() instanceof ICONST)
			{
				// insert new one with integer 5, and...
				instList.insert(handle, new ICONST(5));
				try
				{
					// delete the old one
					instList.delete(handle);

				}
				catch (TargetLostException e)
				{
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}

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