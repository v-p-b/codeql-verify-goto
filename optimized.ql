import cpp
import semmle.code.cpp.dataflow.new.DataFlow
 

Stmt getRecChild(Stmt s) {
  result = s or
  result = getRecChild(s.getChildStmt())
}

Stmt getRecSuccessor(BasicBlock s) {
  result = s or
  result = getRecSuccessor(s.getASuccessor())
}


from DataFlow::Node sinkRet, DataFlow::Node sourceDef, ReturnStmt ret, LocalVariable v, LabelStmt gotoLabel, Function f, IfStmt i, Stmt goto, Assignment ass
where 
  // Function return type
  f.getType() instanceof IntType and
  // Variable return type matches Function return type
  v.getType() = f.getType() and
  // IfStmt is in Function
  i.getEnclosingFunction() = f and
  // v is in the same Function
  v.getFunction() = f and 
  // Only named nodes (e.g. no default returns)
  gotoLabel.isNamed() and
  v.getAnAssignment() = ass and
  // The return statement includes v
  exists(VariableAccess a | a.getTarget() = v and not a.isModified() and a.getEnclosingStmt() = getRecChild(ret)) and
  // return statement is in the labels basic block 
  getRecSuccessor(gotoLabel.getBasicBlock()) = ret.getBasicBlock() and
  i.getThen() = goto and // The if statement executes our goto statement or block
       ((goto instanceof GotoStmt and ((GotoStmt)goto).getName()=gotoLabel.getName()) or 
        (goto instanceof BlockStmt and ((BlockStmt)goto).getLastStmtIn() instanceof GotoStmt and 
         ((GotoStmt)(((BlockStmt)goto).getLastStmtIn())).getName() = gotoLabel.getName())) and // goto is either a single GOTO statement
                                                                                               // or a block that ends with GOTO 
                                                                                               // and goto label matches the return label
  // v is not accessed in i
  not exists(VariableAccess a | a.getEnclosingFunction() = f and a.getTarget() = v and 
                            a.getEnclosingStmt() = getRecChild(i)) and    
  // v is not modified in the basic block of the label
  // Note: This doesn't handle if v is is used as an output argument to a function
  not exists (VariableAccess a | a.getTarget() = v and a.isModified() and a.getEnclosingStmt().getBasicBlock() = getRecSuccessor(gotoLabel)) and
  // There is an untainted dataflow from a variable assignment to the return
  // Note: This will miss ternary assignments in return if returned expressions don't include v  (`return ret==8?0:1;`) 
  sourceDef.asExpr() = ass and
  sinkRet.asExpr() = ret.getAChild() and
  DataFlow::localFlow(sourceDef, sinkRet)
select i, 
     "Function: "+f+" - Label: "+gotoLabel.getName()+" - Variable: "+v+"- Assignment: "+ass.getLocation().getFile().getBaseName()+"("+ass.getLocation().getStartLine()+":"+ass.getLocation().getStartColumn()+")"
