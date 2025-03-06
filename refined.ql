import cpp 
import semmle.code.cpp.controlflow.StackVariableReachability
import semmle.code.cpp.dataflow.new.DataFlow

// variable is not mentioned inside if
predicate notChildOfIf(Variable v, IfStmt i){
    not exists (VariableAccess a | a.getTarget()=v  and i.getEnclosingStmt().getAChild*()=a.getEnclosingStmt())
}

// if leads to goto on its true path
predicate ifToGoto(IfStmt i, GotoStmt g){
    g.hasName() and
    i.getThen().getAChild*()=g
}

// Return statement accesses v
predicate isProperReturn(Variable v, ReturnStmt ret){
    exists(VariableAccess a | a.getTarget() = v and not a.isModified() and a.getEnclosingStmt() = ret.getChildStmt*())
}

class InitToFaultyIfConfiguration extends StackVariableReachability {
    InitToFaultyIfConfiguration() { this = "InitToFaultyIfConfiguration" }

    override predicate isSource(ControlFlowNode node, StackVariable v) {
        // We are interested in all variable accesses
        // Note: Initializers are not VariableAccess!
        exists(VariableAccess ae | v = ae.getTarget() and ae.isModified() and ae = node) 
        
    }

    override predicate isSink(ControlFlowNode node, StackVariable v) {
        exists(ReturnStmt ret, GotoStmt goto, IfStmt i | node = i and // Source is an IfStmt
               i.getEnclosingFunction() = v.getAnAssignment().getEnclosingStmt().getEnclosingFunction() and // IfStmt and StackVariable are in the same function
               isProperReturn(v,ret) and // Return statement accesses v
               notChildOfIf(v, i) and // return variable not part of this if statement
               ifToGoto(i, goto) and // if leads to goto
               goto.getASuccessor+()=ret // goto leads to relevant return
        ) 
    }
    
    override predicate  isBarrier(ControlFlowNode node, StackVariable v) {
        exists(VariableAccess ae | v = ae.getTarget() and ae.isModified() and ae = node)  
    }
}

from ControlFlowNode sourceInit, ControlFlowNode sinkIf, InitToFaultyIfConfiguration confInitIf, LocalVariable v, ReturnStmt ret,
DataFlow::Node sinkRet, DataFlow::Node sourceDef
where confInitIf.reaches(sourceInit, v, sinkIf) and // A local variable reaches a faulty if in the CFG
  isProperReturn(v, ret) and // the variable is used as part of the return
  sourceDef.asExpr() = v.getAnAssignment() and // we are looking for data-flows from the return variable ...
  sinkRet.asExpr() = ret.getAChild() and // ... to the retrun statement
  DataFlow::localFlow(sourceDef, sinkRet) // we are only interested in value-preserving, local data-flows
select sourceInit, sinkIf, sinkIf.getLocation().getFile().getBaseName()+":"+sinkIf.getLocation().getStartLine()+":"+sinkIf.getLocation().getStartColumn()